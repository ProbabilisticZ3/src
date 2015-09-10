using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Irony.Parsing;
using Irony.Interpreter.Ast;

namespace PrismParser
{
    [Language("PRISM", "0.9", "PRISM files")]
    public class PrismGrammar : Grammar
    {
        public PrismGrammar()
            : base(caseSensitive: false)
        {
            // 1. Terminals

            //var pyNumber = TerminalFactory.CreatePythonNumber("number");
            //var pyIdentifier = TerminalFactory.CreatePythonIdentifier("identifier");

            //var prismString = new StringLiteral("string", "\"", StringOptions.AllowsDoubledQuote);
            //prismString.AddStartEnd("\"", StringOptions.NoEscapes);
            var quotedString = CreateQuotedIdentifier(this, "quotedId");

            var identifier = new IdentifierTerminal("Identifier", "_", "_");
            identifier.Options = IdOptions.IsNotKeyword;
            // var identifier = new StringLiteral("string", "\"");
            var number = new NumberLiteral("number");
            var A = new StringLiteral("string", "\"");
            var comment = new CommentTerminal("comment", "//", "\n", "\r");
            base.NonGrammarTerminals.Add(comment);
            var colon = ToTerm(":");
            var comma = ToTerm(",");
            var semicolon = ToTerm(";");
            // for commands:
            var plus = ToTerm("+");
            var arrow = ToTerm("->");

            // 2. Non-terminals
            var system = new NonTerminal("System", typeof(StatementListNode));
            var sysob = new NonTerminal("SystemLevelObject", typeof(AssignmentNode));
            var modeltype = new NonTerminal("ModelType", typeof(IdentifierNode));
            var globalConst = new NonTerminal("GlobalConstant", typeof(AssignmentNode));
            var globalVar = new NonTerminal("GlobalVariable", typeof(AssignmentNode));
            var module = new NonTerminal("Module", typeof(AssignmentNode));
            var moduleRenaming = new NonTerminal("ModuleRenaming", typeof(AssignmentNode));
            var eqnlist = new NonTerminal("EquantionList", typeof(StatementListNode));
            var identifierEqn = new NonTerminal("IdentifierEquation", typeof(AssignmentNode));
            var moduleBody = new NonTerminal("moduleBody");
            var moduleStmt = new NonTerminal("moduleStatement");
            var declaration = new NonTerminal("Declaration", typeof(AssignmentNode));
            var range = new NonTerminal("Range", typeof(AssignmentNode));
            var basictype = new NonTerminal("BasicType");
            var command = new NonTerminal("Command", typeof(AssignmentNode));
            var update = new NonTerminal("Update", typeof(AssignmentNode));
            var updateList = new NonTerminal("UpdateList", typeof(StatementListNode));
            var syncAction = new NonTerminal("SyncAction");
            var guard = new NonTerminal("Guard");
            var effect = new NonTerminal("Effect");
            var pchoice = new NonTerminal("ProbabilisticChoice", typeof(AssignmentNode));
            var pchoiceList = new NonTerminal("ProbabilisticChoiceList", typeof(StatementListNode));
            var rewards = new NonTerminal("Rewards", typeof(AssignmentNode));
            var rewardsList = new NonTerminal("RewardsList", typeof(StatementListNode));
            var rewardsBody = new NonTerminal("RewardsBody", typeof(AssignmentNode));

            var initBlock = new NonTerminal("InitBlock", typeof(AssignmentNode));

            //var prop = new NonTerminal("Property"); // not supported yet
            var label = new NonTerminal("Label", typeof(AssignmentNode));
            var formula = new NonTerminal("Formula", typeof(AssignmentNode));

            // 2.1 Non-terminals for expressions
            var expr = new NonTerminal("Expr");
            var term = new NonTerminal("Term");
            var binExpr = new NonTerminal("BinExpr", typeof(BinaryOperationNode));
            var iteExpr = new NonTerminal("TernaryExpr", typeof(IfNode));
            var parExpr = new NonTerminal("ParExpr");
            var unExpr = new NonTerminal("UnExpr", typeof(UnaryOperationNode));
            var unOp = new NonTerminal("UnOp", "operator");
            var binOp = new NonTerminal("BinOp", "operator");
            var paramList = new NonTerminal("ParamList", typeof(ParamListNode));
            var constant = new NonTerminal("Constant");
            var functionCall = new NonTerminal("FunctionCall", typeof(FunctionCallNode));
            var argList = new NonTerminal("ArgList", typeof(ExpressionListNode));
            // var AssignmentStmt = new NonTerminal("AssignmentStmt", typeof(AssignmentNode));

            //Rules
            system.Rule = MakePlusRule(system, sysob);
            sysob.Rule = modeltype | globalConst | globalVar | module | moduleRenaming | rewards | initBlock | label | formula; // | prop | label | formula;
            modeltype.Rule = ToTerm("mdp") | "ctmdp" | "ctmc" | "pta" | "stochastic" | "dtmc" | "probabilistic" | "nondeterministic";
            module.Rule = "module" + identifier + moduleBody + "endmodule";
            module.ErrorRule = SyntaxError + "endmodule";
            moduleBody.Rule = MakeStarRule(moduleBody, moduleStmt);
            moduleStmt.Rule = declaration | command;
            declaration.Rule = identifier + colon + (range | "bool") + (Empty | "init" + expr) + semicolon;
            range.Rule = "[" + expr + ".." + expr + "]";
            command.Rule = syncAction + guard + arrow + effect + semicolon;
            command.ErrorRule = SyntaxError + semicolon;
            syncAction.Rule = "[" + (Empty | identifier) + "]";
            guard.Rule = expr;
            effect.Rule = pchoiceList | updateList;
            pchoiceList.Rule = MakePlusRule(pchoiceList, plus, pchoice);
            pchoice.Rule = expr + colon + updateList;
            updateList.Rule = MakeStarRule(updateList, ToTerm("&"), update);
            update.Rule = ("(" + identifier + "'" + "=" + expr + ")") | "true"; //| ("(" + expr + ")");


            moduleRenaming.Rule = "module" + identifier + "=" + identifier + "[" + eqnlist + "]" + "endmodule";
            eqnlist.Rule = MakePlusRule(eqnlist, comma, identifierEqn);
            identifierEqn.Rule = identifier + "=" + identifier;

            globalConst.Rule = "const" + (Empty | basictype) + identifier + (Empty | ("=" + expr)) + semicolon;
            globalVar.Rule = "global" + declaration;

            basictype.Rule = ToTerm("int") | "double" | "bool" | "rate" | "prob";

            //rewards.Rule = ToTerm("rewards") + (Empty | "\"" + identifier + "\"") + rewardsList + "endrewards"; 
            rewards.Rule = "rewards" + (Empty | quotedString) + rewardsList + "endrewards";
            rewards.ErrorRule = SyntaxError + "endrewards";
            rewardsList.Rule = MakePlusRule(rewardsList, rewardsBody);
            rewardsBody.Rule = (Empty | syncAction) + expr + colon + expr + semicolon; // transition rewards and state rewards

            initBlock.Rule = "init" + expr + "endinit";
            label.Rule = "label" + quotedString + "=" + expr + semicolon;

            formula.Rule = "formula" + identifier + "=" + expr + semicolon;

            expr.Rule = term | unExpr | binExpr | iteExpr;
            term.Rule = constant | parExpr | identifier | functionCall;
            parExpr.Rule = "(" + expr + ")";
            unExpr.Rule = unOp + term;
            unOp.Rule = ToTerm("+") | "-" | "!";
            binExpr.Rule = expr + binOp + expr;
            binOp.Rule = ToTerm("+") | "-" | "*" | "/" | "<" | "<=" | ">=" | ">" | "=" | "!=" | "&" | "|" | "<=>" | "=>";
            iteExpr.Rule = expr + "?" + expr + colon + expr;
            constant.Rule = number | "true" | "false";
            functionCall.Rule = identifier + "(" + argList + ")";
            // functionCall.NodeCaptionTemplate = "call #{0}(...)";
            // [reply]  rec<mrec -> (rec'=min(rec+1,mrec));
            argList.Rule = MakeStarRule(argList, comma, expr);

            //Set grammar root
            this.Root = system;


            // 4. Token filters - created in a separate method CreateTokenFilters
            //    we need to add continuation symbol to NonGrammarTerminals because it is not used anywhere in grammar
            NonGrammarTerminals.Add(ToTerm(@"\"));

            // 5. Operators precedence        should implement operators as listed here: http://www.prismmodelchecker.org/manual/ThePRISMLanguage/Expressions
            RegisterOperators(1, Associativity.Right, "?");
            RegisterOperators(2, "=>");
            RegisterOperators(3, "<=>");
            RegisterOperators(4, "|");
            RegisterOperators(5, "&");
            RegisterOperators(6, "!");
            RegisterOperators(7, "=", "!=");
            RegisterOperators(8, "<", "<=", ">=", ">");
            RegisterOperators(9, "+", "-");
            RegisterOperators(10, "*", "/");


            // 6. Miscellaneous: punctuation, braces, transient nodes
            MarkPunctuation("(", ")", ":", ";");
            RegisterBracePair("(", ")");
            MarkTransient(term, expr, unOp, binOp, parExpr, constant, modeltype, moduleBody, basictype, guard, effect, moduleStmt);
            //MarkTransient(Term, Expr, Stmt, ExtStmt, UnOp, BinOp, ExtStmt, ParExpr, Block);



            // 7. Error recovery rule
            // included in the rules above

            // 8. Syntax error reporting
            AddToNoReportGroup("(");
            AddOperatorReportGroup("operator");

            // 9. Initialize console attributes
            ConsoleTitle = "Prism parser console";
            ConsoleGreeting =
      @"This is an Irony-generated Prism parser.

Press Ctrl-C to exit the program at any time.
";
            ConsolePrompt = ">>>";
            ConsolePromptMoreInput = "...";

            // 10. Language flags
            //this.LanguageFlags = LanguageFlags.NewLineBeforeEOF | LanguageFlags.CreateAst | LanguageFlags.SupportsBigInt;
            this.LanguageFlags = LanguageFlags.SupportsBigInt;

        }//constructor

        //public override void CreateTokenFilters(LanguageData language, TokenFilterList filters)
        //{
        //    var outlineFilter = new CodeOutlineFilter(language.GrammarData,
        //      OutlineOptions.ProduceIndents | OutlineOptions.CheckBraces, ToTerm(@"\")); // "\" is continuation symbol
        //    filters.Add(outlineFilter);
        //}

        //Covers simple identifiers like abcd, and also quoted versions: [abc d], "abc d".
        public static IdentifierTerminal CreateQuotedIdentifier(Grammar grammar, string name) // derived from SQL identifiers
        {
            var id = new IdentifierTerminal(name);
            StringLiteral term = new StringLiteral(name + "_quoted");
            term.AddStartEnd("\"", StringOptions.NoEscapes);
            term.SetOutputTerminal(grammar, id); //term will be added to NonGrammarTerminals automatically 
            return id;
        }
    }
}


