rem @echo off
rmdir /S /Q dist
mkdir dist\ProbabilisticZ3

xcopy /Q LICENSE.docx dist
xcopy /Q README.txt dist
xcopy /Q ProbabilisticZ3.sln dist

for %%I in (ProbabilisticZ3) DO (
    mkdir dist\%%I
    xcopy /Q %%I\*.fs dist\%%I\
    xcopy /Q %%I\*.fsproj dist\%%I\
    xcopy /Q %%I\*.config dist\%%I\
	xcopy /Q %%I\Properties\*.* dist\%%I\Properties\
)

for %%I in (PrismParser) DO (
    mkdir dist\%%I
    xcopy /Q %%I\*.cs dist\%%I\
    xcopy /Q %%I\*.csproj dist\%%I\
    xcopy /Q %%I\*.config dist\%%I\
	xcopy /Q %%I\Properties\*.* dist\%%I\Properties\
)