(* ::Package:: *)

(* ::Chapter:: *)
(*SpinorHelicity4D*)


BeginPackage["SpinorHelicity4D`",{"SpinorBuildingBlocks`"}]


(*In order to allow the package to be reloaded we unprotect and clear all the symbol definitions*)
Unprotect@@Names["SpinorHelicity4D`*"];
ClearAll@@Names["SpinorHelicity4D`*"];


(* ::Section:: *)
(*Function description*)


(* ::Subsection:: *)
(*Custom functions and palette*)


AssignNames::usage="AssignNames allows to assign custom names to functions of the package. These definitions become permanent, but can be undone through ClearNames. If called without arguments, AssignNames[] displays a list of the custom function definitions. For further informations see package documentation."
ClearNames::usage="ClearNames clears the customized definitions of functions given through AssignNames. If called without arguments, ClearNames[] clears all the defined functions. For further information see the package documentation."
SpinorPalette::usage="SpinorPalette[] opens the input palette."


(* ::Section:: *)
(*Private context starts here*)


Begin["`Private`"]


(*We define a private variable needed for the package to decide whether to run shortcuts and the palette or not. This is related to the availability of a frontend.*)


frontend=If[TrueQ[$FrontEnd==Null],0,1];


(*Define a local MomReps which we will need multiple times to be the same as the one in SpinorBuildingBlocks*)
(*MomReps:=SpinorBuildingBlocks`Private`MomReps;*)


(* ::Section:: *)
(*Custom functions and palette*)


(* ::Subsection::Closed:: *)
(*AssignNames*)


SetAttributes[AssignNames,HoldAllComplete];

AssignNames[names__]:=Module[{path,filename,rd,defs,wr,tofile,redundant,myset,mysetdelayed,defsclear},

(*First of all we clear all definitions. To do so we need to apply special treatment for Set and SetDelayed since these do not allow fo a straight pattern matching as Rule and RuleDelayed do*)

tofile=Hold[{names}]/.{Set->myset,SetDelayed->mysetdelayed};
tofile=tofile/.{Rule[g_[__],_]:>ClearAll[g],RuleDelayed[g_[__],_]:>ClearAll[g],mysetdelayed[g_[__],_]:>ClearAll[g],myset[x_,y_]:>ClearAll[x]};
tofile=tofile/.{mysetdelayed[x_,y_]:>ClearAll[x],RuleDelayed[x_,y_]:>ClearAll[x],Rule[x_,y_]:>Clear[x]};
ReleaseHold[tofile];

(*Now we convert everything into a list of replacements which is safe to handle*)
tofile=Hold[{names}]/.{Set->Rule,SetDelayed->RuleDelayed};
tofile=tofile//ReleaseHold;

(*Find the package*)
path=FindFile["SpinorHelicity4D`"];
(*Extract the position without the package name*)
path=FileNameTake[path,{1,FileNameDepth[path]-1}];
(*Define the name of the file containing the definitions*)
filename=FileNameJoin[{path,"SpinorHelicityCustomFunctions.wl"}];

(*Check if a file that contains definitions already exists. If it does, open it and load its content, which will be a list of replacements*)
If[FileExistsQ[filename],
(*Load the content of the file*)
rd=OpenRead[filename];
defs=Read[rd];
Close[filename];
(*Check if there are any redundant definitions to be replaced. To do so we need also here to clear all the definitions*)
defsclear=defs/.{Rule[g_[__],_]:>ClearAll[g],RuleDelayed[g_[__],_]:>ClearAll[g]};
defsclear=defsclear/.{RuleDelayed[x_,y_]:>Clear[x],Rule[x_,y_]:>Clear[x]};
ReleaseHold[defsclear];
(*Extract all the function names from tofile*)
redundant=tofile/.{Rule[g_[__],_]:>g,RuleDelayed[g_[__],_]:>g};
redundant=redundant/.{RuleDelayed[x_,y_]:>x,Rule[x_,y_]:>x};
redundant=Flatten[redundant];
defs=DeleteCases[defs//ReleaseHold,x_/;AnyTrue[redundant,(!FreeQ[x[[1]],#]&)]];
tofile=Join[defs,tofile//Flatten];
];

(*Open a stream to write to the file*)
wr=OpenWrite[filename];
(*Write to the file*)
Write[wr,Hold/@tofile];
(*Close the stream*)
Close[filename];

(*Convert rules to Set and SetDelayed so that the functions are evaluated and usable*)
tofile/.{RuleDelayed[x_,y_]/;FreeQ[x,Pattern]:>Set[x,y],RuleDelayed[x_,y_]/;!FreeQ[x,Pattern]:>SetDelayed[x,y],Rule[x_,y_]/;FreeQ[x,Pattern]:>Set[x,y],Rule[x_,y_]/;!FreeQ[x,Pattern]:>SetDelayed[x,y]};

];


(*Display all the custom functions*)

AssignNames[]:=Module[{path,filename,rd,defs},

(*Find the package*)
path=FindFile["SpinorHelicity4D`"];
(*Extract the position without the package name*)
path=FileNameTake[path,{1,FileNameDepth[path]-1}];
(*Define the name of the file containing the definitions*)
filename=FileNameJoin[{path,"SpinorHelicityCustomFunctions.wl"}];

(*Check if a file that contains definitions already exists. If it does, open it and save its content, which will be a list of holded replacements*)
If[FileExistsQ[filename],
(*Load the content of the file*)
rd=OpenRead[filename];
defs=Read[rd];
Close[filename];
,
defs="No available definitions.";
];

Return[defs];

];


(* ::Subsection::Closed:: *)
(*ClearNames*)


SetAttributes[ClearNames,HoldAllComplete];

ClearNames[names__]:=Module[{path,filename,rd,defs,wr,tofile,redundant,myset,mysetdelayed,defsclear},

(*Find the package*)
path=FindFile["SpinorHelicity4D`"];
(*Extract the position without the package name*)
path=FileNameTake[path,{1,FileNameDepth[path]-1}];
(*Define the name of the file containing the definitions*)
filename=FileNameJoin[{path,"SpinorHelicityCustomFunctions.wl"}];

(*Check if a file that contains definitions already exists. If it does, open it and load its content, which will be a list of replacements*)
If[FileExistsQ[filename],
(*Clear definitions of the functions*)
tofile=Hold[{names}]/.List->ClearAll;
ReleaseHold[tofile];
tofile={names};

(*Now proceed to removing them from the file. Load the content of the file*)
rd=OpenRead[filename];
defs=Read[rd];
Close[filename];

(*Clear definitions of all the stored functions*)
defsclear=defs/.{Rule[g_[__],_]:>ClearAll[g],RuleDelayed[g_[__],_]:>ClearAll[g]};
defsclear=defsclear/.{RuleDelayed[x_,y_]:>Clear[x],Rule[x_,y_]:>Clear[x]};
ReleaseHold[defsclear];
defs=DeleteCases[defs//ReleaseHold,x_/;AnyTrue[tofile,(!FreeQ[x[[1]],#]&)]];
tofile=defs;
,
Return["No file from which to remove the definitions has been found."];
];

(*Open a stream to write to the file*)
wr=OpenWrite[filename];
(*Write to the file*)
Write[wr,Hold/@tofile];
(*Close the stream*)
Close[filename];

(*Convert rules to Set and SetDelayed so that the functions are evaluated and usable*)
tofile/.{RuleDelayed[x_,y_]/;FreeQ[x,Pattern]:>Set[x,y],RuleDelayed[x_,y_]/;!FreeQ[x,Pattern]:>SetDelayed[x,y],Rule[x_,y_]/;FreeQ[x,Pattern]:>Set[x,y],Rule[x_,y_]/;!FreeQ[x,Pattern]:>SetDelayed[x,y]};

];


(*Clear all the definitions in the file and delete the file itself.*)

ClearNames[]:=Module[{path,filename,rd,defs,defsclear},

(*Find the package*)
path=FindFile["SpinorHelicity4D`"];
(*Extract the position without the package name*)
path=FileNameTake[path,{1,FileNameDepth[path]-1}];
(*Define the name of the file containing the definitions*)
filename=FileNameJoin[{path,"SpinorHelicityCustomFunctions.wl"}];

If[FileExistsQ[filename],
(*Load the content of the file*)
rd=OpenRead[filename];
defs=Read[rd];
Close[filename];

(*Clear definitions of all the stored functions*)
defsclear=defs/.{Rule[g_[__],_]:>ClearAll[g],RuleDelayed[g_[__],_]:>ClearAll[g]};
defsclear=defsclear/.{RuleDelayed[x_,y_]:>Clear[x],Rule[x_,y_]:>Clear[x]};
ReleaseHold[defsclear];
(*Then delete the file*)
DeleteFile[filename],
Return["No file has been found."];
];
];


(* ::Subsection::Closed:: *)
(*File loader*)


(*(*Define the function to load the existing file with the custom-functions' definitions, if any.*)

(*In order not to define unwanted global parameters we keep this inside the local context but we have to call outside of it in order to properly load the functions.*)

LoadFunctions[]:=Module[{path,filename,rd,defs},

(*Find the package*)
path=FindFile["SpinorHelicity4D`"];
(*Extract the position without the package name*)
path=FileNameTake[path,{1,FileNameDepth[path]-1}];
(*Define the name of the file containing the definitions*)
filename=FileNameJoin[{path,"SpinorHelicityCustomFunctions.wl"}];

(*Check if a file that contains definitions already exists. If it does, open it and save its content, which will be a list of holded replacements*)
If[FileExistsQ[filename],
(*Load the content of the file*)
rd=OpenRead[filename];
defs=Read[rd];
Close[filename];
defs=defs/.{Rule\[Rule]Set,RuleDelayed\[Rule]SetDelayed};
ReleaseHold[defs];
];

];*)


(* ::Subsection:: *)
(*Palette*)


SpinorPalette[]:=CreatePalette[DynamicModule[{opener1=True,opener2=False},Column[{OpenerView[{"Spinors",Grid[Join[Partition[PasteButton[RawBoxes[#]]&/@{SpinorBuildingBlocks`Private`SpinorLaUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLaDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLatUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLatDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorUndotBareLBox["\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorDotBareLBox["\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`LevicivitaSHBoxUp["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`LevicivitaSHBoxDown["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`AngleSquareChainBox["\[SelectionPlaceholder]","{\[SelectionPlaceholder]}","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SquareAngleChainBox["\[SelectionPlaceholder]","{\[SelectionPlaceholder]}","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`AngleAngleChainBox["\[SelectionPlaceholder]","{\[SelectionPlaceholder]}","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SquareSquareChainBox["\[SelectionPlaceholder]","{\[SelectionPlaceholder]}","\[SelectionPlaceholder]"]},4],{{PasteButton[RawBoxes[SpinorBuildingBlocks`Private`SpinorAngleBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]],SpanFromLeft,PasteButton[RawBoxes[SpinorBuildingBlocks`Private`SpinorSquareBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]],SpanFromLeft}}],Spacings->{2,0.6}]},Dynamic[opener1,(opener1=#;opener2=opener2)&]],OpenerView[{"Vectors",Grid[{1,2,3,4},Spacings->Automatic]},Dynamic[opener2,(opener2=#;opener1=opener1)&]]}]],WindowTitle->"SpinorHelicity4DInput",Saveable->False];


(* ::Section:: *)
(*End of context*)


(*Open palette*)
If[frontend==1,
CreatePalette[DynamicModule[{opener1=True,opener2=False},Column[{OpenerView[{"Spinors",Grid[Join[Partition[PasteButton[RawBoxes[#]]&/@{SpinorBuildingBlocks`Private`SpinorLaUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLaDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLatUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLatDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorUndotBareLBox["\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorDotBareLBox["\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`LevicivitaSHBoxUp["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`LevicivitaSHBoxDown["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`AngleSquareChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SquareAngleChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`AngleAngleChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SquareSquareChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"]},4],{{PasteButton[RawBoxes[SpinorBuildingBlocks`Private`SpinorAngleBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]],SpanFromLeft,PasteButton[RawBoxes[SpinorBuildingBlocks`Private`SpinorSquareBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]],SpanFromLeft}}],Spacings->{2,0.6}]},Dynamic[opener1,(opener1=#;opener2=opener2)&]],OpenerView[{"Vectors",Grid[{1,2,3,4},Spacings->Automatic]},Dynamic[opener2,(opener2=#;opener1=opener1)&]]}]],WindowTitle->"SpinorHelicity4DInput",Saveable->False];
];


Print["===============SpinorHelicity4D================"];
Print["Author: Manuel Accettulli Huber (QMUL)"];
Print["Please report any bug to:"];
Print["m.accettullihuber@qmul.ac.uk"];
Print["Version 1.0 , last update 03/08/2020"];
Print[Hyperlink["Click here for full documentation","https://github.com/accettullihuber"]];
Print["============================================="];


(*End the private context*)
End[]

(*Protect all public symbols in the package*)
Protect@@Names["SpinorHelicity4D`*"];

(*End the package*)
EndPackage[]


(* ::Section:: *)
(*Load custom function definitions if any*)


(*Now that we are in the global context, load the file with user-defined definitions*)

Module[{path,filename,rd,defs},

(*Find the package*)
path=FindFile["SpinorHelicity4D`"];
(*Extract the position without the package name*)
path=FileNameTake[path,{1,FileNameDepth[path]-1}];
(*Define the name of the file containing the definitions*)
filename=FileNameJoin[{path,"SpinorHelicityCustomFunctions.wl"}];

(*Check if a file that contains definitions already exists. If it does, open it and save its content, which will be a list of holded replacements*)
If[FileExistsQ[filename],
(*Load the content of the file*)
(<<SpinorHelicityCustomFunctions`)/.{Rule->Set,RuleDelayed->SetDelayed}//ReleaseHold;

];

];
