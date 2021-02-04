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


(* ::Subsection:: *)
(*Manipulation of expressions*)


SpinorReplace::usage="SpinorReplace[exp,reps] applies the spinor replacements reps to the expression exp. The replacements need to be given in terms of the bare spinors SpinorUndotBare and SpinorDotBare, and can be any suitable linear combination of them. e replacements may also involve momentum matrices applied to the spinors, which are given for example as p.q.\[Lambda][p1]."
CompleteMandelstam::usage="CompleteMandelstam[exp] turns products of the type \[LeftAngleBracket]ij\[RightAngleBracket][ji] into the Mandelstam invariant S[i,j] for massless particles i,j."


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
(*Main Functions*)


(* ::Subsection::Closed:: *)
(*MasslessQ (private)*)


(*Test if a label belongs to MasslessMomenta*)
MasslessQ[x_]:=MemberQ[MasslessMomenta,x];


(* ::Subsection:: *)
(*SpinorReplace*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary functions*)


(*Recall that in order for dot to recognise all the linearities you need to apply MomReps to its argumenst first*)
dot[x___,y_+a_.*momlabel_String,z__]:=dot[x,y,z]+dot[x,a*momlabel,z];
dot[x___,a_*momlabel_String,z__]:=a*dot[x,momlabel,z];
dot[x__,y_+a_.*SpinorUndotBare[lab_][type_]]:=dot[x,y]+dot[x,a*SpinorUndotBare[lab][type]];
dot[x__,a_*SpinorUndotBare[lab_][type_]]:=a*dot[x,SpinorUndotBare[lab][type]];
dot[x__,y_+a_.*SpinorDotBare[lab_][type_]]:=dot[x,y]+dot[x,a*SpinorDotBare[lab][type]];
dot[x__,a_*SpinorDotBare[lab_][type_]]:=a*dot[x,SpinorDotBare[lab][type]];


(* ::Subsubsection::Closed:: *)
(*The replacement function*)


(*N.B. The matrix replacements are intended as defined on |\[Lambda]\[RightAngleBracket] and on |\[Lambda]], so when applying to \[LeftAngleBracket]\[Lambda]| and [\[Lambda]| minus signs appear when the number of matrices applied is odd*)


SpinorReplace::invalid="Some of the replacements assume an invalid form, please check input. Recall that an odd number of momentum matrices acting on a dotted spinor change it to undotted and viceversa.";
SpinorReplace[exp_,reps_]:=Catch[Block[{locexpSH,locrepsSH,agwrapper,sqwrapper,SpinorAngleBracket,SpinorSquareBracket,Chain,specialSH,list1SH,list2SH,auxlabsSH,repsSH},

(*We replace Dot with a local defined dot symbol, because Dot has some properties which screw up our pattern matching later on*)
locrepsSH={reps}/.Dot->dot//Flatten;

(*Since we want to use equalities instead of replacements for faster evaluation, we need to take into account situations like {\[Lambda][2]\[Rule]\[Lambda][3],\[Lambda][3]\[Rule]\[Lambda][4]}, so we introduce auxiliary labels to take care of that if needed.*)

list1SH=First/@locrepsSH;
list2SH=Last/@locrepsSH;

auxlabsSH=Select[list1SH,(!FreeQ[list2SH,#]&)];
repsSH=auxlabsSH/.{SpinorDotBare[x_][_]:>x,SpinorUndotBare[x_][_]:>x};
repsSH=(#->ToString[#]<>ToString[Unique[]]&)/@repsSH;
auxlabsSH=(#->(#/.repsSH)&)/@auxlabsSH;

list2SH=list2SH/.auxlabsSH//Expand[#,SpinorDotBare|SpinorUndotBare]&;

locrepsSH=Thread[list1SH->list2SH];

(*Introduces two wrappers with respect to which we will define the properties which perform the actual replacement*)
locrepsSH=locrepsSH/.{SpinorUndotBare[x_][$lam]:>agwrapper[x],SpinorDotBare[x_][$lam]:>sqwrapper[x],SpinorUndotBare[x_][$mu]:>agwrapper[obar[x]],SpinorDotBare[x_][$mu]:>sqwrapper[obar[x]]};

(*Isolate the replacements containing matrices which will get special treatment*)
specialSH=Select[locrepsSH,(!FreeQ[#,dot]&)];
locrepsSH=Select[locrepsSH,FreeQ[#,dot]&];


(*Test the correcteness of the replacements*)
If[AnyTrue[locrepsSH,((FreeQ[#,agwrapper]&&FreeQ[#,sqwrapper])||(!FreeQ[#,agwrapper]&&!FreeQ[#,sqwrapper])&)],
Message[SpinorReplace::invalid];
Throw[$Failed];
];

(*Now we transform replacement rules for the wrappers into equalities*)
locrepsSH=locrepsSH/.{Rule->Set,RuleDelayed->Set};

(*Define linearity of brackets and chains with respect to the wrappers*)
SpinorAngleBracket[a_+b_,c_]/;!FreeQ[b,agwrapper]:=SpinorAngleBracket[a,c]+SpinorAngleBracket[b,c];
SpinorAngleBracket[c_,a_+b_]/;!FreeQ[b,agwrapper]:=SpinorAngleBracket[c,a]+SpinorAngleBracket[c,b];

SpinorAngleBracket[a_*agwrapper[x_],y_]:=a*SpinorAngleBracket[agwrapper[x],y];
SpinorAngleBracket[y_,a_*agwrapper[x_]]:=a*SpinorAngleBracket[y,agwrapper[x]];

SpinorSquareBracket[a_+b_,c_]/;!FreeQ[b,sqwrapper]:=SpinorSquareBracket[a,c]+SpinorSquareBracket[b,c];
SpinorSquareBracket[c_,a_+b_]/;!FreeQ[b,sqwrapper]:=SpinorSquareBracket[c,a]+SpinorSquareBracket[c,b];

SpinorSquareBracket[a_*sqwrapper[x_],y_]:=a*SpinorSquareBracket[sqwrapper[x],y];
SpinorSquareBracket[y_,a_*sqwrapper[x_]]:=a*SpinorSquareBracket[y,sqwrapper[x]];

Chain[type1_,a_+b_,y_,z_,type2_]/;!FreeQ[b,agwrapper|sqwrapper]:=Chain[type1,a,y,z,type2]+Chain[type1,b,y,z,type2];
Chain[type1_,x_,y_,a_+b_,type2_]/;!FreeQ[b,agwrapper|sqwrapper]:=Chain[type1,x,y,a,type2]+Chain[type1,x,y,b,type2];

Chain[type1_,a_*agwrapper[x_],y_,z_,type2_]:=a*Chain[type1,agwrapper[x],y,z,type2];
Chain[type1_,a_*sqwrapper[x_],y_,z_,type2_]:=a*Chain[type1,sqwrapper[x],y,z,type2];
Chain[type1_,x_,y_,a_*agwrapper[z_],type2_]:=a*Chain[type1,x,y,agwrapper[z],type2];
Chain[type1_,x_,y_,a_*sqwrapper[z_],type2_]:=a*Chain[type1,x,y,sqwrapper[z],type2];

(*Now for the special replacements, if any*)
If[Length[specialSH]>0,

(*Take into account the matrix products. When a matrix is dotted into an angle wrapper it transforms it into a square and the opposite way around*)
specialSH=specialSH/.{dot[A__,agwrapper[x_]]:>If[OddQ[Length[{A}]],sqwrapper[{{A},x}],agwrapper[{{A},x}]],dot[A__,sqwrapper[x_]]:>If[OddQ[Length[{A}]],agwrapper[{{A},x}],sqwrapper[{{A},x}]]};
(*Test the correcteness of the replacements*)
If[AnyTrue[specialSH,((FreeQ[#,agwrapper]&&FreeQ[#,sqwrapper])||(!FreeQ[#,agwrapper]&&!FreeQ[#,sqwrapper])&)],
Message[SpinorReplace::invalid];
Throw[$Failed];
(*Throw["Some replacements are given in an unknown form. Please check input."];*)
];

(*Now we transform replacement rules for the wrappers into equalities*)
specialSH=specialSH/.{Rule->Set,RuleDelayed->Set};
(*And define the special properties of chains and brackets with respect to these wrappers*)
SpinorAngleBracket[x_,agwrapper[{A_List,y_}]]:=If[OddQ[Length[A]],
Chain[$angle,x,A,y,$square],
Chain[$angle,x,A,y,$angle]
];
SpinorAngleBracket[agwrapper[{A_,x_}],y_]:=If[OddQ[Length[A]],
-Chain[$square,x,Reverse[A],y,$angle],
Chain[$angle,x,Reverse[A],y,$angle]
];
SpinorSquareBracket[x_,sqwrapper[{A_,y_}]]:=If[OddQ[Length[A]],
Chain[$square,x,A,y,$angle],
Chain[$square,x,A,y,$square]
];
SpinorSquareBracket[sqwrapper[{A_,x_}],y_]:=If[OddQ[Length[A]],
-Chain[$angle,x,Reverse[A],y,$square],
Chain[$square,x,Reverse[A],y,$square]
];
Chain[type_,x_,{y__},agwrapper[{A_,z_}],$angle]:=If[OddQ[Length[A]],
Chain[type,x,{y,Sequence@@A},z,$square],
Chain[type,x,{y,Sequence@@A},z,$angle]
];
Chain[$angle,agwrapper[{A_,x_}],{y__},z_,type_]:=If[OddQ[Length[A]],
-Chain[$square,x,{Sequence@@Reverse[A],y},z,type],
Chain[$angle,x,{Sequence@@Reverse[A],y},z,type]
];
Chain[type_,x_,{y__},sqwrapper[{A_,z_}],$square]:=If[OddQ[Length[A]],
Chain[type,x,{y,Sequence@@A},z,$angle],
Chain[type,x,{y,Sequence@@A},z,$square]
];
Chain[$square,sqwrapper[{A_,x_}],{y__},z_,type_]:=If[OddQ[Length[A]],
-Chain[$angle,x,{Sequence@@Reverse[A],y},z,type],
Chain[$square,x,{Sequence@@Reverse[A],y},z,type]
];
];

(*Finally replace the arguments of SpinorAngleBracket, SpinorSquareBracket and Chain with the wrapped argumenst*)

locexpSH=exp/.{SpinorAngleBracket[x_,y_]:>SpinorAngleBracket[agwrapper[x],agwrapper[y]],SpinorSquareBracket[x_,y_]:>SpinorSquareBracket[sqwrapper[x],sqwrapper[y]],
Chain[$angle,x_,{y__},z_,$angle]:>Chain[$angle,agwrapper[x],{y},agwrapper[z],$angle],Chain[$square,x_,{y__},z_,$square]:>Chain[$square,sqwrapper[x],{y},sqwrapper[z],$square],Chain[$angle,x_,{y__},z_,$square]:>Chain[$angle,agwrapper[x],{y},sqwrapper[z],$square],Chain[$square,x_,{y__},z_,$angle]:>Chain[$square,sqwrapper[x],{y},agwrapper[z],$angle]};

(*Properties will be automatically applied so we can now just remove the wrappers and return the output.*)
locexpSH=locexpSH/.{agwrapper[x_]:>x,sqwrapper[x_]:>x};

(*Take into account that we might have made some label replacements, so replace those back.*)
locexpSH=locexpSH/.Reverse/@repsSH;

Throw[locexpSH];
];
];


(* ::Subsection:: *)
(*CompleteMandelstam*)


CompleteMandelstam[test_]:=Block[{SpinorAngleBracket,SpinorSquareBracket,Power},
(*Define a set of local properties for the angle and square brackets*)
(*positive powers*)
Power /: Times[Power[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],n_?Positive],Power[SpinorSquareBracket[x_,y_],m_?Positive]]:=If[n>=m,Times[Power[SpinorAngleBracket[x,y],n-m],Power[S[x,y],m]],Times[Power[SpinorSquareBracket[x,y],m-n],Power[S[x,y],n]]];
(*Negative powers*)
Power /: Times[Power[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],n_?Negative],Power[SpinorSquareBracket[x_,y_],m_?Negative]]:=If[n>=m,Times[Power[SpinorSquareBracket[x,y],m-n],Power[S[x,y],n]],Times[Power[SpinorAngleBracket[x,y],n-m],Power[S[x,y],m]]];
(*One Power and one plain*)
Power /: Times[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],Power[SpinorSquareBracket[x_,y_],m_]]:=Times[S[x,y],Power[SpinorSquareBracket[x,y],m-1]];
Power /: Times[SpinorSquareBracket[x_?MasslessQ,y_?MasslessQ],Power[SpinorAngleBracket[x_,y_],m_]]:=Times[S[x,y],Power[SpinorAngleBracket[x,y],m-1]];
(*Both plain*)
SpinorAngleBracket /: Times[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],SpinorSquareBracket[x_,y_]]:=S[x,y];
(*Return output*)
Return[test];
];


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
