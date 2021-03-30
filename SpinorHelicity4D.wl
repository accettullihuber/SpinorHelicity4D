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
ToChain::usage="ToChain[exp] closes spinors of the |p\[RightAngleBracket][p| into momenta building chains of spinor products. So for example \[LeftAngleBracket]1 2\[RightAngleBracket][2 3] becomes \[LeftAngleBracket]1 2 3]. ToChain allows for the option ChainSelection."
ChainSelection::usage="ChainSelection is an option for ToChain specifying which contraction to pick when multiple chains could be built out of the same brackets. Allowed values (given as strings) are ShortestChain, LongestChain ans MostTraces. For further information see the documentation."
ChainToSpinor::usage="ChainToSpinor[exp] transforms chain objects in exp into products of spinor brackets."
ChainSimplify::usage="ChainSimplify[exp,Options] uses properties of the chains to simplify them, reducing them to chains where a given momentum appears at most once and scalar products. It allows for the options MomCon and ReduceComplete. Notice that in order for the simplifications to work best the momenta should be first declared through DeclareMom and massless momenta should be specified by DeclareMassless."
MomCon::usage="MomCon is an option for ChainSimplify which allows to use momentum conservation to simplify the chains. It must be defined as a list of replacements."
ReduceComplete::usage="ReduceComplete is an option for ChainSimplify which assumes boolean values, default is False. If set to True the function will order the momenta inside the chains, removing in this way spurious structures which could be obtained from each other by reordering. Be aware that this might not actually reduce the number of terms in the expression because of the reordering procedure."


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


(*Test if a label belongs to MasslessMomenta.*)
MasslessQ[x_]:=MemberQ[SpinorBuildingBlocks`Private`MasslessMomentaAll,x];


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


(* ::Subsection::Closed:: *)
(*CompleteMandelstam*)


CompleteMandelstam[test_]:=Block[{SpinorAngleBracket,SpinorSquareBracket,Power},
(*Define a set of local properties for the angle and square brackets*)
(*positive powers*)
Power /: Times[Power[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],n_?Positive],Power[SpinorSquareBracket[x_,y_],m_?Positive]]:=If[n>=m,Times[Power[SpinorAngleBracket[x,y],n-m],Power[-S[x,y],m]],Times[Power[SpinorSquareBracket[x,y],m-n],Power[-S[x,y],n]]];
(*Negative powers*)
Power /: Times[Power[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],n_?Negative],Power[SpinorSquareBracket[x_,y_],m_?Negative]]:=If[n>=m,Times[Power[SpinorSquareBracket[x,y],m-n],Power[-S[x,y],n]],Times[Power[SpinorAngleBracket[x,y],n-m],Power[-S[x,y],m]]];
(*One Power and one plain*)
Power /: Times[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],Power[SpinorSquareBracket[x_,y_],m_]]:=Times[-S[x,y],Power[SpinorSquareBracket[x,y],m-1]];
Power /: Times[SpinorSquareBracket[x_?MasslessQ,y_?MasslessQ],Power[SpinorAngleBracket[x_,y_],m_]]:=Times[-S[x,y],Power[SpinorAngleBracket[x,y],m-1]];
(*Both plain*)
SpinorAngleBracket /: Times[SpinorAngleBracket[x_?MasslessQ,y_?MasslessQ],SpinorSquareBracket[x_,y_]]:=-S[x,y];
(*Return output*)
Return[test];
];


(* ::Subsection:: *)
(*ToChain*)


(* ::Subsubsection::Closed:: *)
(*toChainOld, fastest version but random chains*)


(*Old version of ToChain. The resulting chain might not be minimal or of the best possible form but it is still a perfectly viable chain. We keep this as the fastest version.*)

Options[toChainOld]={MinimalChains->True};
toChainOld[exp_,OptionsPattern[]]:=Module[{locexp},

Block[{ChainPow,SpinorAngleBracket,SpinorSquareBracket,Chain},

(*ChainPow properties:*)

(*Basics*)
ChainPow[x__][0]:=1;

(*SquareAngle as AngleSquare*)
ChainPow[$square,x_,{y__},z_,$angle][n_]:=ChainPow[$angle,z,Reverse[{y}],x,$square][n];

(*The actual contraction properties*)

(* (x...y\[RightAngleBracket][y...z) *)
ChainPow /: Times[ChainPow[type1_,x_,{k___},y_,$angle][n_?Positive],ChainPow[$square,y_,{q___},z_,type2_][m_?Positive]]:=If[n>=m,ChainPow[type1,x,{k,y,q},z,type2][m]ChainPow[type1,x,{k},y,$angle][n-m],
ChainPow[type1,x,{k,y,q},z,type2][n]ChainPow[$square,y,{q},z,type2][m-n]
];

ChainPow /: Times[ChainPow[type1_,x_,{k___},y_,$angle][n_?Negative],ChainPow[$square,y_,{q___},z_,type2_][m_?Negative]]:=If[n<=m,ChainPow[type1,x,{k,y,q},z,type2][m]ChainPow[type1,x,{k},y,$angle][n-m],
ChainPow[type1,x,{k,y,q},z,type2][n]ChainPow[$square,y,{q},z,type2][m-n]
];

(*\[LeftAngleBracket]y...x)[y...z) *)
ChainPow /: Times[ChainPow[$angle,y_,{k___},x_,type1_][n_?Positive],ChainPow[$square,y_,{q___},z_,type2_][m_?Positive]]:=If[n>=m,
(-1)^(m*(Length[{k}]+1))*ChainPow[type1,x,{Sequence@@Reverse[{k}],y,q},z,type2][m]ChainPow[$angle,y,{k},x,type1][n-m],
(-1)^(n*(Length[{k}]+1))*ChainPow[type1,x,{Sequence@@Reverse[{k}],y,q},z,type2][n]ChainPow[$square,y,{q},z,type2][m-n]
];

ChainPow /: Times[ChainPow[$angle,y_,{k___},x_,type1_][n_?Negative],ChainPow[$square,y_,{q___},z_,type2_][m_?Negative]]:=If[n<=m,
(-1)^(m*(Length[{k}]+1))*ChainPow[type1,x,{Sequence@@Reverse[{k}],y,q},z,type2][m]ChainPow[$angle,y,{k},x,type1][n-m],
(-1)^(n*(Length[{k}]+1))*ChainPow[type1,x,{Sequence@@Reverse[{k}],y,q},z,type2][n]ChainPow[$square,y,{q},z,type2][m-n]
];

(*(x...y\[RightAngleBracket][y...z)*)
ChainPow /: Times[ChainPow[type1_,x_,{k___},y_,$angle][n_?Positive],ChainPow[type2_,z_,{q___},y_,$square][m_?Positive]]:=If[n>=m,
(-1)^(m*(Length[{q}]+1))*ChainPow[type1,x,{k,y,Sequence@@Reverse[{q}]},z,type2][m]ChainPow[type1,x,{k},y,$angle][n-m],
(-1)^(n*(Length[{q}]+1))*ChainPow[type1,x,{k,y,Sequence@@Reverse[{q}]},z,type2][n]ChainPow[type2,z,{q},y,$square][m-n]
];

ChainPow /: Times[ChainPow[type1_,x_,{k___},y_,$angle][n_?Negative],ChainPow[type2_,z_,{q___},y_,$square][m_?Negative]]:=If[n<=m,
(-1)^(m*(Length[{q}]+1))*ChainPow[type1,x,{k,y,Sequence@@Reverse[{q}]},z,type2][m]ChainPow[type1,x,{k},y,$angle][n-m],
(-1)^(n*(Length[{q}]+1))*ChainPow[type1,x,{k,y,Sequence@@Reverse[{q}]},z,type2][n]ChainPow[type2,z,{q},y,$square][m-n]
];

(* \[LeftAngleBracket]y...x)(z...y] *)
ChainPow /: Times[ChainPow[$angle,y_,{k___},x_,type1_][n_?Positive],ChainPow[type2_,z_,{q___},y_,$square][m_?Positive]]:=If[n>=m,
ChainPow[type2,z,{q,y,k},x,type1][m]ChainPow[$angle,y,{k},x,type1][n-m],
ChainPow[type2,z,{q,y,k},x,type1][n]ChainPow[type2,z,{q},y,$square][m-n]
];

ChainPow /: Times[ChainPow[$angle,y_,{k___},x_,type1_][n_?Negative],ChainPow[type2_,z_,{q___},y_,$square][m_?Negative]]:=If[n<=m,
ChainPow[type2,z,{q,y,k},x,type1][m]ChainPow[$angle,y,{k},x,type1][n-m],
ChainPow[type2,z,{q,y,k},x,type1][n]ChainPow[type2,z,{q},y,$square][m-n]
];

(*Applying the properties to the expression*)
(*Convert angle and square brackets to Chains and Chains to ChainPow*)
SpinorAngleBracket[x_,y_]:=Chain[$angle,x,{},y,$angle];
SpinorSquareBracket[x_,y_]:=Chain[$square,x,{},y,$square];
ChainPow /: Power[ChainPow[x__][p_],n_]:=ChainPow[x][p*n];
Chain[x__]:=ChainPow[x][1];

locexp=exp;

(*Expand part of the expression containing ChainPow in order for the contractions to happen*)
locexp=Expand[locexp,ChainPow];
];

Block[{ChainPow,Chain},

(*Convert back to angle and square brackets*)
Chain[$angle,x_,{},y_,$angle]:=SpinorAngleBracket[x,y];
Chain[$square,x_,{},y_,$square]:=SpinorSquareBracket[x,y];
ChainPow[x__][n_]:=Power[Chain[x],n];
locexp=locexp;
];

(*Reduce the chains to minimal form if required*)

If[TrueQ[OptionValue[MinimalChains]],
Block[{Chain},
(*Splitting chains into smaller chains*)
Chain[$angle,x_,{y___,x_,z___},k_,type2_]/;OddQ[Length[{y}]]:=Chain[$angle,x,{y},x,$square]*Chain[$angle,x,{z},k,type2];
	Chain[$square,x_,{y___,x_,z___},k_,type2_]/;OddQ[Length[{y}]]:=Chain[$square,x,{y},x,$angle]*Chain[$square,x,{z},k,type2];
	Chain[type1_,k_,{y___,x_,z___},x_,$angle]/;OddQ[Length[{z}]]:=Chain[type1,k,{y},x,$angle]*Chain[$square,x,{z},x,$angle];
	Chain[type1_,k_,{y___,x_,z___},x_,$square]/;OddQ[Length[{z}]]:=Chain[type1,k,{y},x,$square]*Chain[$angle,x,{z},x,$square];

(*Converting emty chains into brackets*)
Chain[$angle,x_,{},y_,$angle]:=SpinorAngleBracket[x,y];
Chain[$square,x_,{},y_,$square]:=SpinorAngleBracket[x,y];

locexp=locexp;
];

];

Return[locexp];
];


(* ::Subsubsection::Closed:: *)
(*Auxiliary for toChainNew*)


(*This is the new version of ToChain which allows to select *)


(*Auxiliary function to test for duplicates in a list, returns False if there are no duplicates*)

duplicatesQ = 0 ===Signature@#&;

(*Auxiliary function for testing if a contraction is possible, i.e. if every bracket appears at most once*)

feasibilitytest =Or@@ duplicatesQ/@Transpose@(First/@Transpose/@#)&;


(*Ordering function for the lists of contractions, to bring them in sequntial order ready to be chained*)
(*We assume everything to be already paired up by contracted angle brackets. Further connect by contracted angles*)

chorder /: List[x1___,chorder[{{i1_,j1_},{i2_,j2_}},y1___],x2___,chorder[{{i1_,j3_},{i4_,j4_}},y2___],x3___]:=List[x1,x2,x3,chorder[Sequence@@Reverse[{y2}],{{i1,j3},{i4,j4}},{{i1,j1},{i2,j2}},y1]];
chorder /: List[x1___,chorder[y1___,{{i1_,j1_},{i2_,j2_}}],x2___,chorder[{{i1_,j3_},{i4_,j4_}},y2___],x3___]:=List[x1,x2,x3,chorder[y1,{{i1,j1},{i2,j2}},{{i1,j3},{i4,j4}},y2]];
chorder /: List[x1___,chorder[{{i1_,j3_},{i4_,j4_}},y2___],x2___,chorder[y1___,{{i1_,j1_},{i2_,j2_}}],x3___]:=List[x1,x2,x3,chorder[y1,{{i1,j1},{i2,j2}},{{i1,j3},{i4,j4}},y2]];
chorder /: List[x1___,chorder[y1___,{{i1_,j1_},{i2_,j2_}}],x2___,chorder[y2___,{{i1_,j3_},{i4_,j4_}}],x3___]:=List[x1,x2,x3,chorder[y1,{{i1,j1},{i2,j2}},{{i1,j3},{i4,j4}},Sequence@@Reverse[{y2}]]];


(*This function converts lists of brackets into a chain. Needs to be embedded in previous code*)

(*We assume traces have been converted from even to odd number of contractions*)

(*Single chain. I think/hope that the use of a Length test intesad of a direct pattern matching increses speed, this is the reason why introduced an auxiliary function*)
ChainBuilder[exp_List,ag_List,sq_List]/;Length@exp===1:=auxChainBuilder[exp,ag,sq]
auxChainBuilder[{{{i1_,1},{i2_,1}}},ag_,sq_]:=-Chain[$angle,Last@ag[[i1]],{First@ag[[i1]]},Last@sq[[i2]],$square];
auxChainBuilder[{{{i1_,1},{i2_,2}}},ag_,sq_]:=Chain[$angle,Last@ag[[i1]],{First@ag[[i1]]},First@sq[[i2]],$square];
auxChainBuilder[{{{i1_,2},{i2_,1}}},ag_,sq_]:=Chain[$angle,First@ag[[i1]],{Last@ag[[i1]]},Last@sq[[i2]],$square];
auxChainBuilder[{{{i1_,2},{i2_,2}}},ag_,sq_]:=-Chain[$angle,First@ag[[i1]],{Last@ag[[i1]]},First@sq[[i2]],$square];

(*Even angle chains*)
ChainBuilder[exp_List,ag_List,sq_List]/;EvenQ@Length@exp&&exp[[1,2,1]]===exp[[2,2,1]]:=(-1)^Count[Last/@Total/@exp,2|4,2]*(Chain[$angle,First@#,Rest@Most@#,Last@#,$angle]&@Flatten@({If[Last@#==1,Reverse@First@#,First@#]&@First@#,If[Last@#==2,Reverse@First@#,First@#]&/@Rest@#}&@Transpose@({Part[List@@@ag,#]&/@#1,#2}&@@Transpose@(First/@If[Length@exp>2,Drop[exp,{3,Length[exp],2}],exp]))));

(*Even square chains*)
ChainBuilder[exp_List,ag_List,sq_List]/;EvenQ@Length@exp&&exp[[1,2,1]]!=exp[[2,2,1]]:=(-1)^Count[Last/@Total/@exp,2|4,2]*(Chain[$square,First@#,Rest@Most@#,Last@#,$square]&@Flatten@({If[Last@#==1,Reverse@First@#,First@#]&@First@#,If[Last@#==2,Reverse@First@#,First@#]&/@Rest@#}&@Transpose@({Part[List@@@sq,#]&/@#1,#2}&@@Transpose@(Last/@If[Length@exp>2,Drop[exp,{3,Length[exp],2}],exp]))));

(*Odd length chains. Just like in the even case with an addition of a final bracket*)
ChainBuilder[exp_List,ag_List,sq_List]/;OddQ@Length@exp:=(-1)^Count[Last/@Total/@exp,2|4,2]*(Chain[$angle,First@#,Rest@#,If[Last@#==1,sq[[First@#,2]],sq[[First@#,1]]]&@Last@Last@exp,$square]&@Flatten@({If[Last@#==1,Reverse@First@#,First@#]&@First@#,If[Last@#==2,Reverse@First@#,First@#]&/@Rest@#}&@Transpose@({Part[List@@@ag,#]&/@#1,#2}&@@Transpose@(First/@If[Length@#>2,Drop[#,{3,Length[#],2}],#]&@Most@exp))));


(*Function which given a list of brackets finda all possible chains that can built out of them, returns a list of possible chains and free uncontracted brackets*)
AllChains[exp_List]:=Module[{ag,sq,ch,connections,momenta,candidatecontractions,chains,pp,unique,sign,localbrackets,labs,removed},

(*Gather by angle and square head, chains are converted into angles and squares and in case mixed chains are found an appropriate connection is added. We take care of chains later on*)

(*Angle and square chains are no problem, the only troublesome are the mixed chains, these are kept separate*)
Block[{Chain},
Chain[$angle,x_,y_,z_,$angle]:=SpinorAngleBracket[x,y,z];
Chain[$square,x_,y_,z_,$square]:=SpinorSquareBracket[x,y,z];
{ag,sq,ch}=Flatten[#,1]&/@{Select[#,(Head@First@#===SpinorAngleBracket&)],Select[#,(Head@First@#===SpinorSquareBracket&)],Select[#,(Head@First@#===Chain&)]}&@GatherBy[exp,Head];
];

(*In order to take care of mixed chains in a simple way we decompose them into an angle and square bracket and add a fixed connection to the list of connections, the rest follows automatically*)
sign=1;
Do[
(*Decomposition into angle and square is done by introducing a unique label fro each chain, so that later on when contractions are performed there will be exactly for each of these.*)
ag=Join[ag,{SpinorAngleBracket[i[[2]],Most@i[[3]],unique=pp[Last@i[[3]],Unique[]]]}];
If[OrderedQ[{unique,i[[4]]}],
sq=Join[sq,{SpinorSquareBracket[unique,i[[4]]]}];
,
(*Sign keeps track of signs since the arguments of the brackets need to be correctly ordered (this was an initial assumption on the input list so it must be mantained)*)
sign=-1*sign;
sq=Join[sq,{SpinorSquareBracket[i[[4]],unique]}];
];
,{i,ch}];

(*Remove some redundancy by removing unnecessary powers*)
Block[{SpinorAngleBracket,SpinorSquareBracket},
SpinorSquareBracket[x_,y_,z_]:=SpinorSquareBracket[x,z];
SpinorAngleBracket[x_,y_,z_]:=SpinorAngleBracket[x,z];
removed={};

If[Length@#>0,
localbrackets=sq;
Do[
labs=Alternatives@@({First@#,Last@#}&@First@i);
If[#>0,
ag=DeleteCases[ag,First@i,1,#];removed=Join[removed,ConstantArray[First@i,#]];]&@(Length@i-Count[localbrackets,labs,2]);
,{i,#}];
]&@Select[Gather[ag],(Length@#>1&)];

If[Length@#>0,
localbrackets=ag;
Do[
labs=Alternatives@@({First@#,Last@#}&@First@i);
If[#>0,sq=DeleteCases[sq,First@i,1,#];removed=Join[removed,ConstantArray[First@i,#]];]&@(Length@i-Count[localbrackets,labs,2]);
,{i,#}];
]&@Select[Gather[sq],(Length@#>1&)];


];

(*Find the momenta and their number*)
Block[{SpinorAngleBracket,SpinorSquareBracket},
SpinorSquareBracket[x_,y_,z_]:=SpinorSquareBracket[x,z];
SpinorAngleBracket[x_,y_,z_]:=SpinorAngleBracket[x,z];

(*These are the momenta and their multiplicities. They are found by extracting all the labels from the brackest, then counting the labels and looking at those which appear both as angle and squares. Then we take the minimum between the angle and square appearences, the mismatch gives the helicity weight which we do not need right now, the rest is the number of momenta which can be formed.*)
If[Length[momenta=Select[#,(Length@First@#==2&)]&@GatherBy[#,Length]&@GatherBy[Join@@Tally/@Flatten/@{List@@@ag,List@@@sq},First]]>0,
momenta={First@#1,Min@#2}&@@@Transpose/@First@momenta;
,
(*If momenta has length=0 no momenta are presents, no contractions can be made and we return the input list as it is*)
Return[exp];
];



(*Extract the positions of the brackets containg each momentum and then pair them*)
candidatecontractions=Flatten[#,1]&/@(Outer[List,#1,#2,1]&@@@({Position[ag,#],Position[sq,#]}&/@First@Transpose@momenta));

(*Out of the candidatecontractions I have to select subsets with number of elements given by the multiplicity of the given momentum and then apply a feasibility check: every bracket can only appear once per momentum.*)
chains=Subsets[#1,{#2}]&@@@Transpose@{candidatecontractions,Last@Transpose@momenta};
(*Apply check:*)
chains=DeleteCases[#,_?feasibilitytest]&/@chains;

(*Out of these we need to take all possible combinations.*)
chains=Flatten[#,1]&/@Tuples@chains;
];

(*Reoreder list such that the structure of contracted chains is visible*)
chains={Apply[chorder,GatherBy[#,#[[2,1]]&]&/@chains,{2}],Flatten@({Part[ag,#]&/@#1,Part[sq,#]&/@#2,removed,sign}&@@{Complement[Range@Length@ag,#1],Complement[Range@Length@sq,#2]}&@@Map[First,Transpose@#,{2}])&/@chains};

(*Next convert to chains the single parts*)
Block[{chorder},

(*Next we transformtraces from even to odd chains (so far we counted the number of momenta, now we count the number of connections)*)
chorder[{{i1_,j1_},{i2_,j2_}},x__,{{i1_,_},{_,_}}]:=chorder[{{i1,j1},{i2,j2}},x];

(*Build the chains*)
chorder[x__]:=ChainBuilder[{x},ag,sq];

(*Reconvert unique labels for mixed chains into original labels*)
pp[x_,_]:=x;

Return[Flatten/@Transpose@chains];
];

];


(* ::Subsubsection::Closed:: *)
(*toChainNew*)


(*toChainNew is the new version of ToChain which is slower (due to combinatorics) but build all possible chains and selects the once fitting the criteria chosen by the user*)

toChainNew[exp_,chainCrit_:"ShortestChain"]:=Module[{locexp,tochain,tochaininv,chainselect},
locexp=exp;
Block[{Power,Times},
Power[f_[x__],p_?Negative]/;f==SpinorAngleBracket||f==SpinorSquareBracket||f==Chain:=tochaininv[Sequence@@ConstantArray[f[x],-p]];
Power[f_[x__],p_]/;f==SpinorAngleBracket||f==SpinorSquareBracket||f==Chain:=tochain[Sequence@@ConstantArray[f[x],p]];
Times[z___,f_[x__],y___]/;f==SpinorAngleBracket||f==SpinorSquareBracket||f==Chain:=Times[z,tochain[f[x]],y];
locexp=locexp;
];
tochain /: Times[tochain[x__],tochain[y__],z___]:=Times[tochain[x,y],z];
tochaininv /: Times[tochaininv[x__],tochaininv[y__],z___]:=Times[tochaininv[x,y],z];
locexp=locexp;

(*Basing on the options we decide which chain we want to pick*)
Which[chainCrit==="ShortestChain",
chainselect[chains_List]:=Times@@Last@SortBy[chains,Length],
chainCrit==="LongestChain",
chainselect[chains_List]:=Times@@First@SortBy[chains,Length],
chainCrit==="MostTraces",
chainselect[chains_List]:=Times@@Last@SortBy[chains,Length@Cases[#,Chain[$angle,x_,{__},x_,$square]:>1]&],
True,
chainselect[chains_List]:=Times@@Last@SortBy[chains,Length]
];

tochain[x__]:=chainselect@AllChains[{x}];
tochaininv[x__]:=Power[chainselect@AllChains[{x}],-1];
Return[locexp];
];


(* ::Subsubsection:: *)
(*ToChain*)


Options[ToChain]={ChainSelection->"RandomChain"};
ToChain::opt="Unknown option, proceed with ShortestChain"


(*ToChain takes simply redirects the call to the appropriate algorithm*)
ToChain[exp_,OptionsPattern[]]:=Which[OptionValue[ChainSelection]==="RandomChain",
toChainOld[exp],
OptionValue[ChainSelection]==="ShortestChain",
toChainNew[exp,"ShortestChain"],
OptionValue[ChainSelection]==="LongestChain",
toChainNew[exp,"LongestChain"],
OptionValue[ChainSelection]==="MostTraces",
toChainNew[exp,"MostTraces"],
True,
Message[ToChain::opt];
toChainNew[exp]
];


(* ::Subsection::Closed:: *)
(*ChainToSpinor*)


ChainToSpinor[exp_]:=Block[{locexp,Chain},
(*Define the local properties of Chain which will allow for the splitting*)
Chain[$angle,a1_,{x___,y_,z___},a2_,type_]/;MasslessQ[y]:=If[OddQ[Length[{x,Null}]],
Chain[$angle,a1,{x},y,$angle]*Chain[$square,y,{z},a2,type],
Chain[$angle,a1,{x},y,$square]*Chain[$angle,y,{z},a2,type]];
Chain[$square,a1_,{x___,y_,z___},a2_,type_]/;MasslessQ[y]:=If[OddQ[Length[{x,Null}]],
Chain[$square,a1,{x},y,$square]*Chain[$angle,y,{z},a2,type],
Chain[$square,a1,{x},y,$angle]*Chain[$square,y,{z},a2,type]
];

(*Define locexp and let the definitions act*)
locexp=exp;

(*Replace empty chains with angle and square brackets*)
locexp=locexp/.{Chain[$angle,x_,{},y_,$angle]:>SpinorAngleBracket[x,y],Chain[$square,x_,{},y_,$square]:>SpinorSquareBracket[x,y]};

(*Return output*)
Return[locexp];
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
