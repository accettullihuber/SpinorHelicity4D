(* ::Package:: *)

(* ::Chapter:: *)
(*SpinorHelicity4D*)


BeginPackage["SpinorHelicity4D`",{"SpinorBuildingBlocks`","SpinorNumerics`"}]


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
ToMandelstam::usage="ToMandelstam[exp] converts products of brackets and scalar products of momenta into Mandelstam invariants where possible. So it turns \[LeftAngleBracket]ij\[RightAngleBracket][ji] and 2*mp[i,j] into the Mandelstam invariant S[i,j] for massless particles i,j."
ToChain::usage="ToChain[exp] closes spinors of the |p\[RightAngleBracket][p| into momenta building chains of spinor products. So for example \[LeftAngleBracket]1 2\[RightAngleBracket][2 3] becomes \[LeftAngleBracket]1 2 3]. ToChain allows for the option ChainSelection."
ChainSelection::usage="ChainSelection is an option for ToChain specifying which contraction to pick when multiple chains could be built out of the same brackets. Allowed values (given as strings) are ShortestChain, LongestChain ans MostTraces. For further information see the documentation."
ChainToSpinor::usage="ChainToSpinor[exp] transforms chain objects in exp into products of spinor brackets."
ChainMomentumCon::usage="ChainMomentumCon[exp,rule] applies momentum conservation to chains in exp following rule. If some of the momenta to be replaced appear as extrema of Dirac traces of the type \[LeftAngleBracket]p...p] this is rearranged in order to replace this momentum."
ChainSort::usage="ChainSort[exp,ordering_List] sorts momenta appearing in chains in exp according to the order of the list ordering. The second argument is optional, if omitted canonical ordering is applied."
ChainSimplify::usage="ChainSimplify[exp,Options] uses properties of the chains to simplify them, reducing them to products of chains where a given momentum appears at most once and scalar products. It allows for the options MomCon and ReduceComplete. Notice that in order for the simplifications to work best the momenta should be first declared through DeclareMom and massless momenta should be specified by DeclareMassless."
MomCon::usage="MomCon is an option for ChainSimplify which allows to use momentum conservation to simplify the chains. It must be defined as a list of replacements."
ReduceBySorting::usage="ReduceBySorting is an option for ChainSimplify, default is False. If set to True the function will order the momenta inside the chains. If set to a list of the ordering will follow the order in the list instead of canonical order."
epsSH::usage="epsSH[p1,p2,p3,p4] represents the a Levi-Civita tensor contracted into the four momenta p1,p2,p3,p4. These appear when converting spinor chains into Dirac traces with ToTrace."
TrG::usage="TrG[{p1,p2,...,pn}] computes the Dirac trace of the given list of slashed momenta."
TrG5::usage="TrG5[{p1,p2,...,pn}] computes the Dirac trace of the given list of slashed momenta with a single \!\(\*SubscriptBox[\(\[Gamma]\), \(5\)]\) insertion at the first position."
ToTrace::usage="ToTrace[exp] converts all closed chains of the form \[LeftAngleBracket]p|...|p] in exp into Dirac traces and evaluates them. It admits the Option EpsilonSimplify."
EpsilonSimplify::usage="EpsilonSimplify is an option for ToTrace whose default value is the string None. If set to the string ReduceEven even powers of the Levi-Civita tensors appearing in the final result of the evaluation are converted into scalar products. If set to KillOdd the even powers are replaced with scalar products and the odd ones are discarded."
CompleteDenominators::usage="CompleteDenominators[exp] completes all spinor products in the denominator of exp to Mandelstam invariants."
SpinorDerivative::usage="SpinorDerivative[exp,der] performs the derivative of exp with respect to the spinor expression der. The input der can be either a single spinor in the form \!\(\*TemplateBox[{\"q\", \"a\"},\n\"SpinorLaUp\",\nDisplayFunction->(RowBox[{SuperscriptBox[\"\[Lambda]\", #2], \"[\", #, \"]\"}]& ),\nInterpretationFunction->(RowBox[{\"SpinorUndot\", \"[\", #, \"]\", \"[\", \"$lam\", \"]\", \"[\", #2, \"]\", \"[\", \"Null\", \"]\"}]& )]\), \!\(\*TemplateBox[{\"p\", \"a\"},\n\"SpinorLaDown\",\nDisplayFunction->(RowBox[{SubscriptBox[\"\[Lambda]\", #2], \"[\", #, \"]\"}]& ),\nInterpretationFunction->(RowBox[{\"SpinorUndot\", \"[\", #, \"]\", \"[\", \"$lam\", \"]\", \"[\", \"Null\", \"]\", \"[\", #2, \"]\"}]& )]\) (and equivalent for dotted), a product of such spinors or a list of them."
SchoutenSimplify::usage="SchoutenSimplify[exp,opts] uses Schouten identities to simplify the expression exp. This function admits options opts, which are the same as those of FullSimplify, since indeed under the hood the function itself is based on Mathematica's FullSimplify."


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


(* ::Subsection::Closed:: *)
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
(*ToMandelstam*)


(* ::Subsubsection::Closed:: *)
(*CompleteMandelstam*)


(*Auxiliary for ToMandelstam, converts the brackets*)

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


(* ::Subsubsection::Closed:: *)
(*mpToMandelstam*)


(*Auxiliary, converts scalar product into mandelstams*)

mpToMandelstam[exp_]:=Block[{mp},
mp[x_?MasslessQ,y_?MasslessQ]:=1/2*S[x,y];
Return[exp];
];


(* ::Subsubsection::Closed:: *)
(*ToMandelstam*)


ToMandelstam= mpToMandelstam@CompleteMandelstam@#&;


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
(*toChainNew*)


Options[PreChain]={ChainSelection->"RandomChain"};

PreChain[exp_,OptionsPattern[]]:=Module[{aa,bb,ab,wrapper,invwrapper,local,mult,tmp},Block[{SpinorAngleBracket,SpinorSquareBracket,Chain},
local=exp;

(*Convert all the chains and spinor brackets into simpler objects and wrap them into a function which will chain them*)
SpinorAngleBracket[x__]:=wrapper[aa[x]];
SpinorSquareBracket[x__]:=wrapper[bb[x]];
Chain[$angle,x__,$angle]:=wrapper[aa[Sequence@@Flatten@{x}]];
Chain[$angle,x__,$square]:=wrapper[ab[Sequence@@Flatten@{x}]];
Chain[$square,x__,$angle]:=wrapper[ab[Sequence@@Reverse@Flatten@{x}]];
Chain[$square,x__,$square]:=wrapper[bb[Sequence@@Flatten@{x}]];

(*Define properties of the wrapper so that it wraps everything together, taking care of the powers. Inverse powers are the reason we need the auxiliary invwrapper, this would be needed if we could go deeper with the upvalues of wrapper...*)
wrapper /: wrapper[x_]*wrapper[y_]:=wrapper[x*y];
wrapper /: Power[wrapper[x_],n_?Positive]:=wrapper[Power[x,n]];
wrapper /: Power[wrapper[x_],n_?Negative]:=invwrapper[Power[x,-n]];
invwrapper /: invwrapper[x_]*invwrapper[y_]:=invwrapper[x*y];
local=local;

(*Reconvert the inwrapper to the inverse power of a wrapper*)
Clear[wrapper];
invwrapper[x_]:=Power[wrapper[x],-1];
local=local;

(*Next we want the wrapper to be ready to actually do stuff, so we group things together in lists: aa,bb,ab and ba separate, along with the product of already used stuff. First convert arguments of wrapper to a list*)
Clear[invwrapper];
wrapper[f_[x__]]:=If[f===Times,invwrapper[List[x]],invwrapper[{x}]];

(*Here we gather the objects by head, then replace powers by arrays with correct multiplicity, and finally make  atable with the elements of each type putting an empty list for the missing ones. We keep the invwrapper as an external container, so that once wrapper has done it's job, invwrapper can select the chain we want*)
local=local;
Clear[wrapper];
invwrapper[x_List]:=invwrapper[wrapper[1,1,Table[SelectFirst[GatherBy[Flatten[x/.Power->ConstantArray],Head],(#[[1,0]]===i&),{}],{i,{aa,ab,bb}}]]];

(*In order to get blown out of the water by combinatorics we need to take into account the multiplicity with which each bracket appears, i.e. its power. To do so "efficiently" we introduce another auxiliary function*)
wrapper[1,1,{a_,b_,c_}]:=wrapper[1,1,mult@@@Tally@a,mult@@@Tally@b,mult@@@Tally@c];
local=local;

(*When multiplicity reaches zero mult simply drops out of the game*)
mult[x_,0]:=Nothing[];

(*Now we clear the invwrapper and make the wrapper do the magic of combinatorics. The aa,bb,ba,ab objects get some specific properties which is what will build the chains*)
Clear[invwrapper,wrapper];

(*The wrapper acts recursively, testing its second argument's head and accordingly combining it with one of the elements in the lists of brackets. If no combination is possible the second argument is merged with the first one and a new cycle begins. Termination condition is that all lists are empty*)


(*Termination condition*)
wrapper[x_,y_,{},{},{}]:=x*y;

(*The starting point*)
wrapper[x_,1,a_,b_,c_]:=Which[a=!={},wrapper[x,a[[1,1]],ReplacePart[a,{1,2}->a[[1,2]]-1],b,c],b=!={},wrapper[x,b[[1,1]],a,ReplacePart[b,{1,2}->b[[1,2]]-1],c]];

(*If any two of the lists are empty and there are no brackets in the second slot of wrapper there is nothing to be done.*)
wrapper[x_,1,{},{},a_]:=x*Times@@Power@@@a;
wrapper[x_,1,{},a_,{}]:=x*Times@@Power@@@a;
wrapper[x_,1,a_,{},{}]:=x*Times@@Power@@@a;

(*GENERAL QUESTION: is this pattern matching aa[x_,y___,z_] faster or is aa[x__] with calling First@x every time faster?*)
(*Entry is aa*)
(*If upon parsing the lists of objects and making all the possible contractions an empty list is returned, we need to move the input entry to the overall product but and start a new iteration*)
wrapper[ex_,aa[x_,y___,z_],a_,b_,c_]:=If[#==={},wrapper[ex*aa[x,y,z],1,a,b,c],#]&@
Join[
(*Combining the last entry of the aa with all the first entries of the bb*)Table[If[c[[i,1,1]]===z,wrapper[ex,ab[x,y,Sequence@@(List@@c[[i,1]])],a,b,ReplacePart[c,{i,2}->c[[i,2]]-1]],Nothing[]],{i,Length@c}],
(*Combining the last entry of aa with the last of ab and bb*)Table[If[b[[i,1,-1]]===z,wrapper[ex,aa[x,y,Sequence@@Reverse@(b[[i,1]])],a,ReplacePart[b,{i,2}->b[[i,2]]-1],c],Nothing[]],{i,Length@b}],Table[If[c[[i,1,-1]]===z,wrapper[-ex,ab[x,y,Sequence@@Reverse@(c[[i,1]])],a,b,ReplacePart[c,{i,2}->c[[i,2]]-1]],Nothing[]],{i,Length@c}],
(*First entry of aa with first of bb*)Table[If[c[[i,1,1]]===x,wrapper[-ex,ab[Sequence@@Reverse@{y,z},Sequence@@(c[[i,1]])],a,b,ReplacePart[c,{i,2}->c[[i,2]]-1]],Nothing[]],{i,Length@c}],(*First of aa with last of ab*)Table[If[b[[i,1,-1]]===x,wrapper[ex,aa[Sequence@@(b[[i,1]]),y,z],a,ReplacePart[b,{i,2}->b[[i,2]]-1],c],Nothing[]],{i,Length@b}],(*First aa with last bb*)Table[If[c[[i,1,-1]]===x,wrapper[ex,ab[Sequence@@Reverse@{Sequence@@(c[[i,1]]),y,z}],a,b,ReplacePart[c,{i,2}->c[[i,2]]-1]],Nothing[]],{i,Length@c}]];

(*Entry in ab*)
wrapper[ex_,ab[x_,y___,z_],a_,b_,c_]:=If[#==={},wrapper[ex*ab[x,y,z],1,a,b,c],#]&@Join[(*Last ab with first aa*)Table[If[a[[i,1,1]]===z,wrapper[ex,aa[x,y,Sequence@@(a[[i,1]])],ReplacePart[a,{i,2}->a[[i,2]]-1],b,c],Nothing[]],{i,Length@a}],(*Last ab with last aa*)Table[If[a[[i,1,-1]]===z,wrapper[-ex,aa[x,y,Sequence@@Reverse@(a[[i,1]])],ReplacePart[a,{i,2}->a[[i,2]]-1],b,c],Nothing[]],{i,Length@a}],(*First ab with last bb*)Table[If[c[[i,1,-1]]===x,wrapper[ex,bb[Sequence@@(c[[i,1]]),y,z],a,b,ReplacePart[c,{i,2}->c[[i,2]]-1]],Nothing[]],{i,Length@c}],(*First ab with first bb*)Table[If[c[[i,1,1]]===x,wrapper[-ex,bb[Sequence@@Reverse@(c[[i,1]]),y,z],a,b,ReplacePart[c,{i,2}->c[[i,2]]-1]],Nothing[]],{i,Length@c}]];

(*Entry in bb. We simply plug it back into the bb list and restart, so we recycle definitions of aa and ab above*)
wrapper[ex_,bb[x__],a_,b_,c_]:=If[(tmp=Flatten[Position[c,bb[x]]])==={},wrapper[ex,1,a,b,Append[c,mult[bb[x],1]]],wrapper[ex,1,a,b,ReplacePart[c,{First@tmp,2}->c[[First@tmp,2]]+1]]];


(*Finally, invwrapper flattens out the nested lists and returns the one which best fits the selection criterion*)
Switch[OptionValue[ChainSelection],
"RandomChain",
invwrapper[x_List]:=First@Flatten[x],
"LongestChain",
invwrapper[x_List]:=#[[First@(FirstPosition[#,Min@#]&@(Total@Cases[{#},aa[y__]|bb[y__]|ab[y__]/;Length@{y}>2:>Length@{y},\[Infinity]]&/@#)&@#)]]&@Flatten[x],
"ShortestChain",
invwrapper[x_List]:=#[[First@(FirstPosition[#,Max@#]&@(Total@Cases[{#},aa[y__]|bb[y__]|ab[y__]/;Length@{y}>2:>Length@{y},\[Infinity]]&/@#)&@#)]]&@Flatten[x],
"MostTraces",
invwrapper[x_List]:=#[[First@(FirstPosition[#,Max@#,{1}]&@(Count[{#},ab[y_,z__,y_],\[Infinity]]&/@#)&@#)]]&@Flatten[x]
];

local=local;

(*Reconvert the aa,ab,bb to the spinor objects*)
Clear[SpinorAngleBracket,SpinorSquareBracket,Chain];
aa[x__]:=Chain[$angle,First@{x},Most@Rest@{x},Last@{x},$angle];
ab[x__]:=Chain[$angle,First@{x},Most@Rest@{x},Last@{x},$square];
bb[x__]:=Chain[$square,First@{x},Most@Rest@{x},Last@{x},$square];
Chain[$angle,x_,{},y_,$angle]:=SpinorAngleBracket[x,y];
Chain[$square,x_,{},y_,$square]:=SpinorSquareBracket[x,y];


(*Return the function*)
local
(*End of Block*)
]
(*End of Module*)
]


(* ::Subsubsection::Closed:: *)
(*ToChain*)


Options[ToChain]={ChainSelection->"RandomChain"};
ToChain::opt="Unknown option, proceed with RandomChain"


(*ToChain takes simply redirects the call to the appropriate algorithm*)
ToChain[exp_,ops:OptionsPattern[]]:=Switch[OptionValue[ChainSelection],"RandomChain",
toChainOld[exp],
"ShortestChain",
PreChain[exp,ops],
"LongestChain",
PreChain[exp,ops],
"MostTraces",
PreChain[exp,ops],
_,
Message[ToChain::opt];
toChainOld[exp]
];


(* ::Subsection::Closed:: *)
(*ChainToSpinor*)


ChainToSpinor[exp_]:=Block[{Chain},
(*Define the local properties of Chain which will allow for the splitting*)
Chain[$angle,a1_,{x___,y_,z___},a2_,type_]/;MasslessQ[y]:=If[OddQ[Length[{x,Null}]],
Chain[$angle,a1,{x},y,$angle]*Chain[$square,y,{z},a2,type],
Chain[$angle,a1,{x},y,$square]*Chain[$angle,y,{z},a2,type]];
Chain[$square,a1_,{x___,y_,z___},a2_,type_]/;MasslessQ[y]:=If[OddQ[Length[{x,Null}]],
Chain[$square,a1,{x},y,$square]*Chain[$angle,y,{z},a2,type],
Chain[$square,a1,{x},y,$angle]*Chain[$square,y,{z},a2,type]
];
Chain[$angle,x_,{},y_,$angle]:=SpinorAngleBracket[x,y];
Chain[$square,x_,{},y_,$square]:=SpinorSquareBracket[x,y];

(*Define locexp and let the definitions act*)
Return[exp];
];


(* ::Subsection::Closed:: *)
(*ChainMomentumCon*)


ChainMomentumCon[exp_,rule_]:=Module[{locexp,locrule,mom,mom2},

locexp=exp;
(*Take into account that rule could be a single rule or a list of rules*)
locrule=Flatten[{rule},1];
(*Convert replacements into lists*)
locrule=List@@@locrule;

(*Perform the replacements sequentially*)
Do[
mom=First@i;
mom2=Last@i;
(*Extrema replacement. Be careful that extrema replacements only work if there is an internal massless momentum which can take up the slot of extremum*)
locexp=locexp/.{Chain[$angle,mom,{x___,y_?MasslessQ,z___},mom,$square]:>Chain[$angle,y,{z,mom,x},y,$square],Chain[$square,mom,{x___,y_?MasslessQ,z___},mom,$angle]:>Chain[$square,y,{z,mom,x},y,$angle]};
(*Internal replacements*)
locexp=locexp/.{Chain[type1_,x1_,{y1___,mom,y2___},x2_,type2_]:>Chain[type1,x1,{y1,mom2,y2},x2,type2]};

,{i,locrule}];

Return[locexp];

];


(* ::Subsection:: *)
(*ChainSort*)


ChainSort[exp_,order_List:{}]:=Block[{Chain,SHorderedQ,SHlistordering},
(*Pick sorting criterion. If a non-empty list of labels is given we use this to sort the chains*)
If[Length[order]>0,
(*Custom order, in order to take into account that some of the elements in the chain may be missing from the list we need to check momenta which are far apart *)
SHlistordering=Flatten[Transpose@{ToString/@order,order}];
SHorderedQ=OrderedQ[#,(First@(FirstPosition[SHlistordering,#2])>=First@(FirstPosition[SHlistordering,#1])&)]&;

(*Reorder extrema among each other*)
Chain[type_,x1_,y_List,x2_,type_]/;!SHorderedQ[{x1,x2}]&&x1=!=x2:=-Chain[type,x2,Reverse@y,x1,type];
Chain[type_,x1_,y_List,x2_,type2_]/;!SHorderedQ[{x1,x2}]&&x1=!=x2:=Chain[type2,x2,Reverse@y,x1,type];

(*Define properties which reorder the chains with momenta in prescibed order*)
Chain[type_,x1_,{y1___,z1_?(MemberQ[SHlistordering,#]&),z2_?(MemberQ[SHlistordering,#]&),y2___},x2_,type2_]/;!SHorderedQ[{z1,z2}]:=2*mp[z1,z2]*Chain[type,x1,{y1,y2},x2,type2]-Chain[type,x1,{y1,z2,z1,y2},x2,type2];
Chain[type_,x1_,{y1___,z1_?(MemberQ[SHlistordering,#]&),y3___,y4_,z2_?(MemberQ[SHlistordering,#]&),y2___},x2_,type2_]/;!SHorderedQ[{z1,z2}]:=2*mp[y4,z2]*Chain[type,x1,{y1,z1,y3,y2},x2,type2]-Chain[type,x1,{y1,z1,y3,z2,y4,y2},x2,type2];

(*Dirac traces can also have the extrema reordered with internal momenta*)

Chain[$angle,x_?(MemberQ[SHlistordering,#]&),{y1___,y2_?((MemberQ[SHlistordering,#]&&MasslessQ[#])&),y3___},x_,$square]/; !SHorderedQ[{x,y2}]:=Chain[$angle,y2,{y3,x,y1},y2,$square];
Chain[$square,x_?(MemberQ[SHlistordering,#]&),{y1___,y2_?((MemberQ[SHlistordering,#]&&MasslessQ[#])&),y3___},x_,$angle]/; !SHorderedQ[{x,y2}]:=Chain[$square,y2,{y3,x,y1},y2,$angle];
,

(*Canonical ordering, easy case, criteria checked on adjacient elements*)
SHorderedQ=OrderedQ;

(*Reorder extrema among each other*)
Chain[type_,x1_,y_List,x2_,type_]/;!SHorderedQ[{x1,x2}]&&x1=!=x2:=-Chain[type,x2,Reverse@y,x1,type];
Chain[type_,x1_,y_List,x2_,type2_]/;!SHorderedQ[{x1,x2}]&&x1=!=x2:=Chain[type2,x2,Reverse@y,x1,type];

(*Define properties which reorder the chains with momenta in prescibed order*)
Chain[type_,x1_,{y1___,z1_,z2_,y2___},x2_,type2_]/;!OrderedQ[{z1,z2}]:=2*mp[z1,z2]*Chain[type,x1,{y1,y2},x2,type2]-Chain[type,x1,{y1,z2,z1,y2},x2,type2];

(*Dirac traces can also have the extrema reordered with internal momenta*)

Chain[$angle,x_,{y1___,y2_?(MasslessQ[#]&),y3___},x_,$square]/; !SHorderedQ[{x,y2}]:=Chain[$angle,y2,{y3,x,y1},y2,$square];
Chain[$square,x_,{y1___,y2_?(MasslessQ[#]&),y3___},x_,$angle]/; !SHorderedQ[{x,y2}]:=Chain[$square,y2,{y3,x,y1},y2,$angle];
];

Chain[$angle,x_,{},y_,$angle]:=SpinorAngleBracket[x,y];
Chain[$square,x_,{},y_,$square]:=SpinorSquareBracket[x,y];

Return[exp];
];


(* ::Subsection::Closed:: *)
(*ChainSimplify*)


(*Messages*)
ChainSimplify::momcon="Unknown form of momentum conservation, option MomCon ignored.";
ChainSimplify::sort="Unknown form of ordering, option ReduceBySorting ignored"

(*Options*)
Options[ChainSimplify]={MomCon->{},ReduceBySorting->False};

(*Function*)
ChainSimplify[exp_,OptionsPattern[]]:=
Module[{locexp},

locexp=exp;

(*Apply momentum conservation, if needed. This needs to be done outside the Block below because it requires linearity properties of chains to appropriately work.*)
Which[
	MatchQ[OptionValue[MomCon],{}],
	Null,
	AllTrue[OptionValue[MomCon],MatchQ[#,_Rule|_RuleDelayed]&],
	locexp=ChainMomentumCon[locexp,OptionValue[MomCon]],
	True,
	Message[ChainSimplify::momcon]];


(*Define local properties of chains for the simplification*)
Block[{Chain},
	Chain[type_,x_,{x_,y___},z_,type2_]:=0;
	Chain[type_,x_,{y___,z_},z_,type2_]:=0;
	Chain[type_,x_,{y___,z_,z_,k___},l_,type2_]:=mp[z,z]*Chain[type,x,{y,k},l,type2];
	Chain[type1_,p1_,{x___,y_,l___,z_,y_,k___},p2_,type2_]:=2*mp[y,z]*Chain[type1,p1,{x,y,l,k},p2,type2]-Chain[type1,p1,{x,y,l,y,z,k},p2,type2];
	Chain[t1_,x_,{y___,z_,x_,k___},p2_,t2_]:=2*mp[z,x]Chain[t1,x,{y,k},p2,t2]-Chain[t1,x,{y,x,z,k},p2,t2];
	Chain[t1_,p1_,{y___,z_,x_,k___},z_,t2_]:=2*mp[z,x]Chain[t1,p1,{y,k},z,t2]-Chain[t1,p1,{y,x,z,k},z,t2];
	Chain[$angle,x_,{y_},x_,$square]:=2*mp[x,y];
	Chain[$square,x_,{y_},x_,$angle]:=2*mp[x,y];
 Chain[$angle,x_,{},y_,$angle]:=SpinorAngleBracket[x,y];
Chain[$square,x_,{},y_,$square]:=SpinorSquareBracket[x,y];


(*If[Length@OptionValue[MomCon]>0,
locexp=ChainMomentumCon[locexp,OptionValue[MomCon]];
];*)

(*Reorder chains if necessary:*)
Switch[OptionValue[ReduceBySorting],
	False,
	Null,
	True,
	locexp=ChainSort[locexp],
	_List,
	locexp=ChainSort[locexp,OptionValue[ReduceBySorting]],
	_,
	Message[ChainSimplify::sort]];


(*If[OptionValue[ReduceComplete],
locexp=ChainOrder[locexp];
];*)

Return[locexp];
];

];


(* ::Subsection::Closed:: *)
(*epsSH*)


(*Display*)
epsSHBox[a_,b_,c_,d_]:=TemplateBox[{a,b,c,d},"epsSH",
DisplayFunction->(RowBox[{"\[Epsilon]","[",#1,",",#2,",",#3,",",#4,"]"}]&),
InterpretationFunction->(RowBox[{"epsSH","[",#1,",",#2,",",#3,",",#4,"]"}]&)
];
epsSH /: MakeBoxes[epsSH[a_,b_,c_,d_],StandardForm|TraditionalForm]:=epsSHBox[ToBoxes[a],ToBoxes[b],ToBoxes[c],ToBoxes[d]];

(*Contraction with twice the same vector vanishes*)
epsSH[x___,y_,z___,y_,k___]:=0;

(*Antisymmetry*)
epsSH[x___,y_,z_,k___]/;OrderedQ[{z,y}]:=-epsSH[x,z,y,k];

(*Linearity with respect to declared momenta*)
epsSH[x___,A_*y_String+z_,k___]:=A*epsSH[x,y,k]+epsSH[x,z,k];
epsSH[x___,y_String+z_,k___]:=epsSH[x,y,k]+epsSH[x,z,k];
epsSH[x___,Times[A_,y_String],z___]:=A*epsSH[x,y,z];


(* ::Subsection::Closed:: *)
(*TrG*)


(*Trace of gamma matrices*)

TrG[x_List]/;OddQ[Length[x]]:=0;
TrG[{}]:=4;
TrG[x_List]:=Sum[(-1)^i*mp[x[[1]],x[[i]]]TrG[Delete[x,{{1},{i}}]],{i,2,Length[x]}];


(* ::Subsection::Closed:: *)
(*TrG5*)


TrG5[x_List]/;Length[x]<4:=0;
TrG5[x_List]/;OddQ[Length[x]]:=0;
TrG5[x_List]:=mp[x[[-3]],x[[-2]]]*TrG5[Delete[x,{{-3},{-2}}]]+mp[x[[-2]],x[[-1]]]*TrG5[x[[;;-3]]]-mp[x[[-3]],x[[-1]]]*TrG5[Delete[x,{{-3},{-1}}]]-I*Sum[(-1)^i*epsSH[x[[-i]],x[[-3]],x[[-2]],x[[-1]]]*TrG[Delete[x[[;;-4]],{-(i-3)}]],{i,4,Length[x]}];


(* ::Subsection::Closed:: *)
(*ToTrace*)


Options[ToTrace]={EpsilonSimplify->"None"};

ToTrace::epsilonsim="Unknown value for the option EpsilonSimplify, proceed ingnoring it.";

ToTrace[exp_,OptionsPattern[]]:=Block[{Chain,epsSH},

Chain[$angle,a_,b_List,a_,$square]:=(TrG[Join[{a},b]]-TrG5[Join[{a},b]])/2;
Chain[$square,a_,b_List,a_,$angle]:=(TrG[Join[{a},b]]+TrG5[Join[{a},b]])/2;

(*Depending on the option specification for KillEpsilon we remove the Levi-Civita tensors*)

Switch[OptionValue[EpsilonSimplify],
	"None",Return[exp],
	"ReduceEven",
	(*Define the contraction properties of even powers of Levi-Civita*)
	epsSH /: Times[epsSH[a1_,b1_,c1_,d1_],epsSH[a2_,b2_,c2_,d2_]] := -(mp[a1,d2]*mp[a2,d1]*mp[b1,c2]*mp[b2,c1])+mp[a1,c2]*mp[a2,d1]*mp[b1,d2]*mp[b2,c1]+mp[a1,d2]*mp[a2,c1]*mp[b1,c2]*mp[b2,d1]-mp[a1,c2]*mp[a2,c1]*mp[b1,d2]*mp[b2,d1]+mp[a1,d2]*mp[a2,d1]*mp[b1,b2]*mp[c1,c2]-mp[a1,b2]*mp[a2,d1]*mp[b1,d2]*mp[c1,c2]-mp[a1,d2]*mp[a2,b1]*mp[b2,d1]*mp[c1,c2]+mp[a1,a2]*mp[b1,d2]*mp[b2,d1]*mp[c1,c2]-mp[a1,c2]*mp[a2,d1]*mp[b1,b2]*mp[c1,d2]+mp[a1,b2]*mp[a2,d1]*mp[b1,c2]*mp[c1,d2]+mp[a1,c2]*mp[a2,b1]*mp[b2,d1]*mp[c1,d2]-mp[a1,a2]*mp[b1,c2]*mp[b2,d1]*mp[c1,d2]-mp[a1,d2]*mp[a2,c1]*mp[b1,b2]*mp[c2,d1]+mp[a1,b2]*mp[a2,c1]*mp[b1,d2]*mp[c2,d1]+mp[a1,d2]*mp[a2,b1]*mp[b2,c1]*mp[c2,d1]-mp[a1,a2]*mp[b1,d2]*mp[b2,c1]*mp[c2,d1]-mp[a1,b2]*mp[a2,b1]*mp[c1,d2]*mp[c2,d1]+mp[a1,a2]*mp[b1,b2]*mp[c1,d2]*mp[c2,d1]+mp[a1,c2]*mp[a2,c1]*mp[b1,b2]*mp[d1,d2]-mp[a1,b2]*mp[a2,c1]*mp[b1,c2]*mp[d1,d2]-mp[a1,c2]*mp[a2,b1]*mp[b2,c1]*mp[d1,d2]+mp[a1,a2]*mp[b1,c2]*mp[b2,c1]*mp[d1,d2]+mp[a1,b2]*mp[a2,b1]*mp[c1,c2]*mp[d1,d2]-mp[a1,a2]*mp[b1,b2]*mp[c1,c2]*mp[d1,d2];
	epsSH /: Power[epsSH[a1_,b1_,c1_,d1_],n_?EvenQ]:=(-(mp[a1,d1]^2*mp[b1,c1]^2)+2*mp[a1,c1]*mp[a1,d1]*mp[b1,c1]*mp[b1,d1]-mp[a1,c1]^2*mp[b1,d1]^2+mp[a1,d1]^2*mp[b1,b1]*mp[c1,c1]-2*mp[a1,b1]*mp[a1,d1]*mp[b1,d1]*mp[c1,c1]+mp[a1,a1]*mp[b1,d1]^2*mp[c1,c1]-2*mp[a1,c1]*mp[a1,d1]*mp[b1,b1]*mp[c1,d1]+2*mp[a1,b1]*mp[a1,d1]*mp[b1,c1]*mp[c1,d1]+2*mp[a1,b1]*mp[a1,c1]*mp[b1,d1]*mp[c1,d1]-2*mp[a1,a1]*mp[b1,c1]*mp[b1,d1]*mp[c1,d1]-mp[a1,b1]^2*mp[c1,d1]^2+mp[a1,a1]*mp[b1,b1]*mp[c1,d1]^2+mp[a1,c1]^2*mp[b1,b1]*mp[d1,d1]-2*mp[a1,b1]*mp[a1,c1]*mp[b1,c1]*mp[d1,d1]+mp[a1,a1]*mp[b1,c1]^2*mp[d1,d1]+mp[a1,b1]^2*mp[c1,c1]*mp[d1,d1]-mp[a1,a1]*mp[b1,b1]*mp[c1,c1]*mp[d1,d1])^(n/2);
	Return[Expand[exp,epsSH]],
	"KillOdd",
	(*Define the contraction properties of even powers of Levi-Civita*)
	epsSH /: Times[epsSH[a1_,b1_,c1_,d1_],epsSH[a2_,b2_,c2_,d2_]] := -(mp[a1,d2]*mp[a2,d1]*mp[b1,c2]*mp[b2,c1])+mp[a1,c2]*mp[a2,d1]*mp[b1,d2]*mp[b2,c1]+mp[a1,d2]*mp[a2,c1]*mp[b1,c2]*mp[b2,d1]-mp[a1,c2]*mp[a2,c1]*mp[b1,d2]*mp[b2,d1]+mp[a1,d2]*mp[a2,d1]*mp[b1,b2]*mp[c1,c2]-mp[a1,b2]*mp[a2,d1]*mp[b1,d2]*mp[c1,c2]-mp[a1,d2]*mp[a2,b1]*mp[b2,d1]*mp[c1,c2]+mp[a1,a2]*mp[b1,d2]*mp[b2,d1]*mp[c1,c2]-mp[a1,c2]*mp[a2,d1]*mp[b1,b2]*mp[c1,d2]+mp[a1,b2]*mp[a2,d1]*mp[b1,c2]*mp[c1,d2]+mp[a1,c2]*mp[a2,b1]*mp[b2,d1]*mp[c1,d2]-mp[a1,a2]*mp[b1,c2]*mp[b2,d1]*mp[c1,d2]-mp[a1,d2]*mp[a2,c1]*mp[b1,b2]*mp[c2,d1]+mp[a1,b2]*mp[a2,c1]*mp[b1,d2]*mp[c2,d1]+mp[a1,d2]*mp[a2,b1]*mp[b2,c1]*mp[c2,d1]-mp[a1,a2]*mp[b1,d2]*mp[b2,c1]*mp[c2,d1]-mp[a1,b2]*mp[a2,b1]*mp[c1,d2]*mp[c2,d1]+mp[a1,a2]*mp[b1,b2]*mp[c1,d2]*mp[c2,d1]+mp[a1,c2]*mp[a2,c1]*mp[b1,b2]*mp[d1,d2]-mp[a1,b2]*mp[a2,c1]*mp[b1,c2]*mp[d1,d2]-mp[a1,c2]*mp[a2,b1]*mp[b2,c1]*mp[d1,d2]+mp[a1,a2]*mp[b1,c2]*mp[b2,c1]*mp[d1,d2]+mp[a1,b2]*mp[a2,b1]*mp[c1,c2]*mp[d1,d2]-mp[a1,a2]*mp[b1,b2]*mp[c1,c2]*mp[d1,d2];
	epsSH /: Power[epsSH[a1_,b1_,c1_,d1_],n_?EvenQ]:=(-(mp[a1,d1]^2*mp[b1,c1]^2)+2*mp[a1,c1]*mp[a1,d1]*mp[b1,c1]*mp[b1,d1]-mp[a1,c1]^2*mp[b1,d1]^2+mp[a1,d1]^2*mp[b1,b1]*mp[c1,c1]-2*mp[a1,b1]*mp[a1,d1]*mp[b1,d1]*mp[c1,c1]+mp[a1,a1]*mp[b1,d1]^2*mp[c1,c1]-2*mp[a1,c1]*mp[a1,d1]*mp[b1,b1]*mp[c1,d1]+2*mp[a1,b1]*mp[a1,d1]*mp[b1,c1]*mp[c1,d1]+2*mp[a1,b1]*mp[a1,c1]*mp[b1,d1]*mp[c1,d1]-2*mp[a1,a1]*mp[b1,c1]*mp[b1,d1]*mp[c1,d1]-mp[a1,b1]^2*mp[c1,d1]^2+mp[a1,a1]*mp[b1,b1]*mp[c1,d1]^2+mp[a1,c1]^2*mp[b1,b1]*mp[d1,d1]-2*mp[a1,b1]*mp[a1,c1]*mp[b1,c1]*mp[d1,d1]+mp[a1,a1]*mp[b1,c1]^2*mp[d1,d1]+mp[a1,b1]^2*mp[c1,c1]*mp[d1,d1]-mp[a1,a1]*mp[b1,b1]*mp[c1,c1]*mp[d1,d1])^(n/2);
	Return[Expand[exp,epsSH]//.epsSH[x__]:>0],
	_,Message[ToTrace::epsilonsim];
];

];


(* ::Subsection::Closed:: *)
(*CompleteDenominators*)


CompleteDenominators[exp_]:=exp/.{Power[SpinorAngleBracket[a_,b_],n_?Negative]:>Power[S[a,b]/SpinorSquareBracket[b,a],n],Power[SpinorSquareBracket[a_,b_],n_?Negative]:>Power[S[a,b]/SpinorAngleBracket[b,a],n]};


(* ::Subsection:: *)
(*SchoutenSimplify*)


(* ::Subsubsection:: *)
(*SchoutenRules*)


(*Function to extract the pairs for which to build the Schouten-identity rules*)

SchoutenRules[exp_]:=Module[{agl,sqr},
(*Extract all brackets which are multiplied among each other*)
agl=Cases[{exp},Times[x__?(Head[#]===SpinorAngleBracket&),y___]:>List[x],\[Infinity]];
sqr=Cases[{exp},Times[x__?(Head[#]===SpinorSquareBracket&),y___]:>List[x],\[Infinity]];

(*Make pairs taking into account that indices cannot overAutomaticlap*)
agl=ruleBuilder@@@(Union[Join@@(pairSelector/@agl)]);
sqr=ruleBuilder@@@(Union[Join@@(pairSelector/@sqr)]);

Return[Join[agl,sqr]]

]

(*Function to convert products of brackets into pairs which allow Schouten identities*)

pairSelector[{x_}]:={};
pairSelector[pairlist_]:={Splice[Table[If[Intersection[Sequence@@(List@@@#)]==={},#,Nothing]&@{First@pairlist,i},{i,Rest@pairlist}]],Splice[pairSelector[Rest@pairlist]]}

(*Function to convert a product of brackets into the associated Schouten identity*)

ruleBuilder[f_[a_,b_],f_[c_,d_]]:=(f[a,b]f[c,d]->-f[a,c]f[d,b]-f[a,d]f[b,c])


(* ::Subsubsection:: *)
(*SchoutenApply*)


(*Function to convert a set of rules to something TransformationRules of Simplify can use*)

toSingleRules[rules_]:=Function[e,e/.#]&/@rules;

(*This functions tryies to apply only Schouten identities to simplify an expression, which means that the expression needs to be already in a factorised form for this to work, so we will feed this into a Simplify*)
SchoutenApply[exp_,opts:OptionsPattern[FullSimplify]]:=Module[{rules=SchoutenRules[exp]},FullSimplify[exp,opts,TransformationFunctions->toSingleRules[rules]]]


(* ::Subsubsection:: *)
(*SchoutenSimplify*)


(*Function which applies Schouten identities to simplify expression. It admits the same options as FullSimplify.*)

SchoutenSimplify[exp_,opts:OptionsPattern[FullSimplify]]:=FullSimplify[exp,opts,TransformationFunctions->{Automatic,SchoutenApply[#,opts]&}]


(* ::Subsection:: *)
(*SpinorDerivative*)


(* ::Subsubsection::Closed:: *)
(*Auxiliary functions*)


(*The auxiliary functions actually perform the differentiation, there is four of them, one for each type of spinor.*)


SpinorDerivativeDot[exp_,SpinorDot[p_][type_][a_][Null]]:=Module[{local,globaloptions},

(*save options for D*)
globaloptions=OptionValue[D,NonConstants];
(*Set the options for SpinorSquareBracket and SpinorDot to be considered as functions of what we take the derivative*)
SetOptions[D,NonConstants->{SpinorDot,SpinorSquareBracket}];

(*Now Mathematica will apply differentiation but keeps the last step as it is since it does not know how to differentiate spinors*)
local=D[exp,SpinorDot[p][type][a][Null]];

(*Set global options for D back to what they where*)
SetOptions[D,NonConstants->globaloptions];

(*Now teach him how to derive spinors*)
Block[{SpinorDot,SpinorSquareBracket},

(*Define the derivatives. we also have to take into account the type of the objects in the bracket*)
SpinorDot /: D[SpinorDot[p][type][a1_][Null],SpinorDot[p][type][a][Null],___]:=DeltaTildeSH[a1,a];
SpinorDot /: D[SpinorDot[p][type][Null][a1_],SpinorDot[p][type][a][Null],___]:=LeviCivitaSH[a1,a][$down];

(*The rules for the contracted spinors are more complicated, because we have to embed in the rules the distinction between reference and lamda spinor*)
If[type===$lam,
(*Make sure that derivative of references is zero. Alos take into account the special case [p,obar[p]]*)
SpinorSquareBracket /: D[SpinorSquareBracket[p,obar[p]],SpinorDot[p][type][a][Null],___]:=-SpinorDot[p][$mu][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[p],q_],SpinorDot[p][type][_][_],___]:=0;
SpinorSquareBracket /:D[SpinorSquareBracket[q_,obar[p]],SpinorDot[p][type][_][_],___]:=0;

(*Define the actual derivatives for the spinor*)
SpinorSquareBracket /: D[SpinorSquareBracket[p,obar[q_]],SpinorDot[p][type][a][Null],___]:=-SpinorDot[q][$mu][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[p,q_],SpinorDot[p][type][a][Null],___]:=-SpinorDot[q][$lam][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[q_],p],SpinorDot[p][type][a][Null],___]:=SpinorDot[q][$mu][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[q_,p],SpinorDot[p][type][a][Null],___]:=SpinorDot[q][$lam][Null][a];
,
(*The derivative is taken with respect to a reference spinor*)
SpinorSquareBracket /: D[SpinorSquareBracket[obar[p],obar[q_]],SpinorDot[p][type][a][Null],___]:=-SpinorDot[q][$mu][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[p],q_],SpinorDot[p][type][a][Null],___]:=-SpinorDot[q][$lam][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[q_],obar[p]],SpinorDot[p][type][a][Null],___]:=SpinorDot[q][$mu][Null][a];
SpinorSquareBracket /: D[SpinorSquareBracket[q_,obar[p]],SpinorDot[p][type][a][Null],___]:=SpinorDot[q][$lam][Null][a];
];




(*Take care of the fact that the SpinorDot and SpinorUndot are deep functions...*)
Block[{D},
D[SpinorDot[x_],y_,op___][a0_][a1_][a2_]:=D[SpinorDot[x][a0][a1][a2],y];
D[SpinorSquareBracket[x__],y_,___]:=0;
local=local;

];

];


(*Return output*)
local
];


SpinorDerivativeDot[exp_,SpinorDot[p_][type_][Null][a_]]:=Module[{local,globaloptions},

(*save options for D*)
globaloptions=OptionValue[D,NonConstants];
(*Set the options for SpinorSquareBracket and SpinorDot to be considered as functions of what we take the derivative*)
SetOptions[D,NonConstants->{SpinorDot,SpinorSquareBracket}];

(*Now Mathematica will apply differentiation but keeps the last step as it is since it does not know how to differentiate spinors*)
local=D[exp,SpinorDot[p][type][Null][a]];

(*Set global options for D back to what they where*)
SetOptions[D,NonConstants->globaloptions];

(*Now teach him how to derive spinors*)
Block[{SpinorDot,SpinorSquareBracket},

(*Define the derivatives. we also have to take into account the type of the objects in the bracket*)
SpinorDot /: D[SpinorDot[p][type][a1_][Null],SpinorDot[p][type][Null][a],___]:=LeviCivitaSH[a1,a][$up];
SpinorDot /: D[SpinorDot[p][type][Null][a1_],SpinorDot[p][type][Null][a],___]:=DeltaTildeSH[a,a1];

(*The rules for the contracted spinors are more complicated, because we have to embed in the rules the distinction between reference and lamda spinor*)
If[type===$lam,
(*Make sure that derivative of references is zero. Alos take into account the special case [p,obar[p]]*)
SpinorSquareBracket /: D[SpinorSquareBracket[p,obar[p]],SpinorDot[p][type][Null][a],___]:=SpinorDot[p][$mu][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[p],q_],SpinorDot[p][type][_][_],___]:=0;
SpinorSquareBracket /:D[SpinorSquareBracket[q_,obar[p]],SpinorDot[p][type][_][_],___]:=0;

(*Define the actual derivatives for the spinor*)
SpinorSquareBracket /: D[SpinorSquareBracket[p,obar[q_]],SpinorDot[p][type][Null][a],___]:=SpinorDot[q][$mu][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[p,q_],SpinorDot[p][type][Null][a],___]:=SpinorDot[q][$lam][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[q_],p],SpinorDot[p][type][Null][a],___]:=-SpinorDot[q][$mu][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[q_,p],SpinorDot[p][type][Null][a],___]:=-SpinorDot[q][$lam][a][Null];
,
(*The derivative is taken with respect to a reference spinor*)
SpinorSquareBracket /: D[SpinorSquareBracket[obar[p],obar[q_]],SpinorDot[p][type][Null][a],___]:=SpinorDot[q][$mu][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[p],q_],SpinorDot[p][type][Null][a],___]:=SpinorDot[q][$lam][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[obar[q_],obar[p]],SpinorDot[p][type][Null][a],___]:=-SpinorDot[q][$mu][a][Null];
SpinorSquareBracket /: D[SpinorSquareBracket[q_,obar[p]],SpinorDot[p][type][Null][a],___]:=-SpinorDot[q][$lam][a][Null];
];




(*Take care of the fact that the SpinorDot and SpinorUndot are deep functions...*)
Block[{D},
D[SpinorDot[x_],y_,op___][a0_][a1_][a2_]:=D[SpinorDot[x][a0][a1][a2],y];
D[SpinorSquareBracket[x__],y_,___]:=0;
local=local;

];

];


(*Return output*)
local
];


SpinorDerivativeUndot[exp_,SpinorUndot[p_][type_][a_][Null]]:=Module[{local,globaloptions},

(*save options for D*)
globaloptions=OptionValue[D,NonConstants];
(*Set the options for SpinorAngleBracket and SpinorUndot to be considered as functions of what we take the derivative*)
SetOptions[D,NonConstants->{SpinorUndot,SpinorAngleBracket}];

(*Now Mathematica will apply differentiation but keeps the last step as it is since it does not know how to differentiate spinors*)
local=D[exp,SpinorUndot[p][type][a][Null]];

(*Set global options for D back to what they where*)
SetOptions[D,NonConstants->globaloptions];

(*Now teach him how to derive spinors*)
Block[{SpinorUndot,SpinorAngleBracket},

(*Define the derivatives. we also have to take into account the type of the objects in the bracket*)
SpinorUndot /: D[SpinorUndot[p][type][a1_][Null],SpinorUndot[p][type][a][Null],___]:=DeltaSH[a1,a];
SpinorUndot /: D[SpinorUndot[p][type][Null][a1_],SpinorUndot[p][type][a][Null],___]:=LeviCivitaSH[a1,a][$down];

(*The rules for the contracted spinors are more complicated, because we have to embed in the rules the distinction between reference and lamda spinor*)
If[type===$lam,
(*Make sure that derivative of references is zero. Alos take into account the special case [p,obar[p]]*)
SpinorAngleBracket /: D[SpinorAngleBracket[p,obar[p]],SpinorUndot[p][type][a][Null],___]:=SpinorUndot[p][$mu][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[p],q_],SpinorUndot[p][type][_][_],___]:=0;
SpinorAngleBracket /:D[SpinorAngleBracket[q_,obar[p]],SpinorUndot[p][type][_][_],___]:=0;

(*Define the actual derivatives for the spinor*)
SpinorAngleBracket /: D[SpinorAngleBracket[p,obar[q_]],SpinorUndot[p][type][a][Null],___]:=SpinorUndot[q][$mu][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[p,q_],SpinorUndot[p][type][a][Null],___]:=SpinorUndot[q][$lam][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[q_],p],SpinorUndot[p][type][a][Null],___]:=-SpinorUndot[q][$mu][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[q_,p],SpinorUndot[p][type][a][Null],___]:=-SpinorUndot[q][$lam][Null][a];
,
(*The derivative is taken with respect to a reference spinor*)
SpinorAngleBracket /: D[SpinorAngleBracket[obar[p],obar[q_]],SpinorUndot[p][type][a][Null],___]:=SpinorUndot[q][$mu][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[p],q_],SpinorUndot[p][type][a][Null],___]:=SpinorUndot[q][$lam][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[q_],obar[p]],SpinorUndot[p][type][a][Null],___]:=-SpinorUndot[q][$mu][Null][a];
SpinorAngleBracket /: D[SpinorAngleBracket[q_,obar[p]],SpinorUndot[p][type][a][Null],___]:=-SpinorUndot[q][$lam][Null][a];
];




(*Take care of the fact that the SpinorUndot and SpinorUndot are deep functions...*)
Block[{D},
D[SpinorUndot[x_],y_,op___][a0_][a1_][a2_]:=D[SpinorUndot[x][a0][a1][a2],y];
D[SpinorAngleBracket[x__],y_,___]:=0;
local=local;

];

];


(*Return output*)
local
];


SpinorDerivativeUndot[exp_,SpinorUndot[p_][type_][Null][a_]]:=Module[{local,globaloptions},

(*save options for D*)
globaloptions=OptionValue[D,NonConstants];
(*Set the options for SpinorAngleBracket and SpinorUndot to be considered as functions of what we take the derivative*)
SetOptions[D,NonConstants->{SpinorUndot,SpinorAngleBracket}];

(*Now Mathematica will apply differentiation but keeps the last step as it is since it does not know how to differentiate spinors*)
local=D[exp,SpinorUndot[p][type][Null][a]];

(*Set global options for D back to what they where*)
SetOptions[D,NonConstants->globaloptions];

(*Now teach him how to derive spinors*)
Block[{SpinorUndot,SpinorAngleBracket},

(*Define the derivatives. we also have to take into account the type of the objects in the bracket*)
SpinorUndot /: D[SpinorUndot[p][type][a1_][Null],SpinorUndot[p][type][Null][a],___]:=LeviCivitaSH[a1,a][$up];
SpinorUndot /: D[SpinorUndot[p][type][Null][a1_],SpinorUndot[p][type][Null][a],___]:=DeltaSH[a,a1];

(*The rules for the contracted spinors are more complicated, because we have to embed in the rules the distinction between reference and lamda spinor*)
If[type===$lam,
(*Make sure that derivative of references is zero. Alos take into account the special case [p,obar[p]]*)
SpinorAngleBracket /: D[SpinorAngleBracket[p,obar[p]],SpinorUndot[p][type][Null][a],___]:=-SpinorUndot[p][$mu][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[p],q_],SpinorUndot[p][type][_][_],___]:=0;
SpinorAngleBracket /:D[SpinorAngleBracket[q_,obar[p]],SpinorUndot[p][type][_][_],___]:=0;

(*Define the actual derivatives for the spinor*)
SpinorAngleBracket /: D[SpinorAngleBracket[p,obar[q_]],SpinorUndot[p][type][Null][a],___]:=-SpinorUndot[q][$mu][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[p,q_],SpinorUndot[p][type][Null][a],___]:=-SpinorUndot[q][$lam][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[q_],p],SpinorUndot[p][type][Null][a],___]:=SpinorUndot[q][$mu][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[q_,p],SpinorUndot[p][type][Null][a],___]:=SpinorUndot[q][$lam][a][Null];
,
(*The derivative is taken with respect to a reference spinor*)
SpinorAngleBracket /: D[SpinorAngleBracket[obar[p],obar[q_]],SpinorUndot[p][type][Null][a],___]:=-SpinorUndot[q][$mu][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[p],q_],SpinorUndot[p][type][Null][a],___]:=-SpinorUndot[q][$lam][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[obar[q_],obar[p]],SpinorUndot[p][type][Null][a],___]:=SpinorUndot[q][$mu][a][Null];
SpinorAngleBracket /: D[SpinorAngleBracket[q_,obar[p]],SpinorUndot[p][type][Null][a],___]:=SpinorUndot[q][$lam][a][Null];
];




(*Take care of the fact that the SpinorUndot and SpinorUndot are deep functions...*)
Block[{D},
D[SpinorUndot[x_],y_,op___][a0_][a1_][a2_]:=D[SpinorUndot[x][a0][a1][a2],y];
D[SpinorAngleBracket[x__],y_,___]:=0;
local=local;

];

];


(*Return output*)
local
];


(* ::Subsubsection::Closed:: *)
(*The function for the user*)


SpinorDerivative::inv="Cannot differentiate with respect to the given quantity. Please check your input or the documentation for help.";


SpinorDerivative[exp_,labs_]:=Module[{loclabs,ang,squ},

(*If it is derivative with respect to asingle spinor return output directly, else make into a list and apply spinor derivative multiple times*)
Switch[Head[labs],
SpinorDot[_][_][_],
Return[SpinorDerivativeDot[exp,labs]],
SpinorUndot[_][_][_],
Return[SpinorDerivativeUndot[exp,labs]],
List,
loclabs=labs;
,
Times,
If[AllTrue[labs,(MatchQ[Head[#],SpinorBuildingBlocks`SpinorDot[_][_][_]]||MatchQ[Head[#],SpinorBuildingBlocks`SpinorUndot[_][_][_]]&)],
loclabs=List@@labs,
Message[SpinorDerivative::inv];
Return[$Failed]
];
];

(*Now we send each input to the appropriate differentiation function*)
loclabs=GatherBy[loclabs,#[[0,0,0,0]]&];
ang=SelectFirst[loclabs,#[[1,0,0,0,0]]===SpinorBuildingBlocks`SpinorUndot&,{}];
squ=SelectFirst[loclabs,#[[1,0,0,0,0]]===SpinorBuildingBlocks`SpinorDot&,{}];

(*Now apply the proper derivatives in sequence*)
loclabs=Fold[SpinorDerivativeUndot,exp,ang];
Fold[SpinorDerivativeDot,loclabs,squ]

];


(* ::Section:: *)
(*End of context*)


(*Open palette*)
If[frontend==1,
CreatePalette[DynamicModule[{opener1=True,opener2=False},Column[{OpenerView[{"Spinors",Grid[Join[Partition[PasteButton[RawBoxes[#]]&/@{SpinorBuildingBlocks`Private`SpinorLaUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLaDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLatUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorLatDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorUndotBareLBox["\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SpinorDotBareLBox["\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`LevicivitaSHBoxUp["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`LevicivitaSHBoxDown["\[SelectionPlaceholder]","\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`AngleSquareChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SquareAngleChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`AngleAngleChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"],SpinorBuildingBlocks`Private`SquareSquareChainBox["\[SelectionPlaceholder]",ToBoxes[{\[SelectionPlaceholder]}],"\[SelectionPlaceholder]"]},4],{{PasteButton[RawBoxes[SpinorBuildingBlocks`Private`SpinorAngleBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]],SpanFromLeft,PasteButton[RawBoxes[SpinorBuildingBlocks`Private`SpinorSquareBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]],SpanFromLeft}}],Spacings->{2,0.6}]},Dynamic[opener1,(opener1=#;opener2=opener2)&]],OpenerView[{"Vectors",Grid[{1,2,3,4},Spacings->Automatic]},Dynamic[opener2,(opener2=#;opener1=opener1)&]]}]],WindowTitle->"SpinorHelicity4DInput",Saveable->False];
];


Print["===============SpinorHelicity4D=============="];
Print["Author: Manuel Accettulli Huber (QMUL)"];
Print["Please report any bug to:"];
Print["m.accettullihuber@qmul.ac.uk"];
Print["Version 1.0 , last update 15/01/2023"];
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
