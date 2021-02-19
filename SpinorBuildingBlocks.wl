(* ::Package:: *)

(* ::Chapter:: *)
(*SpinorBuildingBlocks*)


BeginPackage["SpinorBuildingBlocks`"]


(*In order to allow the package to be reloaded we unprotect and clear all the symbol definitions*)
Unprotect@@Names["SpinorBuildingBlocks`*"];
ClearAll@@Names["SpinorBuildingBlocks`*"];


(* ::Section:: *)
(*Function description*)


(* ::Subsection:: *)
(*Label declaration*)


DeclareMom::usage="DeclareMom[p,q,...] adds p,q,... to the list of momenta known to the package. Declaring momenta is not necessary but allows for the use of certain properties (like linearity) of functions like Chain and mp. Numbers cannot be declared as momentum labels. To access the list of declared labels use DeclareMom[] without arguments."
UndeclareMom::usage="UndeclareMom[p,q,...] removes p,q,... from the list of known momenta. UndeclareMom[] clears the list of declared momenta."
(*MomList::usage="MomList is the list containing all the labels which have been declared to be momenta. Names for momenta can be declared through DeclareMom."*)
DeclareMassless::usage="DeclareMassless[p,q,k,...] adds p,q,k,... to the list of massless momenta. Also it automatically adds p,q,k,... to the list of momentum labels. To access the list of massless momenta use DeclareMassless[] without any arguments."
(*MasslessMomenta::usage="MasslessMomenta is the list of momenta which have been declared to be massless through DeclareMassless."*)
UndeclareMassless::usage="UndeclareMassless[p,q,...] removes p,q,... from the list of massless momenta. UndeclareMassless[] clears the list of massless momenta."


(* ::Subsection:: *)
(*Auxiliary functions*)


obar::usage="obar[p] is used inside invariants such as the angle and square brackets when the momentum p has to be interpreted as a reference momentum and thus associated spinors will be of the type \[Mu](p). obar is linear with respect to members of MomList."
$lam::usage="Protected label for the \[Lambda] spinors."
$mu::usage="Protected label for the \[Mu] spinors."
$angle::usage="Protected label for angle bracket in Chain."
$square::usage="Protected label for square bracket in Chain."
$up::usage="Protected label used for type specification in certain functions."
$down::usage="Protected label used for type specification in certain functions."
$Shortcuts::usage="$Shortcuts returns a list of all the available shortcuts for expression input."


(* ::Subsection:: *)
(*Building blocks*)


SpinorUndot::usage="SpinorUndot[momlabel][type][upper][lower] represents the generic four-dimensional spinor with undotted indices. The type is either $lam for \[Lambda] spinors or $mu for \[Mu] spinors. The label upper is for the upper spinor index and lower for the lower index, one of them needs to be Null. Explicit usage of this function can be easily avoided through the shortcuts, the palette or a custom definition. For further details see the documentation."
SpinorDot::usage="SpinorDot[momlabel][type][upper][lower] represents the generic four-dimensional spinor with dotted indices. The type is either $lam for \[Lambda] spinors or $mu for \[Mu] spinors. The label upper is for the upper spinor index and lower for the lower index, one of them needs to be Null. Explicit usage of this function can be easily avoided through the shortcuts, the palette or a custom definition. For further details see the documentation."
SpinorDotBare::usage="SpinorDotBare[p][type] represents a dotted spinor stripped of its Lorentz indices. Type assumes values $lam or $mu. This object is used mainly in SpinorReplace to define replacement rules."
SpinorUndotBare::usage="SpinorUndotBare[p][type] represents an undotted spinor stripped of its Lorentz indices. Type assumes values $lam or $mu. This object is used mainly in SpinorReplace to define replacement rules."
SpinorAngleBracket::usage="SpinorAngleBracket[p,q] is the spinor invariant \[LeftAngleBracket]p q\[RightAngleBracket]. SPinorAngleBracket is linear with respect to momenta which are members of MomList."
SpinorSquareBracket::usage="SpinorSquareBracket[p,q] is the spinor invariant [p q]. SpinorSquareBracket is linear with respect to momenta which are members of MomList."
Chain::usage="Chain[type1,p1,{p2,...,p3},p4,type2] represents a chain of contracted spinors. The two labels type1,type2 take values $angle/$square specifying the type of chain. For example Chain[$angle,p1,{p2},p3,$square]=\[LeftAngleBracket]p1 {p2} p3]."
Mass::usage="Mass[i] is the mass squared of the i'th particle."
LeviCivitaSH::usage="LeviCivitaSH[a,b][type] represents the SU(2) Levi-Civita tensor which contracts the spinor indices. type takes values $up or $down."
mp::usage="mp[p,q] represents the scalar product of p and q. mp is linear with respect to declared momenta."
S::usage="S[p,...,q] is the Mandelstam invariant (p+...+q\!\(\*SuperscriptBox[\()\), \(2\)]\). S has attribute Orderless."
NewProcess::usage="NewProcess[] clears all the invariants, the list of defined massless momenta as well as the declared momenta."


(* ::Subsection:: *)
(*Actions on building blocks*)


SetInvariants::usage="SetMp[list] takes as input a list of replacements of the type mp[x,y]->... and allows to fix given scalar products to a desired value."
ClearInvariants::usage="ClearMp[mp[p1,p2],...] clears the definitions of the scalar products given as arguments. If ClearMp is called without arguments all the scalar products are cleared."


(* ::Section:: *)
(*Private context starts here*)


Begin["`Private`"]


(*We define a private variable needed for the package to decide whether to run shortcuts and the palette or not. This is related to the availability of a frontend.*)


frontend=If[TrueQ[$FrontEnd==Null],0,1];


(* ::Section:: *)
(*Label declaration*)


(* ::Subsection::Closed:: *)
(*DeclareMom and UndeclareMom*)


(*MomList={};
Protect[MomList];

(*Define MomReps, a private list of replacements which sends labels p into "p"*)
MomReps={};

DeclareMom[label__]:=(Unprotect[MomList];MomList=DeleteCases[Join[MomList,Flatten[{label}]]//DeleteDuplicates,_?NumberQ]//Sort;MomReps=Table[i->ToString[i],{i,MomList}];Protect[MomList];);

UndeclareMom[label__]:=(Unprotect[MomList];MomList=DeleteCases[MomList,x_/;MemberQ[Flatten[{label}],x]];MomReps=Table[i->ToString[i],{i,MomList}]; Protect[MomList];);
UndeclareMom[]:=(Unprotect[MomList];MomList={};MomReps={}; Protect[MomList];);
(*Protect the function definitions*)
Protect[DeclareMom,UndeclareMom];*)


MomList={};

(*Define MomReps, a private list of replacements which sends labels p into "p"*)
MomReps={};

DeclareMom[label__]:=(MomList=DeleteCases[Join[MomList,Flatten[{label}]]//DeleteDuplicates,_?NumberQ]//Sort;MomReps=Table[i->ToString[i],{i,MomList}];MomList);
DeclareMom[]:=(MomList);

UndeclareMom[label__]:=(MomList=DeleteCases[MomList,x_/;MemberQ[Flatten[{label}],x]];MomReps=Table[i->ToString[i],{i,MomList}];MomList);
UndeclareMom[]:=(MomList={};MomReps={};MomList);
(*Protect the function definitions*)
Protect[DeclareMom,UndeclareMom];


(* ::Subsection:: *)
(*DeclareMassless and UndeclareMassless*)


(*MasslessMomenta={};
Protect[MasslessMomenta];

DeclareMassless[moms__]:=Module[{x},
x=Flatten[{moms}];
Unprotect[Extramass,Extramasstilde,MasslessMomenta,mp];
Do[Extramass[i]=0;Extramasstilde[i]=0;SetMp[mp[i,i]->0],{i,x}];
MasslessMomenta={MasslessMomenta,x}//Flatten//DeleteDuplicates//Sort;
Protect[Extramass,Extramasstilde,MasslessMomenta,mp];
];

Protect[DeclareMassless];*)


(*MasslessMomenta={};

DeclareMassless[moms__]:=Module[{x},
x=Flatten[{moms}];
Unprotect[Mass];
MasslessMomenta={MasslessMomenta,x}//Flatten//DeleteDuplicates//Sort;
Do[Mass[i]=0;SetInvariants[mp[i,i]->0],{i,x}];
(*Declare also as momentum labels*)
DeclareMom[x];
Protect[Mass];
Return[MasslessMomenta];
];

DeclareMassless[]:=(MasslessMomenta);*)


(*UndeclareMassless[moms___]:=Module[{x},
x=Flatten[{moms}];
Unprotect[Mass];
If[Length[x]===0,
x=DeclareMassless[];
];
Do[
If[MemberQ[MasslessMomenta,i],
Mass[i]=.;
ClearInvariants[mp[i]];
];
,{i,x}];
Protect[Mass];
MasslessMomenta=DeleteCases[MasslessMomenta,y_/;MemberQ[x,y]];
Return[MasslessMomenta];
];*)


(*The list MasslessMomentaAll contains also a string version of each of the massless momenta. This is needed for MasslessQ in SpinorHelicity4D because declared momenta get automatically replaced by strings*)
MasslessMomenta={};
MasslessMomentaAll={};

DeclareMassless[moms__]:=Module[{x},
x=Flatten[{moms}];
Unprotect[Mass];
MasslessMomenta={MasslessMomenta,x}//Flatten//DeleteDuplicates//Sort;
Do[Mass[i]=0;SetInvariants[mp[i,i]->0],{i,x}];
(*Declare also as momentum labels*)
DeclareMom[x];
MasslessMomentaAll=Join[MasslessMomenta,ToString/@MasslessMomenta];
Protect[Mass];
Return[MasslessMomenta];
];

DeclareMassless[]:=(MasslessMomenta);


UndeclareMassless[moms___]:=Module[{x},
x=Flatten[{moms}];
Unprotect[Mass];
If[Length[x]===0,
x=DeclareMassless[];
];
Do[
If[MemberQ[MasslessMomenta,i],
Mass[i]=.;
ClearInvariants[mp[i]];
];
,{i,x}];
Protect[Mass];
MasslessMomenta=DeleteCases[MasslessMomenta,y_/;MemberQ[x,y]];
MasslessMomentaAll=Join[MasslessMomenta,ToString/@MasslessMomenta];
Return[MasslessMomenta];
];


(* ::Section:: *)
(*Auxiliary functions*)


(* ::Subsection::Closed:: *)
(*obar*)


(*Linearity with respect to declared momenta*)
obar[x_+a_.*y_String]:=obar[x]+a*obar[y];
obar[a_*x_String]:=a*obar[x];
obar[x_]/;AnyTrue[MomList,!FreeQ[x,#]&]:=obar[x/.MomReps];

(*Visualisation*)
obarBox[x_]:=TemplateBox[{x},"obar",
DisplayFunction->(OverscriptBox[#,"_"]&),
InterpretationFunction->(RowBox[{"obar","[",#,"]"}]&)
];

obar /: MakeBoxes[obar[x_],StandardForm|TraditionalForm]:=obarBox[ToBoxes[x]];

Protect[obar];


(* ::Subsection::Closed:: *)
(*obarQ*)


(*Test if a function is an obar, private function not available to the user*)
obarQ[x_]:=TrueQ[Head[x]==obar];


(* ::Subsection::Closed:: *)
(*$Shortcuts*)


If[frontend==1,
$Shortcuts={RawBoxes[RowBox[{SuperscriptBox["\[Lambda]","\[Alpha]"],"[p]"}]] -> "esc + lu + esc",
			RawBoxes[RowBox[{SubscriptBox["\[Lambda]","\[Alpha]"],"[p]"}]] -> "esc + ld + esc",
			RawBoxes[RowBox[{SuperscriptBox[OverscriptBox["\[Lambda]","~"],"\[Alpha]"],"[p]"}]] -> "esc + ltu + esc",
			RawBoxes[RowBox[{SubscriptBox[OverscriptBox["\[Lambda]","~"],"\[Alpha]"],"[p]"}]] -> "esc + ltd + esc",
			RawBoxes[RowBox[{SuperscriptBox["\[Mu]","\[Alpha]"],"[p]"}]] -> "esc + muu + esc",
			RawBoxes[RowBox[{SubscriptBox["\[Mu]","\[Alpha]"],"[p]"}]] -> "esc + mud + esc",
			RawBoxes[RowBox[{SuperscriptBox[OverscriptBox["\[Mu]","~"],"\[Alpha]"],"[p]"}]] -> "esc + mtu + esc",
			RawBoxes[RowBox[{SubscriptBox[OverscriptBox["\[Mu]","~"],"\[Alpha]"],"[p]"}]] -> "esc + mtd + esc",
			RawBoxes[RowBox[{"\[Lambda][p]"}]]-> "esc + lp + esc",
			RawBoxes[RowBox[{"\[Mu][p]"}]]-> "esc + mp + esc",
			RawBoxes[RowBox[{OverscriptBox["\[Lambda]","~"],"[p]"}]]-> "esc + ltp + esc",
			RawBoxes[RowBox[{OverscriptBox["\[Mu]","~"],"[p]"}]]-> "esc + mtp + esc",
			RawBoxes[SuperscriptBox["\[Epsilon]",RowBox[{"a","b"}]]]->"esc + lcup + esc",
			RawBoxes[SubscriptBox["\[Epsilon]",RowBox[{"a","b"}]]]->"esc + lcd + esc",
			RawBoxes[RowBox[{"\[LeftAngleBracket]",RowBox[{"p  q"}],"\[RightAngleBracket]"}]] -> "esc + ab + esc",
			RawBoxes[RowBox[{"[",RowBox[{"p  q"}],"]"}]]-> "esc + sb + esc",
RawBoxes[RowBox[{"\[LeftAngleBracket]",RowBox[{"p q k"}],"]"}]]-> "esc + cas + esc",
RawBoxes[RowBox[{"[",RowBox[{"p q k"}],"\[RightAngleBracket]"}]]-> "esc + csa + esc",RawBoxes[RowBox[{"\[LeftAngleBracket]",RowBox[{"p q k l"}],"\[RightAngleBracket]"}]]-> "esc + caa + esc",
RawBoxes[RowBox[{"[",RowBox[{"p q k l"}],"]"}]]-> "esc + css + esc"}//MatrixForm;
			];


(* ::Subsection::Closed:: *)
(*ClearDownValues*)


(*Private function used to clear the downvalues of a given function*)
ClearDownValues[f_]:=DownValues[f]=DeleteCases[DownValues[f],_?(FreeQ[First[#],Pattern]&)];


(* ::Section:: *)
(*Building blocks*)


(* ::Subsection::Closed:: *)
(*SpinorUndot*)


(*Define all the boxing functions for the different cases, \[Lambda], \[Mu] with both up and down indices*)
SpinorLaUpBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorLaUp",
DisplayFunction->(RowBox[{SuperscriptBox["\[Lambda]",#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorUndot","[",#1,"]","[","$lam","]","[",#2,"]","[","Null","]"}]&)
];
SpinorLaDownBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorLaDown",
DisplayFunction->(RowBox[{SubscriptBox["\[Lambda]",#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorUndot","[",#1,"]","[","$lam","]","[","Null","]","[",#2,"]"}]&)
];
SpinorMuUpBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorMuUp",
DisplayFunction->(RowBox[{SuperscriptBox["\[Mu]",#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorUndot","[",#1,"]","[","$mu","]","[",#2,"]","[","Null","]"}]&)
];
SpinorMuDownBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorMuDown",
DisplayFunction->(RowBox[{SubscriptBox["\[Mu]",#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorUndot","[",#1,"]","[","$mu","]","[","Null","]","[",#2,"]"}]&)
];


(*Define the action of Makeboxes on our functions*)
SpinorUndot /: MakeBoxes[SpinorUndot[mom_][$lam][upper_][Null],StandardForm|TraditionalForm]:=SpinorLaUpBox[ToBoxes[mom],ToBoxes[upper]];
SpinorUndot /: MakeBoxes[SpinorUndot[mom_][$mu][upper_][Null],StandardForm|TraditionalForm]:=SpinorMuUpBox[ToBoxes[mom],ToBoxes[upper]];
SpinorUndot /: MakeBoxes[SpinorUndot[mom_][$lam][Null][lower_],StandardForm|TraditionalForm]:=SpinorLaDownBox[ToBoxes[mom],ToBoxes[lower]];
SpinorUndot /: MakeBoxes[SpinorUndot[mom_][$mu][Null][lower_],StandardForm|TraditionalForm]:=SpinorMuDownBox[ToBoxes[mom],ToBoxes[lower]];


(*Define all the shortcuts*)
If[frontend==1,
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "lu" -> SpinorLaUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "ld" -> SpinorLaDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "muu" -> SpinorMuUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "mud" -> SpinorMuDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
];


(*Finally define the contraction properties of the Undotted spinors among themselves when repeated indices are encoutered:*)
SpinorUndot /: Times[SpinorUndot[a_][$mu][d_][Null],SpinorUndot[b_][$mu][Null][d_]]:=SpinorAngleBracket[OverBar[a],OverBar[b]];
SpinorUndot /: Times[SpinorUndot[a_][$lam][d_][Null],SpinorUndot[b_][$mu][Null][d_]]:=SpinorAngleBracket[a,OverBar[b]];
SpinorUndot /: Times[SpinorUndot[a_][$mu][d_][Null],SpinorUndot[b_][$lam][Null][d_]]:=SpinorAngleBracket[OverBar[a],b];
SpinorUndot /: Times[SpinorUndot[a_][$lam][d_][Null],SpinorUndot[b_][$lam][Null][d_]]:=SpinorAngleBracket[a,b];
SpinorUndot /: Times[LeviCivitaSH[a_,b_][$down],SpinorUndot[mom_][type_][b_][Null]]:=SpinorUndot[mom][type][Null][a];
SpinorUndot /: Times[LeviCivitaSH[a_,b_][$down],SpinorUndot[mom_][type_][a_][Null]]:=-SpinorUndot[mom][type][Null][b];
SpinorUndot /: Times[LeviCivitaSH[a_,b_][$up],SpinorUndot[mom_][type_][Null][b_]]:=SpinorUndot[mom][type][a][Null];
SpinorUndot /: Times[LeviCivitaSH[a_,b_][$up],SpinorUndot[mom_][type_][Null][a_]]:=-SpinorUndot[mom][type][b][Null];


(*Define the properties with respect to declared momenta*)
SpinorUndot[momlabel_][type_][upper_][lower_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=SpinorUndot[momlabel/.MomReps][type][upper][lower];
SpinorUndot[x_+a_.*momlabel_String][type_][upper_][lower_]:=SpinorUndot[x][type][upper][lower]+SpinorUndot[a*momlabel][type][upper][lower];
SpinorUndot[Times[int_?Negative,a1___,momlabel_String,a2___]][type_][upper_][lower_]:=I*(-int)SpinorUndot[a1*momlabel*a2][type][upper][lower];
SpinorUndot[a_*momlabel_String][type_][upper_][lower_]:=a*SpinorUndot[momlabel][type][upper][lower];


(* ::Subsection::Closed:: *)
(*SpinorUndotBare*)


SpinorUndotBareLBox[label_]:=TemplateBox[{label},"SpinorUndotBareL",
DisplayFunction->(RowBox[{"\[Lambda]","[",#,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorUndotBare","[",#,"]","[","$lam","]"}]&)
];
SpinorUndotBareMBox[label_]:=TemplateBox[{label},"SpinorUndotBareM",
DisplayFunction->(RowBox[{"\[Mu]","[",#,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorUndotBare","[",#,"]","[","$mu","]"}]&)
];

SpinorUndotBare /: MakeBoxes[SpinorUndotBare[label_][$lam],TraditionalForm|StandardForm]:=SpinorUndotBareLBox[ToBoxes[label]];
SpinorUndotBare /: MakeBoxes[SpinorUndotBare[label_][$mu],TraditionalForm|StandardForm]:=SpinorUndotBareMBox[ToBoxes[label]];

If[frontend==1,
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "lp" -> SpinorUndotBareLBox["\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "mp" -> SpinorUndotBareMBox["\[SelectionPlaceholder]"]]];
];

(*Define the properties with respect to declared momenta*)
SpinorUndotBare[momlabel_][type_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=SpinorUndotBare[momlabel/.MomReps][type];
SpinorUndotBare[x_+a_.*momlabel_String][type_]:=SpinorUndotBare[x][type]+SpinorUndotBare[a*momlabel][type];
SpinorUndotBare[Times[int_?Negative,a1___,momlabel_String,a2___]][type_]:=I*(-int)SpinorUndotBare[a1*momlabel*a2][type];
SpinorUndotBare[a_*momlabel_String][type_]:=a*SpinorUndotBare[momlabel][type];

(*Define that an obar in the momentum label becomes a $mu*)
SpinorUndotBare[obar[x_]][$lam]:=SpinorUndotBare[x][$mu];
SpinorUndotBare[obar[x_]][$mu]:=SpinorUndotBare[x][$mu];


(* ::Subsection::Closed:: *)
(*SpinorDot*)


(*For an explaination of the following functions see the section SpinorUndot, these work just in the same way*)
SpinorLatUpBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorLatUp",
DisplayFunction->(RowBox[{SuperscriptBox[OverscriptBox["\[Lambda]","~"],#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorDot","[",#1,"]","[","$lam","]","[",#2,"]","[","Null","]"}]&)
];
SpinorLatDownBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorLatDown",
DisplayFunction->(RowBox[{SubscriptBox[OverscriptBox["\[Lambda]","~"],#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorDot","[",#1,"]","[","$lam","]","[","Null","]","[",#2,"]"}]&)
];
SpinorMutUpBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorMutUp",
DisplayFunction->(RowBox[{SuperscriptBox[OverscriptBox["\[Mu]","~"],#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorDot","[",#1,"]","[","$mu","]","[",#2,"]","[","Null","]"}]&)
];
SpinorMutDownBox[mom_,index_]:=TemplateBox[{mom,index},"SpinorMutDown",
DisplayFunction->(RowBox[{SubscriptBox[OverscriptBox["\[Mu]","~"],#2],"[",#1,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorDot","[",#1,"]","[","$mu","]","[","Null","]","[",#2,"]"}]&)
];


SpinorDot /: MakeBoxes[SpinorDot[mom_][$lam][upper_][Null],StandardForm|TraditionalForm]:=SpinorLatUpBox[ToBoxes[mom],ToBoxes[upper]];
SpinorDot /: MakeBoxes[SpinorDot[mom_][$mu][upper_][Null],StandardForm|TraditionalForm]:=SpinorMutUpBox[ToBoxes[mom],ToBoxes[upper]];
SpinorDot /: MakeBoxes[SpinorDot[mom_][$lam][Null][lower_],StandardForm|TraditionalForm]:=SpinorLatDownBox[ToBoxes[mom],ToBoxes[lower]];
SpinorDot /: MakeBoxes[SpinorDot[mom_][$mu][Null][lower_],StandardForm|TraditionalForm]:=SpinorMutDownBox[ToBoxes[mom],ToBoxes[lower]];


If[frontend==1,
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "ltu" -> SpinorLatUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "ltd" -> SpinorLatDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "mtu" -> SpinorMutUpBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "mtd" -> SpinorMutDownBox["\[SelectionPlaceholder]","\[SelectionPlaceholder]"]]];
];


(*Finally define the contraction properties of the Undotted spinors among themselves when repeated indices are encoutered:*)
SpinorDot /: Times[SpinorDot[a_][$mu][d_][Null],SpinorDot[b_][$mu][Null][d_]]:=SpinorSquareBracket[OverBar[b],OverBar[a]];
SpinorDot /: Times[SpinorDot[a_][$lam][d_][Null],SpinorDot[b_][$mu][Null][d_]]:=SpinorSquareBracket[OverBar[b],a];
SpinorDot /: Times[SpinorDot[a_][$mu][d_][Null],SpinorDot[b_][$lam][Null][d_]]:=SpinorSquareBracket[b,OverBar[a]];
SpinorDot /: Times[SpinorDot[a_][$lam][d_][Null],SpinorDot[b_][$lam][Null][d_]]:=SpinorSquareBracket[b,a];
SpinorDot /: Times[LeviCivitaSH[a_,b_][$down],SpinorDot[mom_][type_][b_][Null]]:=SpinorDot[mom][type][Null][a];
SpinorDot /: Times[LeviCivitaSH[a_,b_][$down],SpinorDot[mom_][type_][a_][Null]]:=-SpinorDot[mom][type][Null][b];
SpinorDot /: Times[LeviCivitaSH[a_,b_][$up],SpinorDot[mom_][type_][Null][b_]]:=SpinorDot[mom][type][a][Null];
SpinorDot /: Times[LeviCivitaSH[a_,b_][$up],SpinorDot[mom_][type_][Null][a_]]:=-SpinorDot[mom][type][b][Null];


(*Define the properties with respect to declared momenta*)
SpinorDot[momlabel_][type_][upper_][lower_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=SpinorDot[momlabel/.MomReps][type][upper][lower];
SpinorDot[x_+a_.*momlabel_String][type_][upper_][lower_]:=SpinorDot[x][type][upper][lower]+SpinorDot[a*momlabel][type][upper][lower];
SpinorDot[Times[int_?Negative,a1___,momlabel_String,a2___]][type_][upper_][lower_]:=I*(-int)*SpinorDot[a1*momlabel*a2][type][upper][lower];
SpinorDot[a_*momlabel_String][type_][upper_][lower_]:=a*SpinorDot[momlabel][type][upper][lower];


(* ::Subsection::Closed:: *)
(*SpinorDotBare*)


SpinorDotBareLBox[label_]:=TemplateBox[{label},"SpinorDotBareL",
DisplayFunction->(RowBox[{OverscriptBox["\[Lambda]","~"],"[",#,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorDotBare","[",#,"]","[","$lam","]"}]&)
];
SpinorDotBareMBox[label_]:=TemplateBox[{label},"SpinorDotBareM",
DisplayFunction->(RowBox[{OverscriptBox["\[Mu]","~"],"[",#,"]"}]&),
InterpretationFunction->(RowBox[{"SpinorDotBare","[",#,"]","[","$mu","]"}]&)
];

SpinorDotBare /: MakeBoxes[SpinorDotBare[label_][$lam],TraditionalForm|StandardForm]:=SpinorDotBareLBox[ToBoxes[label]];
SpinorDotBare /: MakeBoxes[SpinorDotBare[label_][$mu],TraditionalForm|StandardForm]:=SpinorDotBareMBox[ToBoxes[label]];

If[frontend==1,
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "ltp" -> SpinorDotBareLBox["\[SelectionPlaceholder]"]]];
SetOptions[EvaluationNotebook[],InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "mtp" -> SpinorDotBareMBox["\[SelectionPlaceholder]"]]];
];

(*Define the properties with respect to declared momenta*)
SpinorDotBare[momlabel_][type_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=SpinorDotBare[momlabel/.MomReps][type];
SpinorDotBare[x_+a_.*momlabel_String][type_]:=SpinorDotBare[x][type]+SpinorDotBare[a*momlabel][type];
SpinorDotBare[Times[int_?Negative,a1___,momlabel_String,a2___]][type_]:=I*(-int)SpinorDotBare[a1*momlabel*a2][type];
SpinorDotBare[a_*momlabel_String][type_]:=a*SpinorDotBare[momlabel][type];

(*Define that an obar in the momentum label becomes a $mu*)
SpinorDotBare[obar[x_]][$lam]:=SpinorDotBare[x][$mu];
SpinorDotBare[obar[x_]][$mu]:=SpinorDotBare[x][$mu];


(* ::Subsection::Closed:: *)
(*SpinorAngleBracket*)


(*Antisymmetry*)
SpinorAngleBracket[a_, b_] /; (a == b) := 0
SpinorAngleBracket[a_, b_] /; \[Not]OrderedQ[{a,b}] := -SpinorAngleBracket[b, a];

(*Visualisation*)
SpinorAngleBracketBox[a_, b_] :=
    TemplateBox[{a, b}, "SpinorAngleBracket",
        DisplayFunction -> (RowBox[{"\[LeftAngleBracket]",RowBox[{#1,"\[MediumSpace]",#2}],"\[RightAngleBracket]"}]&),
        InterpretationFunction -> (RowBox[{"SpinorAngleBracket","[",RowBox[{#1,",",#2}],"]"}]&)]

SpinorAngleBracket /: MakeBoxes[SpinorAngleBracket[a_, b_], StandardForm | TraditionalForm] := SpinorAngleBracketBox[ToBoxes[a], ToBoxes[b]];

(*Linearity with repsect to declared momenta and obar*)
SpinorAngleBracket[x_,y_]/;AnyTrue[MomList,!FreeQ[x|y,#]&]:=SpinorAngleBracket[x/.MomReps,y/.MomReps];

SpinorAngleBracket[x_+a_.*momlabel_String,y_]:=SpinorAngleBracket[x,y]+SpinorAngleBracket[a*momlabel,y];
SpinorAngleBracket[Times[int_?Negative,a1___,momlabel_String,a2___],y_]:=I*(-int)*SpinorAngleBracket[a1*momlabel*a2,y];
SpinorAngleBracket[a_*momlabel_String,y_]:=a*SpinorAngleBracket[momlabel,y];

SpinorAngleBracket[y_,x_+a_.*momlabel_String]:=SpinorAngleBracket[y,x]+SpinorAngleBracket[y,a*momlabel];
SpinorAngleBracket[y_,Times[int_?Negative,a1___,momlabel_String,a2___]]:=I*(-int)*SpinorAngleBracket[y,a1*momlabel*a2];
SpinorAngleBracket[y_,a_*momlabel_String]:=a*SpinorAngleBracket[y,momlabel];

SpinorAngleBracket[x_+a_.*momlabel_?obarQ,y_]:=SpinorAngleBracket[x,y]+SpinorAngleBracket[a*momlabel,y];
SpinorAngleBracket[Times[int_?Negative,a1___,momlabel_?obarQ,a2___],y_]:=I*(-int)*SpinorAngleBracket[a1*momlabel*a2,y];
SpinorAngleBracket[a_*momlabel_?obarQ,y_]:=a*SpinorAngleBracket[momlabel,y];

SpinorAngleBracket[y_,x_+a_.*momlabel_?obarQ]:=SpinorAngleBracket[y,x]+SpinorAngleBracket[y,a*momlabel];
SpinorAngleBracket[y_,Times[int_?Negative,a1___,momlabel_?obarQ,a2___]]:=I*(-int)*SpinorAngleBracket[y,a1*momlabel*a2];
SpinorAngleBracket[y_,a_*momlabel_?obarQ]:=a*SpinorAngleBracket[y,momlabel];

(*Shortcut definition*)
If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "ab" -> SpinorAngleBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]];
    ];


(* ::Subsection::Closed:: *)
(*SpinorSquareBracket*)


SpinorSquareBracket[a_, b_] /; (a == b) := 0
SpinorSquareBracket[a_, b_] /; \[Not]OrderedQ[{a, b}] := -SpinorSquareBracket[b, a]

SpinorSquareBracketBox[a_, b_] :=
    TemplateBox[{a, b}, "SpinorSquareBracket",
        DisplayFunction -> (RowBox[{"[",RowBox[{#1,"\[MediumSpace]",#2}],"]"}]&),
        InterpretationFunction -> (RowBox[{"SpinorSquareBracket","[",RowBox[{#1,",",#2}],"]"}]&)]

SpinorSquareBracket /: MakeBoxes[SpinorSquareBracket[a_, b_], StandardForm | TraditionalForm] := SpinorSquareBracketBox[ToBoxes[a], ToBoxes[b]]

(*Linearity with repsect to declared momenta and obar*)
SpinorSquareBracket[x_,y_]/;AnyTrue[MomList,!FreeQ[x|y,#]&]:=SpinorSquareBracket[x/.MomReps,y/.MomReps];

SpinorSquareBracket[x_+a_.*momlabel_String,y_]:=SpinorSquareBracket[x,y]+SpinorSquareBracket[a*momlabel,y];
SpinorSquareBracket[Times[int_?Negative,a1___,momlabel_String,a2___],y_]:=I*(-int)*SpinorSquareBracket[a1*momlabel*a2,y];
SpinorSquareBracket[a_*momlabel_String,y_]:=a*SpinorSquareBracket[momlabel,y];

SpinorSquareBracket[y_,x_+a_.*momlabel_String]:=SpinorSquareBracket[y,x]+SpinorSquareBracket[y,a*momlabel];
SpinorSquareBracket[y_,Times[int_?Negative,a1___,momlabel_String,a2___]]:=I*(-int)*SpinorSquareBracket[y,a1*momlabel*a2];
SpinorSquareBracket[y_,a_*momlabel_String]:=a*SpinorSquareBracket[y,momlabel];

SpinorSquareBracket[x_+a_.*momlabel_?obarQ,y_]:=SpinorSquareBracket[x,y]+SpinorSquareBracket[a*momlabel,y];
SpinorSquareBracket[Times[int_?Negative,a1___,momlabel_?obarQ,a2___],y_]:=I*(-int)*SpinorSquareBracket[a1*momlabel*a2,y];
SpinorSquareBracket[a_*momlabel_?obarQ,y_]:=a*SpinorSquareBracket[momlabel,y];

SpinorSquareBracket[y_,x_+a_.*momlabel_?obarQ]:=SpinorSquareBracket[y,x]+SpinorSquareBracket[y,a*momlabel];
SpinorSquareBracket[y_,Times[int_?Negative,a1___,momlabel_?obarQ,a2___]]:=I*(-int)*SpinorSquareBracket[y,a1*momlabel*a2];
SpinorSquareBracket[y_,a_*momlabel_?obarQ]:=a*SpinorSquareBracket[y,momlabel];

If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "sb" -> SpinorSquareBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]];
    ];


(* ::Subsection::Closed:: *)
(*Chain*)


(*Display of the chains*)
AngleSquareChainBox[beginning_,args_,end_]:=TemplateBox[{beginning,args,end},"AngleSquareChain",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,#2,#3,"]"}]&),
InterpretationFunction->(RowBox[{"Chain","[","$angle",",",#1,",",#2,",",#3,",","$square","]"}]&)
];
SquareAngleChainBox[beginning_,args_,end_]:=TemplateBox[{beginning,args,end},"SquareAngleChain",
DisplayFunction->(RowBox[{"[",#1,#2,#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"Chain","[","$square",",",#1,",",#2,",",#3,",","$angle","]"}]&)
];
AngleAngleChainBox[beginning_,args_,end_]:=TemplateBox[{beginning,args,end},"AngleAngleChain",
DisplayFunction->(RowBox[{"\[LeftAngleBracket]",#1,#2,#3,"\[RightAngleBracket]"}]&),
InterpretationFunction->(RowBox[{"Chain","[","$angle",",",#1,",",#2,",",#3,",","$angle","]"}]&)
];
SquareSquareChainBox[beginning_,args_,end_]:=TemplateBox[{beginning,args,end},"SquareSquareChain",
DisplayFunction->(RowBox[{"[",#1,#2,#3,"]"}]&),
InterpretationFunction->(RowBox[{"Chain","[","$square",",",#1,",",#2,",",#3,",","$square","]"}]&)
];
Chain /: MakeBoxes[Chain[$angle,x_,y_List,z_,$square],StandardForm|TraditionalForm] /;OddQ[Length[y]+2]:=AngleSquareChainBox[ToBoxes[x],ToBoxes[y],ToBoxes[z]];
Chain /: MakeBoxes[Chain[$angle,x_,y_List,z_,$angle],StandardForm|TraditionalForm] /;EvenQ[Length[y]+2]:=AngleAngleChainBox[ToBoxes[x],ToBoxes[y],ToBoxes[z]];
Chain /: MakeBoxes[Chain[$square,x_,y_List,z_,$angle],StandardForm|TraditionalForm] /;OddQ[Length[y]+2]:=SquareAngleChainBox[ToBoxes[x],ToBoxes[y],ToBoxes[z]];
Chain /: MakeBoxes[Chain[$square,x_,y_List,z_,$square],StandardForm|TraditionalForm] /;EvenQ[Length[y]+2]:=SquareSquareChainBox[ToBoxes[x],ToBoxes[y],ToBoxes[z]];

(*Shortcuts*)

If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "cas" -> AngleSquareChainBox[ToBoxes[\[SelectionPlaceholder]],ToBoxes[{\[SelectionPlaceholder]}],ToBoxes[\[SelectionPlaceholder]]]]];
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "csa" -> SquareAngleChainBox[ToBoxes[\[SelectionPlaceholder]],ToBoxes[{\[SelectionPlaceholder]}],ToBoxes[\[SelectionPlaceholder]]]]];
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "caa" -> AngleAngleChainBox[ToBoxes[\[SelectionPlaceholder]],ToBoxes[{\[SelectionPlaceholder]}],ToBoxes[\[SelectionPlaceholder]]]]];
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "css" -> SquareSquareChainBox[ToBoxes[\[SelectionPlaceholder]],ToBoxes[{\[SelectionPlaceholder]}],ToBoxes[\[SelectionPlaceholder]]]]];
 ];

(*Linearity properties with respect to declared momenta*)

Chain[momlabel__]/;AnyTrue[MomList,!FreeQ[{momlabel},#]&]:=Chain[Sequence@@({momlabel}/.MomReps)];
Chain[type1_,p1_+a_.*momlabel_String,{p2__},p3_,type2_]:=Chain[type1,p1,{p2},p3,type2]+Chain[type1,a*momlabel,{p2},p3,type2];
Chain[type1_,Times[int_?Negative,a1___,momlabel_String,a2___],{p2__},p3_,type2_]:=I*(-int)*Chain[type1,a1*momlabel*a2,{p2},p3,type2];
Chain[type1_,a_*momlabel_String,{p2__},p3_,type2_]:=a*Chain[type1,momlabel,{p2},p3,type2];
Chain[type1_,p1_,{p2__},p3_+a_.*momlabel_String,type2_]:=Chain[type1,p1,{p2},p3,type2]+Chain[type1,p1,{p2},a*momlabel,type2];
Chain[type1_,p1_,{p2__},Times[int_?Negative,a1___,momlabel_String,a2___],type2_]:=I*(-int)*Chain[type1,p1,{p2},a1*momlabel*a2,type2];
Chain[type1_,p1_,{p2__},a_*momlabel_String,type2_]:=a*Chain[type1,p1,{p2},momlabel,type2];
Chain[type1_,p1_,{x___,p2_+a_. momlabel_String,y___},p3_,type2_]:=Chain[type1,p1,{x,p2,y},p3,type2]+a*Chain[type1,p1,{x,momlabel,y},p3,type2];
Chain[type1_,p1_,{x___,a_*momlabel_String,y___},p3_,type2_]:=a*Chain[type1,p1,{x,momlabel,y},p3,type2];


(* ::Subsection::Closed:: *)
(*LeviCivitaSH*)


(*Tensor with upper indices*)
LevicivitaSHBoxUp[a_,b_]:=TemplateBox[{a,b},"LevicivitaSHUp",
DisplayFunction->(SuperscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),
InterpretationFunction->(RowBox[{"LeviCivitaSH","[",#1,",",#2,"]","[","$up","]"}]&)
];

LeviCivitaSH /: MakeBoxes[LeviCivitaSH[a_,b_][$up],TraditionalForm|StandardForm]:=LevicivitaSHBoxUp[ToBoxes[a],ToBoxes[b]];

(*Tensor with lower indices*)
LevicivitaSHBoxDown[a_,b_]:=TemplateBox[{a,b},"LevicivitaSHDown",
DisplayFunction->(SubscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),
InterpretationFunction->(RowBox[{"LeviCivitaSH","[",#1,",",#2,"]","[","$down","]"}]&)
];

LeviCivitaSH /: MakeBoxes[LeviCivitaSH[a_,b_][$down],TraditionalForm|StandardForm]:=LevicivitaSHBoxDown[ToBoxes[a],ToBoxes[b]];

(*Properties*)
LeviCivitaSH[a_, b_][_] /; (a == b) := 0;
LeviCivitaSH[a_, b_] [type_]/; OrderedQ[{b,a}] := -LeviCivitaSH[b, a][type];
LeviCivitaSH[a_Integer,b_Integer][_]:=LeviCivitaTensor[2][[a,b]];

(*Shortcut definition*)
If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "lcup" -> LevicivitaSHBoxUp[ToBoxes[\[SelectionPlaceholder]],ToBoxes[\[SelectionPlaceholder]]]]];
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates@Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "lcd" -> LevicivitaSHBoxDown[ToBoxes[\[SelectionPlaceholder]],ToBoxes[\[SelectionPlaceholder]]]]];

    ];


(* ::Subsection::Closed:: *)
(*Scalar product*)


(*Display*)
mpBox[x_,y_]:=TemplateBox[{x,y},"ScalarProduct",
DisplayFunction->(RowBox[{"(",#1,"\[CenterDot]",#2,")"}]&),
InterpretationFunction->(RowBox[{"mp","[",#1,",",#2,"]"}]&)];

(*Different display when the two momenta are equal*)

mpBox[x_,x_]:=TemplateBox[{x},"ScalarProduct2",
DisplayFunction->(SuperscriptBox[RowBox[{"(",#1,")"}],"2"]&),
InterpretationFunction->(RowBox[{"mp","[",#1,",",#1,"]"}]&)];

mp /: MakeBoxes[mp[x_,y_],StandardForm|TraditionalForm]:=mpBox[ToBoxes[x],ToBoxes[y]];

(*In order to make it more user friendly we define the function in such a way that it automatically adds the MomPure to its argument if it is not already in that format.*)
mp[x_]:=mp[x,x];

(*Linearity in declared momenta*)
SetAttributes[mp,Orderless];
mp[momlabel_,y_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=mp[momlabel/.MomReps,y];
mp[x_+a_. momlabel_String,y_]:=mp[x,y]+a*mp[momlabel,y];
mp[a_*momlabel_String,y_]:=a*mp[momlabel,y];


(* ::Subsection::Closed:: *)
(*Mandelstam invariants*)


(*Just implement the orderlessness of the Mandelstam invariants*)
SetAttributes[S,Orderless];


(* ::Section:: *)
(*Actions on building blocks*)


(* ::Subsection::Closed:: *)
(*SetInvariants*)


FixedInvariants={};

SetAttributes[SetInvariants,HoldAll];


SetInvariants[x__]:=Module[{loclist,new},
(*First inactivate mp in order to avoid undesired evaluations of already defined scalar products*)
loclist=Flatten[Inactivate[Inactivate[{x},mp],S]];
(*Delete the instances where mp does not appear, for any reason*)
loclist=DeleteCases[loclist,y_/;FreeQ[y,mp]&&FreeQ[y,S]];
(*Bring mp[i] into suitable form*)
loclist=loclist/.{Inactive[mp][a_]:>Inactive[mp][a,a]};
(*Given an mp[x,y] with x,y massless, set also the S[x,y] to 2*mp[x,y]*)
(*Rules to list for easier manipulation*)
loclist=loclist/.{Rule->List,RuleDelayed->List,Equal->List};
(*If first member of list is mp[x,y] massless add setting for S[x,y]*)
loclist=Join[loclist,Cases[loclist,{z_,y_}/;MatchQ[z,Inactive[mp][a_,b_]/;MemberQ[MasslessMomenta,a]&&MemberQ[MasslessMomenta,b]]:>{(z/.mp->S),2*y}]];
(*Do it the opposite way around also for S and delete duplicates*)
loclist=DeleteDuplicates[Join[loclist,Cases[loclist,{z_,y_}/;MatchQ[z,Inactive[S][a_,b_]/;MemberQ[MasslessMomenta,a]&&MemberQ[MasslessMomenta,b]]:>{(z/.S->mp),1/2*y}]]];
loclist=(RuleDelayed@@@loclist)/.{Inactive[mp]->"mp",Inactive[S]->"S"};

(*Now actually set the values*)
Unprotect[mp,S];
FixedInvariants=DeleteDuplicatesBy[Join[loclist,FixedInvariants],First];
ClearDownValues[mp];
ClearDownValues[S];
FixedInvariants/.{"mp"->mp,"S"->S}/.RuleDelayed->SetDelayed;
Protect[mp,S];
Return[FixedInvariants//Sort];
];

SetInvariants[]:=(FixedInvariants//Sort);


(* ::Subsection::Closed:: *)
(*ClearInvariants*)


SetAttributes[ClearInvariants,HoldAll];

ClearInvariants[x___]:=Module[{loc,loclist,new},
loclist=Flatten[Inactivate[Inactivate[{x},mp],S]]/.{Inactive[mp]->"mp",Inactive[S]->"S"};
loclist=loclist/.{"mp"[a_]:>"mp"[a,a]};
(*Take into account that for massless particles S and mp are related*)
loclist=Flatten[loclist/.{"mp"[a_,b_]/;MemberQ[MasslessMomenta,a]&&MemberQ[MasslessMomenta,b]:>{"mp"[a,b],"S"[a,b]},"S"[a_,b_]/;MemberQ[MasslessMomenta,a]&&MemberQ[MasslessMomenta,b]:>{"mp"[a,b],"S"[a,b]}}];
Unprotect[mp,S];
ClearDownValues[mp];
ClearDownValues[S];
If[Length[loclist]===0,
(*No argument means clear all*)
	FixedInvariants={},
(*Remove from FixedInvariants the ones to be undeclared*)
FixedInvariants=DeleteCases[FixedInvariants,z_/;MemberQ[loclist,z[[1]]]];
(*Apply remaining definitions*)
FixedInvariants/.{"mp"->mp,"S"->S}/.RuleDelayed->SetDelayed;
];
Protect[mp,S];
Return[FixedInvariants//Sort];
];


(* ::Subsection:: *)
(*NewProcess*)


NewProcess[]:=(ClearInvariants[];UndeclareMassless[];UndeclareMom[];);


(* ::Section:: *)
(*End of context*)


(*End the private context*)
End[]

(*Protect all public symbols in the package*)
Protect@@Names["SpinorBuildingBlocks`*"];

(*End the package*)
EndPackage[]
