(* ::Package:: *)

(* ::Chapter:: *)
(*SpinorBuildingBlocks*)


BeginPackage["SpinorBuildingBlocks`"]


(* ::Section:: *)
(*Function description*)


(* ::Subsection:: *)
(*Label declaration*)


DeclareMom::usage="DeclareMom[p,q,...] adds p,q,... to the list of momenta known to the package. Declaring momenta is not necessary but allows for the use of certain properties (like linearity) of functions like Chain and mp."
UndeclareMom::usage="UndeclareMom[p,q,...] removes p,q,... from the list of known momenta. UndeclareMom[] clears the list of declared momenta."
MomList::usage="MomList is the list containing all the labels which have been declared to be momenta. Names for momenta can be declared through DeclareMom."
DeclareMassless::usage="DeclareMassless[p,q,k,...] adds p,q,k,... to the list of massless momenta."
MasslessMomenta::usage="MasslessMomenta is the list of momenta which have been declared to be massless through DeclareMassless."


(* ::Subsection:: *)
(*Auxiliary functions*)


obar::usage="obar[p] is used inside invariants such as the angle and square brackets when the momentum p has to be interpreted as a reference momentum and thus associated spinors will be of the type \[Mu](p). obar is linear with respect to members of MomList."
$lam::usage="Protected label for the \[Lambda] spinors."
$mu::usage="Protected label for the \[Mu] spinors."


(* ::Subsection:: *)
(*Building blocks*)


SpinorUndot::usage="SpinorUndot[momlabel][type][upper][lower] represents the generic four-dimensional spinor with undotted indices. The type is either $lam for \[Lambda] spinors or $mu for \[Mu] spinors.
The label upper is for the upper spinor index and lower for the lower index, one of them needs to be Null. Explicit usage of this function can be easily avoided through the shortcuts, the palette or a custom definition. For further details see the documentation."
SpinorDot::usage="SpinorDot[momlabel][type][upper][lower] represents the generic four-dimensional spinor with dotted indices. The type is either $lam for \[Lambda] spinors or $mu for \[Mu] spinors.
The label upper is for the upper spinor index and lower for the lower index, one of them needs to be Null. Explicit usage of this function can be easily avoided through the shortcuts, the palette or a custom definition. For further details see the documentation."
SpinorAngleBracket::usage="SpinorAngleBracket[p,q] is the spinor invariant \[LeftAngleBracket]p q\[RightAngleBracket]. SPinorAngleBracket is linear with respect to momenta which are members of MomList."
SpinorSquareBracket::usage="SpinorSquareBracket[p,q] is the spinor invariant [p q]. SpinorSquareBracket is linear with respect to momenta which are members of MomList."


(* ::Section:: *)
(*Private context starts here*)


Begin["`Private`"]


(*We define a private variable needed for the package to decide whether to run shortcuts and the palette or not. This is related to the availability of a frontend.*)


frontend=If[TrueQ[$FrontEnd==Null],0,1];


(* ::Section:: *)
(*Label declaration*)


(* ::Subsection::Closed:: *)
(*MomList, DeclareMom and UndeclareMom*)


MomList={};
Protect[MomList];

(*Define MomReps, a private list of replacements which sends labels p into "p"*)
MomReps={};
Protect[MomReps];

DeclareMom[label__]:=(Unprotect[MomList,MomReps];MomList=Join[MomList,Flatten[{label}]]//DeleteDuplicates;MomReps=Table[i->ToString[i],{i,MomList}];Protect[MomList,MomReps];);

UndeclareMom[label__]:=(Unprotect[MomList,MomReps];MomList=DeleteCases[MomList,x_/;MemberQ[Flatten[{label}],x]];MomReps=Table[i->ToString[i],{i,MomList}]; Protect[MomList,MomReps];);
UndeclareMom[]:=(Unprotect[MomList,MomReps];MomList={};MomReps={}; Protect[MomList,MomReps];);
(*Protect the function definitions*)
Protect[DeclareMom,UndeclareMom];


(* ::Subsection::Closed:: *)
(*DeclareMassless and MasslessMomenta*)


MasslessMomenta={};
Protect[MasslessMomenta];

DeclareMassless[moms__]:=Module[{x},
x=Flatten[{moms}];
Unprotect[Extramass,Extramasstilde,MasslessMomenta,mp];
Do[Extramass[i]=0;Extramasstilde[i]=0;SetMp[mp[i,i]->0],{i,x}];
MasslessMomenta={MasslessMomenta,x}//Flatten//DeleteDuplicates;
Protect[Extramass,Extramasstilde,MasslessMomenta,mp];
];

Protect[DeclareMassless];


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
SpinorUndot /: Times[levicivita2Down[a_,b_],SpinorUndot[mom_][type_][b_][Null]]:=SpinorUndot[mom][type][Null][a];
SpinorUndot /: Times[levicivita2Down[a_,b_],SpinorUndot[mom_][type_][a_][Null]]:=-SpinorUndot[mom][type][Null][b];
SpinorUndot /: Times[levicivita2Up[a_,b_],SpinorUndot[mom_][type_][Null][b_]]:=SpinorUndot[mom][type][a][Null];
SpinorUndot /: Times[levicivita2Up[a_,b_],SpinorUndot[mom_][type_][Null][a_]]:=-SpinorUndot[mom][type][b][Null];


(*Define the properties with respect to declared momenta*)
SpinorUndot[x_+a_.*momlabel_String][type_][upper_][lower_]:=SpinorUndot[x][type][upper][lower]+SpinorUndot[a*momlabel][type][upper][lower];
SpinorUndot[Times[-1,a1___,momlabel_String,a2___]][type_][upper_][lower_]:=I*SpinorUndot[a1*momlabel*a2][type][upper][lower];
SpinorUndot[a_*momlabel_String][type_][upper_][lower_]:=a*SpinorUndot[momlabel][type][upper][lower];
SpinorUndot[momlabel_][type_][upper_][lower_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=SpinorUndot[momlabel/.MomReps][type][upper][lower];


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
SpinorDot /: Times[levicivita2Down[a_,b_],SpinorDot[mom_][type_][b_][Null]]:=SpinorDot[mom][type][Null][a];
SpinorDot /: Times[levicivita2Down[a_,b_],SpinorDot[mom_][type_][a_][Null]]:=-SpinorDot[mom][type][Null][b];
SpinorDot /: Times[levicivita2Up[a_,b_],SpinorDot[mom_][type_][Null][b_]]:=SpinorDot[mom][type][a][Null];
SpinorDot /: Times[levicivita2Up[a_,b_],SpinorDot[mom_][type_][Null][a_]]:=-SpinorDot[mom][type][b][Null];


(*Define the properties with respect to declared momenta*)
SpinorDot[x_+a_.*momlabel_String][type_][upper_][lower_]:=SpinorDot[x][type][upper][lower]+SpinorDot[a*momlabel][type][upper][lower];
SpinorDot[Times[-1,a1___,momlabel_String,a2___]][type_][upper_][lower_]:=I*SpinorDot[a1*momlabel*a2][type][upper][lower];
SpinorDot[a_*momlabel_String][type_][upper_][lower_]:=a*SpinorDot[momlabel][type][upper][lower];
SpinorDot[momlabel_][type_][upper_][lower_]/;AnyTrue[MomList,!FreeQ[momlabel,#]&]:=SpinorDot[momlabel/.MomReps][type][upper][lower];


(* ::Subsection:: *)
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
SpinorAngleBracket[Times[-1,a1___,momlabel_String,a2___],y_]:=I*SpinorAngleBracket[a1*momlabel*a2,y];
SpinorAngleBracket[a_*momlabel_String,y_]:=a*SpinorAngleBracket[momlabel,y];

SpinorAngleBracket[y_,x_+a_.*momlabel_String]:=SpinorAngleBracket[y,x]+SpinorAngleBracket[y,a*momlabel];
SpinorAngleBracket[y_,Times[-1,a1___,momlabel_String,a2___]]:=I*SpinorAngleBracket[y,a1*momlabel*a2];
SpinorAngleBracket[y_,a_*momlabel_String]:=a*SpinorAngleBracket[y,momlabel];

SpinorAngleBracket[x_+a_.*momlabel_?obarQ,y_]:=SpinorAngleBracket[x,y]+SpinorAngleBracket[a*momlabel,y];
SpinorAngleBracket[Times[-1,a1___,momlabel_?obarQ,a2___],y_]:=I*SpinorAngleBracket[a1*momlabel*a2,y];
SpinorAngleBracket[a_*momlabel_?obarQ,y_]:=a*SpinorAngleBracket[momlabel,y];

SpinorAngleBracket[y_,x_+a_.*momlabel_?obarQ]:=SpinorAngleBracket[y,x]+SpinorAngleBracket[y,a*momlabel];
SpinorAngleBracket[y_,Times[-1,a1___,momlabel_?obarQ,a2___]]:=I*SpinorAngleBracket[y,a1*momlabel*a2];
SpinorAngleBracket[y_,a_*momlabel_?obarQ]:=a*SpinorAngleBracket[y,momlabel];

(*Shortcut definition*)
If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "ab" -> SpinorAngleBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]];
    ];


(* ::Subsection:: *)
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
SpinorSquareBracket[Times[-1,a1___,momlabel_String,a2___],y_]:=I*SpinorSquareBracket[a1*momlabel*a2,y];
SpinorSquareBracket[a_*momlabel_String,y_]:=a*SpinorSquareBracket[momlabel,y];

SpinorSquareBracket[y_,x_+a_.*momlabel_String]:=SpinorSquareBracket[y,x]+SpinorSquareBracket[y,a*momlabel];
SpinorSquareBracket[y_,Times[-1,a1___,momlabel_String,a2___]]:=I*SpinorSquareBracket[y,a1*momlabel*a2];
SpinorSquareBracket[y_,a_*momlabel_String]:=a*SpinorSquareBracket[y,momlabel];

SpinorSquareBracket[x_+a_.*momlabel_?obarQ,y_]:=SpinorSquareBracket[x,y]+SpinorSquareBracket[a*momlabel,y];
SpinorSquareBracket[Times[-1,a1___,momlabel_?obarQ,a2___],y_]:=I*SpinorSquareBracket[a1*momlabel*a2,y];
SpinorSquareBracket[a_*momlabel_?obarQ,y_]:=a*SpinorSquareBracket[momlabel,y];

SpinorSquareBracket[y_,x_+a_.*momlabel_?obarQ]:=SpinorSquareBracket[y,x]+SpinorSquareBracket[y,a*momlabel];
SpinorSquareBracket[y_,Times[-1,a1___,momlabel_?obarQ,a2___]]:=I*SpinorSquareBracket[y,a1*momlabel*a2];
SpinorSquareBracket[y_,a_*momlabel_?obarQ]:=a*SpinorSquareBracket[y,momlabel];

If[frontend==1,
SetOptions[EvaluationNotebook[],
    InputAliases -> DeleteDuplicates @ Append[InputAliases /. Options[EvaluationNotebook[], InputAliases], "sb" -> SpinorSquareBracketBox["\[SelectionPlaceholder]", "\[Placeholder]"]]];
    ];


(* ::Section:: *)
(*End of context*)


(*End the private context*)
End[]

(*End the package*)
EndPackage[]
