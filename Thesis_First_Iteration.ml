(* Justin lachapelle - University of Ottawa *)
(* SAT implementation based on the pseudocode provided on page 227 in the book 
   Logic in Computer Science: Modelling and Reasoning About Systems 
   by Michael Huth and Mark Ryan, second edition *)

(* Types *)
type state = State of int
type transitions = state list
type prop = string
type form =
  | True
  | False
  | And of form * form
  | Or of form * form
  | Imp of form * form
  | Neg of form
  | Prop of prop
  | AX of form
  | EX of form
  | AU of form * form
  | EU of form * form
  | EF of form
  | EG of form
  | AF of form
  | AG of form

(* Predicate Functions *)
(* Function to check if proposition is true *)
let hasProposition (proposition : string) ((s,props) : state * prop list) : bool = List.mem proposition props 

(* Function to Compare two states *)
let stateComparator (s1 : state) (s2 : state) : int = 
    match (s1,s2) with
    | (State(x),State(y)) -> x - y

(* Function to check if state exists in a list of states *)
let hasStateInList (sl : state list) (s : state) : bool = List.mem s sl

(* Function to check if state does not exist in list *)
let doesNotHaveStateInList (sl : state list) (s : state) : bool = not (List.mem s sl)

(* Function to check if a state can transition into a subset of states *)
let canStateXTransitionIntoSubsetY (subset_Y: state list) (s: state * transitions): bool =
    let isTransitionInSubset (subset_Y: state list) (s1: state): bool = List.mem s1 subset_Y in
    match s with
    | (_,transitions) -> List.exists (isTransitionInSubset subset_Y) transitions

(* Algorithm Functions *)
(* PreExistential Function:
    Takes a subeset Y of states and returns the set of states which CAN make a transition into Y *)
let preExistential (subset_Y: state list) (model: (state * transitions) list) : state list =
    match List.split (List.filter (canStateXTransitionIntoSubsetY subset_Y) model) with
                            | (state_list,_) -> state_list
(*  PreUniversal Functions:
    Takes a subset Y of states and returns the set of states which make transitions ONLY into Y *)
let preUniversal (subset_Y: state list) (model: (state * transitions) list) : state list =
    let (setS,transitionsList) = List.split model in
    let setSMinusY: state list = List.filter (doesNotHaveStateInList (subset_Y)) setS in
    let preExistentialResult = preExistential setSMinusY model in
    List.filter (doesNotHaveStateInList (preExistentialResult)) setS

(* Implementation of CTL Model Checking Alogirthm *)
let rec sat (model: (state * transitions) list) (labels: (state * prop list) list) (ctl_form: form) : state list = 
    (* SubRoutines EX, AF & EU *)
    let satEX (model: (state * transitions) list) (labels: (state * prop list) list) (ctl_form: form) : state list =
        let x : state list = sat model labels ctl_form in
        preExistential x model
    in
    let satAF (model: (state * transitions) list) (labels: (state * prop list) list) (ctl_form: form) : state list =
        let (setS,_) = List.split model in
        let var_y: state list = sat model labels ctl_form in
        let rec recSatAF (model: (state * transitions) list) (labels: (state * prop list) list) (ctl_form: form) (x: state list) (y: state list) : state list =
            if x = y then y
            else let new_x = y in
                let new_y = List.sort_uniq (stateComparator) ((y) @ (preUniversal y model)) in (* Union two lists, sorts and removes duplicates *)
                recSatAF model labels ctl_form new_x new_y 
        in
        recSatAF model labels ctl_form setS var_y
    in
    let satEU (model: (state * transitions) list) (labels: (state * prop list) list) (ctl_form1: form) (ctl_form2: form) : state list = 
        let (setS,_) = List.split model in
        let var_w: state list = sat model labels ctl_form1 in
        let var_y: state list = sat model labels ctl_form2 in
        let rec recSatEU (model: (state * transitions) list) (labels: (state * prop list) list) (ctl_form1: form) (ctl_form2: form) (x: state list) (y: state list) (w: state list) : state list =
            if x = y then y
            else let new_x = y in
                let new_y =  List.sort_uniq (stateComparator) ((y) @ List.filter (hasStateInList w) (preExistential y model)) in
                recSatEU model labels ctl_form1 ctl_form2 new_x new_y w
        in
        recSatEU model labels ctl_form1 ctl_form2 setS var_y var_w
    in
    (* Implementation of SAT *)
    match ctl_form with
    (* return all states *)
    | True -> (match List.split model with
            | (state_list,_) -> state_list) 
    (* returns the empty set *)
    | False -> [] 
    (*filters labels using a two-parameter predicate with the first parameter binded to the predicate.
    The second parameter is a label item that is compared to the binded proposition *)
    | Prop(proposition) -> (match List.split (List.filter (hasProposition proposition) labels) with
                            | (state_list,_) -> state_list) 
    (* applies sat on two CTL subformulas, taking the Union of the results. Returns a unique sorted list *)
    | Or(f1,f2) -> List.sort_uniq (stateComparator) ((sat model labels f1) @ (sat model labels f2))
    (* applies sat on two CTL subformulas, taking the Intersection of the results. Returns a unique sorted list *)
    (* Sort both lists in nLog(n) and then keep the duplicates in linear time nlog(n) + mlog(m) + (n+m) *)
    | And(f1,f2) -> List.filter (hasStateInList (sat model labels f1)) (sat model labels f2)
    (* applies sat on the CTL formula. Returns the set difference between the set of states S and the result of sat *)
    | Neg(f) -> (match List.split model with
            | (state_list,_) -> List.filter (doesNotHaveStateInList (sat model labels f)) state_list)
    | Imp(f1,f2) -> sat model labels (Or(Neg(f1),f2)) (* f1 V -F2 *)
    | AX(f1) -> sat model labels (Neg(EX(Neg(f1)))) (* -EX-f1 *)
    | EX(f1) -> satEX model labels f1 (* satEX *)
    | AU(f1,f2) -> sat model labels (Neg(Or(EU(Neg(f2),And(Neg(f1),Neg(f2))),EG(Neg(f2))))) (* -(EU(-f2,(-f1 ^ -f2))V (EG-f2) )) *)
    | EU(f1,f2) -> satEU model labels f1 f2
    | EF(f1) -> sat model labels (EU(True,f1))
    | EG(f1) -> sat model labels (Neg(AF(Neg(f1))))
    | AF(f1) -> satAF model labels f1
    | AG(f1) -> sat model labels (Neg(EF(Neg(f1))))


(* Test data for example from the book *)
let model2 = [(State(0),[State(1);State(5)]); (State(1),[State(2);State(3)]); (State(2),[State(0);State(4)]); (State(3),[State(4)]); (State(4),[State(5)]); (State(5),[State(9);State(6)]); (State(6),[State(0);State(7)]); (State(7),[State(1)]);(State(9),[State(7)])]
let labels2 = [(State(0),["n1";"n2"]);(State(1),["t1";"n2"]);(State(2),["c1";"n2"]);(State(3),["t1";"t2"]);(State(4),["c1";"t2"]);(State(5),["n1";"t2"]);(State(6),["n1";"c2"]);(State(7),["t1";"c2"]);(State(9),["t1";"t2"])]
let eu1 = EU(Neg(Prop("c2")),Prop("c1")) 

(* Test CTL formulas for models and labels in the book  *)
let af1 : form = AF(And(Prop("t1"),Prop("t2")))
let af2 : form = AF(Prop("t1"))
let truth1 : form = True (* answer : all states 0-7,9 *)
let false1 : form = False (* answer : empty set *)
let prop3 : form = Prop("c1") (* answer : 2 & 4 *)
let or4 : form =  Or(Prop("c1"),Prop("c2")) (* answer : 2,4,6,7*)
let and6 : form = And(Prop("t1"),Prop("t2")) (* answer : 1 & 2 *)
let ex1 : form = EX(and6)

(* Test CTL formulas for models and labels 1  *)
let model1 : (state * transitions) list = [ (State(1),[State(2)]); (State(2),[State(3)]); (State(3),[State(2)]) ]
let labels1 : (state * prop list) list = [(State(1),["q";"r"]);(State(2),["q";"s"]);(State(3),["t"])]
let truth1 : form = True (* answer : all states *)
let false1 : form = False (* answer : empty set *)
let prop1 : form = Prop("q") (* answer : 1 & 2 *)
let prop2 : form = Prop("t") 
let or1 : form =  Or(Prop("q"),Prop("t")) (* answer : 1,2 & 3*)
let or2 : form =  Or(Prop("q"),Prop("q")) (* answer : 1,2 & 3 with no duplicates *)
let or3 : form =  Or(Prop("z"),Prop("x")) (* answer : empty set *)
let and1 : form = And(Prop("q"),Prop("r")) (* answer : 1 *)
let and2 : form = And(Prop("q"),Prop("s")) (* answer : 2 *)
let and3 : form = And(Prop("t"),Prop("t")) (* answer : 3 with no duplicates *)
let and4 : form = And(Prop("s"),Prop("t")) (* answer : empty set *)
let and5 : form = And(Prop("q"),True) (* answer : 1 & 2 *)
let and7 : form = And(Prop("t"),Prop("true")) (* answer : 3 with no duplicates *)
let neg1 : form = Neg(And(Prop("q"),True)) (* answer : 3 *)
let neg2 : form = Neg(True) (* answer : empty set *)
let neg3 : form = Neg(False) (* answer : set S *)
let neg4 : form = Neg(Prop("q")) (* answer : 3*)
let imp1 : form = Imp(Prop("q"),Or(Prop("r"),Prop("s"))) (* answer : 1,2,3 *)
let imp2 : form = Imp(Prop("q"),Prop("r")) (* answer : 1 & 3 *)

(* Test subsets with model/labels 1 for preExistential function *)
let subset_Y1 : state list = [State(1)] (* answer : empty set *)
let subset_Y2 : state list = [State(2)] (* answer : 1 & 3 *)
let subset_Y3 : state list = [State(3)] (* answer : 1 & 3 *)

(* Tests subsets with model/labels1 for preUniversal function *)
let subset_Y1 : state list = [State(1)] (* answer : empty set *)
let subset_Y2 : state list = [State(2)] (* answer : 1 & 3 *)
let subset_Y3 : state list = [State(3)] (* answer : 2 *)


