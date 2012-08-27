(* Delta Debugging Algorithm 
 *
 * Author: Lisong Guo 
 * Date:   24 Aug, 2012 
 *
 * Reference: 
   Andreas Zeller and Ralf Hildebrandt. 2002. Simplifying and Isolating
    Failure-Inducing Input. IEEE Trans. Softw. Eng. 28, 2 (February 2002),
    183-200. DOI=10.1109/32.988498 
 * *)

let is_DEBUG = false ;;  (*a global flag for debugging*)

(* Data structure for profiling *)
type profile = { 
  mutable ddmin_test_count : int;
  mutable dd_test_count : int } ;;

let profiling = { ddmin_test_count=0; dd_test_count=0 } ;;


(* Data type defined for test case outcomes, all constants *)
type testcase_outcome = PASS | FAIL | UNRESOLVED ;;

let print_outcome oc = 
  match oc with 
    PASS -> print_string "PASS" 
  | FAIL -> print_string "FAIL"
  | UNRESOLVED -> print_string "UNRESOLVED" ;;


(* Function that checks the result of test case, 
 *  using pattern matching to change the configuration. 
 * Note: in the following case, change set (1, 7, 8) is the right recipe
 * to make the test case fail. 
 *  *)
let rec test_rec tc pg =  
  match tc with 
    1::tail -> test_rec tail 1  (*first sign, carry on*)
  | 7::tail -> if pg = 1 
               then test_rec tail 8 
               else UNRESOLVED  
  | 8::_    -> if pg = 8 
               then FAIL    (*the right recipe!*)     
               else UNRESOLVED 
  | others::tail -> test_rec tail pg 
  | [] -> UNRESOLVED ;;


(* Initialize the value of progress indicator 'pg', 
 *   and turn the recusive function into non-recursive.
 *
 * The progress is the accumulation value of all expected elements 
 *  that encounterred so far. 
 *  *)
let test tc = test_rec tc 0 ;;


(* Verify the 'test' function *)
let test_case_unrt = [1; 7] and 
  test_case_fail = [1; 4; 7; 8] in 
    if is_DEBUG then 
    begin 
      print_outcome (test test_case_unrt);
      print_newline();
      print_outcome (test test_case_fail);
      print_newline()
    end ;;


(* Function to divide array into the subsets and its complementary sets. 
 * Note: Array is adopted here instead of list, 
 *        since it has spliting function "sub" which comes in handy.
 *
 * For example:
   array = [1; 2; 3; 4; 5; 6], num = 3; 
   index 0 = [1; 2]   index 1 = [3; 4]  index 2 = [5; 6]
   index 3 = [3; 4; 5; 6] 
   index 4 = [1; 2; 5; 6]
   index 5 = [1; 2; 3; 4]
 
 * Conditions: 
 *  0 <= index < 2*num 
 *  2 <= num <= array.length
 *  *)
let subset array num index = 
  let size = (Array.length array)/num in 
    if num > Array.length array 
    then [||]     (* num <= array.length *)
    
    else if index < num 
    then Array.sub array (index*size) size 
    
    else if index < 2*num 
    then Array.append (Array.sub array 0 ((index-num)*size)) 
                      (Array.sub array ((index-num+1)*size)
                                     ((2*num-index-1)*size))
    else [||]     (* index < 2*num *) ;;

let print_int_array a = 
  if Array.length a = 0
  then print_endline "[]"
  else let print_elem e = 
         print_int e; print_string ";" 
       in
         Array.iter print_elem a;
         print_newline() ;;

let test_array = [|1; 2; 3; 4; 5; 6; 7; 8|] ;;

(* Verify the 'subset' function *)
if is_DEBUG then
begin
  print_int_array (subset test_array 4 7);
  print_newline() 
end ;;

(* Find the difference between list op1 and op2. 
 *  The concept of algorithm applies to the general set structure.  
 *
 * Conditions: 
 * op1, op2 should be sorted in the same order. 
 * op1 is the superset of op2. 
 * *)
let rec set_diff_rec op1 op2 =
  (* Start from the larger set *)
  match op1 with
    [] -> []
  | op1_h::op1_t -> 
      match op2 with
        [] -> op1
      | op2_h::op2_t -> 
          if op1_h = op2_h 
          then set_diff_rec op1_t op2_t 
          else op1_h :: set_diff_rec op1_t op2 ;;

(* Another version of function set_diff_rec *)
let rec set_diff_rec_2 op1 op2 =
  match (op1, op2) with
    ([], _) -> []
  | (_, []) -> op1
  | (op1_h::op1_t, op2_h::op2_t) -> 
      if op1_h = op2_h 
      then set_diff_rec_2 op1_t op2_t 
      else op1_h :: set_diff_rec_2 op1_t op2 ;;

(* Adjust the order of parameters and wrap into non-recursive function*)
let set_diff op1 op2 = 
  if List.length op1 > List.length op2 
  then set_diff_rec_2 op1 op2 
  else set_diff_rec_2 op2 op1 ;;


if is_DEBUG then 
begin
  print_endline "Test function set_diff: "; 
  let op2 = [1; 2; 3; 4; 5; 6; 7; 8] and op1 = [4; 5] in 
    print_int_array (Array.of_list (set_diff op1 op2)) 
end ;;  


(* Merge two lists, 
 * The result would be sorted, 
 *  no matter whether the input lists are ordered or not. 
 * *)
let set_union s1 s2 = 
  (* Define the comparison function *)
  let cmp p1 p2 = 
    if p1 = p2      then 0 
    else if p1 < p2 then -1 
    else 1 
  in 
  List.merge cmp (List.fast_sort cmp s1) (List.fast_sort cmp s2) ;; 

if is_DEBUG then
begin
  print_endline "Test function set_union: "; 
  let op1 = [ 3; 1; 4; 5] and op2 = [7; 8] in 
       print_int_array (Array.of_list (set_union op1 op2))
end ;;


(* Algorithm to minimize the differences between two change sets *)
let rec dd_rec c0 cx n i = 
  begin 
  profiling.dd_test_count <- profiling.dd_test_count + 1 ; 


  let diff = set_diff c0 cx in 
    let delta = subset (Array.of_list diff) n i in 
      let union = set_union c0 (Array.to_list delta) and 
          cplmt = set_diff cx  (Array.to_list delta) in 
        let oc_union = test union and 
            oc_cplmt = test cplmt in 
          match (oc_union, oc_cplmt) with 
            (* reduce to subset *)
            (FAIL, _) -> dd_rec c0 union 2 0 

            (* increase to complement *)
          | (_, PASS) -> dd_rec cplmt cx 2 0 

            (* increase to subset *)
          | (PASS, _) -> dd_rec union cx (max (n-1) 2) 0

            (* reduce to complement *)
          | (_, FAIL) -> dd_rec c0 cplmt (max (n-2) 2) 0 

          | (_, _) -> 
              (* still has more subsets to evaluate, do tail recursion*)
              if i < (n-1) 
              then dd_rec c0 cx n (i+1)
              
              (* exhaust subsets, then increase granulity *)
              else if n < (List.length diff) 
              then dd_rec c0 cx (min (2*n) (List.length diff)) 0

              (* bottom of tail recursion *)
              else (c0, cx) 
  end ;;

(* The general Delta Debugging algorithm *)
let dd cx = dd_rec [] cx 2 0 ;;


(* Algorithm to minimize one single change set *) 
let rec ddmin_rec array n i =
  begin 
  (* Profiling *)
  profiling.ddmin_test_count <- profiling.ddmin_test_count + 1; 

  let case = subset array n i in  
    let outcome = test (Array.to_list case) in   
      match outcome with 
        FAIL -> 
          print_int_array array; 
          if i < n 
          then ddmin_rec case 2 0
          else ddmin_rec case (max (n-1) 2)  0

      | PASS | UNRESOLVED -> 
          (*exhausted all subsets, find the minimum*)
          if (n >= Array.length array) && i >= (2*n) 
          then array
          
          else if i >= (2*n) 
          (*increate the granuality*)
          then ddmin_rec array (n*2) 0
          
          (*move on to the next subset of array*)
          else ddmin_rec array n (i+1) 
  end ;;


let ddmin cs = 
  (* first, transform list into array*)
  let array = Array.of_list cs in

  (*encapsulate the resursive function into non-resurive one*)
  ddmin_rec array 2 0 ;;

let main () = 
  let test_case = [1; 2; 3; 4; 5; 6; 7; 8] in 
  print_endline "Initial change set:";
  print_int_array (Array.of_list test_case);
  
  print_endline "\nddmin...";
  print_int_array (ddmin test_case);    

  print_endline "\ndd...";
  let (c0, cx) = dd test_case in  
  print_string "c0: ";
  print_int_array (Array.of_list c0);    
  print_string "cx: "; 
  print_int_array (Array.of_list cx); 
  print_string "diff: "; 
  print_int_array (Array.of_list (set_diff cx c0));
  print_newline(); 

  print_endline "Profiling...";
  print_string "ddmin_test_count:";
  print_int profiling.ddmin_test_count;
  print_newline();
  print_string "dd_test_count:";
  print_int profiling.dd_test_count;
  print_newline() ;;

(* Tracing setting 
#trace ddmin_rec ;;
#trace dd_rec ;;
*)





(* Kicking off, after all the definitions above *)
main () ;;


