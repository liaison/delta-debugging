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
        mutable test_count : int;
};;

let profiling = { test_count = 0; } ;;


(* Data type defined for test case outcomes, all constants *)
type testcase_outcome = PASS | FAIL | UNRESOLVED ;;

let print_outcome oc = 
    match oc with
        PASS -> print_string "PASS" 
      | FAIL -> print_string "FAIL"
      | UNRESOLVED -> print_string "UNRESOLVED"
;;


(* Function that checks the result of test case, 
 *  using pattern matching to change the configuration. 
 * Note: in the following case, change set (1, 7, 8) is the right recipe
 * to make the test case fail. 
 *  *)
let rec test_rec tc pg =  
    match tc with 
        1::tail -> test_rec tail 1  (*first sign, carry on*)
      | 7::tail -> if pg=1 then test_rec tail 8 else UNRESOLVED  
      | 8::_    -> if pg=8 then FAIL    (*the right recipe!*)     
                   else UNRESOLVED 
      | others::tail -> test_rec tail pg 
      | [] -> UNRESOLVED  
;;


(* Initialize the value of progress indicator 'pg', 
 *   and turn the recusive function into non-recursive.
 *
 * The progress is the accumulation value of all expected elements 
 *  that encounterred so far. 
 *  *)
let test tc = test_rec tc 0 ;;


(* Verify the 'test' function *)
let test_case_unrt = [1; 7;] and 
    test_case_fail = [1; 4; 7; 8;] in 
        if is_DEBUG then 
        begin 
            print_outcome (test test_case_unrt);
            print_newline();
            print_outcome (test test_case_fail);
            print_newline()
        end 
;;


(* Function to divide array into the subsets and its complementary sets. 
 * Note: Array is adopted here instead of list, 
 *        since it has spliting function "sub" which comes in handy.
 *
 * For example:
    array = {1; 2; 3; 4; 5; 6;}, num = 3; 
    index 0 = {1; 2}   index 1 = {3; 4}  index 2 = {5; 6}
    index 3 = {3; 4; 5; 6} 
    index 4 = {1; 2; 5; 6}
    index 5 = {1; 2; 3; 4}
 
 * Conditions: 
 *  0 <= index < 2*num 
 *  2 <= num <= array.length
 *  *)
let subset array num index = 
    let size = (Array.length array) / num in 
        if num > Array.length array then 
            [||]     (* num <= array.length *)
        else 
            if index < num then 
                Array.sub array (index*size) size 
            else
                if index < 2*num then 
                    Array.append (Array.sub array 0 ((index-num)*size)) 
                                 (Array.sub array ((index-num+1)*size)
                                                ((2*num-index-1)*size))
                else [||] (* index < 2*num *)
;;


let print_int_array a = 
    let print_elem e = 
            print_int e; 
            print_string ";" 
    in         
        Array.iter print_elem a;
        print_newline()
;;

let test_array = [|1; 2; 3; 4; 5; 6; 7; 8;|] ;;

(* Verify the 'subset' function *)
if is_DEBUG then
    begin
        print_int_array (subset test_array 4 7);
        print_newline() 
    end
;;


(* main body of Delta Debugging algorithm*) 
let rec ddmin_rec array n i =
    begin 
    (* Profiling *)
    profiling.test_count <- profiling.test_count + 1; 

    let case = subset array n i in  
        let outcome = test (Array.to_list case) in   
            match outcome with 
                FAIL -> 
                    print_int_array array; 
                    if i < n then 
                        ddmin_rec case 2 0
                    else 
                        ddmin_rec case (max (n-1) 2)  0

              | PASS | UNRESOLVED -> 
                    if (n>=Array.length array) && i>=(2*n) then 
                        (*exhausted all subsets, find the minimum*)
                        array
                    else
                        if i>=(2*n) then
                            (*increate the granuality*)
                            ddmin_rec array (n*2) 0
                        else 
                            (*move on to the next subset of array*)
                            ddmin_rec array n (i+1) 
    end
;;


let ddmin cs = 
    (* first, transform list into array*)
    let array = Array.of_list cs in

    (*encapsulate the resursive function into non-resurive one*)
    ddmin_rec array 2 0 
;;

let main () = 
        let test_case = [1; 2; 3; 4; 5; 6; 7; 8;] in 
        print_endline "Initial change set:";
        print_int_array (Array.of_list test_case);
        
        print_endline "\nStart reduction...";
        print_int_array (ddmin test_case);    
        print_newline();

        print_endline "Profiling";
        print_string "test_count:";
        print_int profiling.test_count;
        print_newline();
;;

(* Tracing setting 
#trace ddmin_rec ;;
*)


(* Kicking off, after all the definitions above *)
main ();;






