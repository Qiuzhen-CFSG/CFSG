module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCountTransportA256
/-!
# Intrinsic fiber counts for the order-256 small even candidates

Both prescribed order/centralizer tests are counted on the exact candidates
7 through 17. The transport module identifies the group-theoretic predicates
with polynomial equations and a Boolean commuting test. The final bit cancels
from commutation, reducing the centralizer enumeration to 128 tuples with a
proved factor of two. Kernel reduction certifies all centralizer values, then
counts the two tests in each of the sixteen fixed coordinate fibers.

The intermediate centralizer tables are checked against the multiplication
law; they are not assumptions. The original quotient coordinates and profile
tables, including the quadratic coordinate of row 7, are used unchanged.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model and
SmallEvenTwoAutCoordinatesA256. The polynomial count transport is proved in
SmallEvenTwoAutCountTransportA256.
-/

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA A256Count
set_option maxRecDepth 32768
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 4000000
private abbrev B7 := Bool × Bool × Bool × Bool × Bool × Bool × Bool
private def inflate (w : B7) (h : Bool) : B8 :=
  (w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2.1,w.2.2.2.2.2.2,h)
private def cut (w : B8) : B7 :=
  (w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2.1,w.2.2.2.2.2.1,w.2.2.2.2.2.2.1)
private theorem quickComm_tail (i : Fin 11) (w z : B8) :
    quickComm i w z = quickComm i (inflate (cut w) false) (inflate (cut z) false) := by
  fin_cases i <;> rfl
private def allB7 : List B7 := [(false,false,false,false,false,false,false),(true,false,false,false,false,false,false),(false,true,false,false,false,false,false),(true,true,false,false,false,false,false),(false,false,true,false,false,false,false),(true,false,true,false,false,false,false),(false,true,true,false,false,false,false),(true,true,true,false,false,false,false),(false,false,false,true,false,false,false),(true,false,false,true,false,false,false),(false,true,false,true,false,false,false),(true,true,false,true,false,false,false),(false,false,true,true,false,false,false),(true,false,true,true,false,false,false),(false,true,true,true,false,false,false),(true,true,true,true,false,false,false),(false,false,false,false,true,false,false),(true,false,false,false,true,false,false),(false,true,false,false,true,false,false),(true,true,false,false,true,false,false),(false,false,true,false,true,false,false),(true,false,true,false,true,false,false),(false,true,true,false,true,false,false),(true,true,true,false,true,false,false),(false,false,false,true,true,false,false),(true,false,false,true,true,false,false),(false,true,false,true,true,false,false),(true,true,false,true,true,false,false),(false,false,true,true,true,false,false),(true,false,true,true,true,false,false),(false,true,true,true,true,false,false),(true,true,true,true,true,false,false),(false,false,false,false,false,true,false),(true,false,false,false,false,true,false),(false,true,false,false,false,true,false),(true,true,false,false,false,true,false),(false,false,true,false,false,true,false),(true,false,true,false,false,true,false),(false,true,true,false,false,true,false),(true,true,true,false,false,true,false),(false,false,false,true,false,true,false),(true,false,false,true,false,true,false),(false,true,false,true,false,true,false),(true,true,false,true,false,true,false),(false,false,true,true,false,true,false),(true,false,true,true,false,true,false),(false,true,true,true,false,true,false),(true,true,true,true,false,true,false),(false,false,false,false,true,true,false),(true,false,false,false,true,true,false),(false,true,false,false,true,true,false),(true,true,false,false,true,true,false),(false,false,true,false,true,true,false),(true,false,true,false,true,true,false),(false,true,true,false,true,true,false),(true,true,true,false,true,true,false),(false,false,false,true,true,true,false),(true,false,false,true,true,true,false),(false,true,false,true,true,true,false),(true,true,false,true,true,true,false),(false,false,true,true,true,true,false),(true,false,true,true,true,true,false),(false,true,true,true,true,true,false),(true,true,true,true,true,true,false),(false,false,false,false,false,false,true),(true,false,false,false,false,false,true),(false,true,false,false,false,false,true),(true,true,false,false,false,false,true),(false,false,true,false,false,false,true),(true,false,true,false,false,false,true),(false,true,true,false,false,false,true),(true,true,true,false,false,false,true),(false,false,false,true,false,false,true),(true,false,false,true,false,false,true),(false,true,false,true,false,false,true),(true,true,false,true,false,false,true),(false,false,true,true,false,false,true),(true,false,true,true,false,false,true),(false,true,true,true,false,false,true),(true,true,true,true,false,false,true),(false,false,false,false,true,false,true),(true,false,false,false,true,false,true),(false,true,false,false,true,false,true),(true,true,false,false,true,false,true),(false,false,true,false,true,false,true),(true,false,true,false,true,false,true),(false,true,true,false,true,false,true),(true,true,true,false,true,false,true),(false,false,false,true,true,false,true),(true,false,false,true,true,false,true),(false,true,false,true,true,false,true),(true,true,false,true,true,false,true),(false,false,true,true,true,false,true),(true,false,true,true,true,false,true),(false,true,true,true,true,false,true),(true,true,true,true,true,false,true),(false,false,false,false,false,true,true),(true,false,false,false,false,true,true),(false,true,false,false,false,true,true),(true,true,false,false,false,true,true),(false,false,true,false,false,true,true),(true,false,true,false,false,true,true),(false,true,true,false,false,true,true),(true,true,true,false,false,true,true),(false,false,false,true,false,true,true),(true,false,false,true,false,true,true),(false,true,false,true,false,true,true),(true,true,false,true,false,true,true),(false,false,true,true,false,true,true),(true,false,true,true,false,true,true),(false,true,true,true,false,true,true),(true,true,true,true,false,true,true),(false,false,false,false,true,true,true),(true,false,false,false,true,true,true),(false,true,false,false,true,true,true),(true,true,false,false,true,true,true),(false,false,true,false,true,true,true),(true,false,true,false,true,true,true),(false,true,true,false,true,true,true),(true,true,true,false,true,true,true),(false,false,false,true,true,true,true),(true,false,false,true,true,true,true),(false,true,false,true,true,true,true),(true,true,false,true,true,true,true),(false,false,true,true,true,true,true),(true,false,true,true,true,true,true),(false,true,true,true,true,true,true),(true,true,true,true,true,true,true)]
private theorem list_split : allB8 = allB7.map (fun w => inflate w false) ++
    allB7.map (fun w => inflate w true) := by decide +kernel
private def shortCent (i : Fin 11) (w : B7) : ℕ :=
  2 * allB7.countP (fun z => quickComm i (inflate z false) (inflate w false))
private theorem quickCent_short (i : Fin 11) (w : B8) :
    quickCent i w = shortCent i (cut w) := by
  unfold quickCent
  rw [list_split, List.countP_append, List.countP_map, List.countP_map]
  have h (b : Bool) :
      List.countP (fun z => quickComm i (inflate z b) w) allB7 =
        List.countP (fun z => quickComm i (inflate z false) (inflate (cut w) false)) allB7 := by
    apply List.countP_congr
    intro z _
    rw [quickComm_tail]
    rfl
  change List.countP (fun z => quickComm i (inflate z false) w) allB7 +
    List.countP (fun z => quickComm i (inflate z true) w) allB7 = _
  rw [h false, h true]
  exact (two_mul _).symm
private def quickTable (i : Fin 11) (w : B8) : ℕ :=
  let n := w.1.toNat + 2*w.2.1.toNat + 4*w.2.2.1.toNat + 8*w.2.2.2.1.toNat +
    16*w.2.2.2.2.1.toNat + 32*w.2.2.2.2.2.1.toNat + 64*w.2.2.2.2.2.2.1.toNat +
    128*w.2.2.2.2.2.2.2.toNat
  match i.val with
  | 0 => ([256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32, 256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 256, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 128, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32, 128, 32, 32, 16, 32, 16, 64, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 16, 16, 16, 16, 32, 32, 64, 32, 32, 16, 32, 16, 64, 32] : List ℕ).getD n 0
  | 1 => ([256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32] : List ℕ).getD n 0
  | 2 => ([256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32] : List ℕ).getD n 0
  | 3 => ([256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 256, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32, 128, 32, 64, 32, 32, 32, 32, 32] : List ℕ).getD n 0
  | 4 => ([256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 256, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32, 128, 32, 64, 32, 64, 32, 64, 32] : List ℕ).getD n 0
  | 5 => ([256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 256, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64] : List ℕ).getD n 0
  | 6 => ([256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 256, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 128, 32, 128, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32, 64, 32] : List ℕ).getD n 0
  | 7 => ([256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 256, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64, 128, 32, 64, 32, 32, 64, 32, 64] : List ℕ).getD n 0
  | 8 => ([256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 256, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32, 128, 32, 32, 64, 32, 64, 64, 32] : List ℕ).getD n 0
  | 9 => ([256, 64, 64, 128, 64, 64, 64, 64, 256, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 256, 64, 64, 128, 64, 64, 64, 64, 256, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64] : List ℕ).getD n 0
  | _ => ([256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 256, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32, 128, 64, 64, 64, 32, 32, 32, 32] : List ℕ).getD n 0

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_0 : ∀ w,
    shortCent 0 w = quickTable 0 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_1 : ∀ w,
    shortCent 1 w = quickTable 1 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_2 : ∀ w,
    shortCent 2 w = quickTable 2 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_3 : ∀ w,
    shortCent 3 w = quickTable 3 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_4 : ∀ w,
    shortCent 4 w = quickTable 4 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_5 : ∀ w,
    shortCent 5 w = quickTable 5 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_6 : ∀ w,
    shortCent 6 w = quickTable 6 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_7 : ∀ w,
    shortCent 7 w = quickTable 7 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_8 : ∀ w,
    shortCent 8 w = quickTable 8 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_9 : ∀ w,
    shortCent 9 w = quickTable 9 (inflate w false) := by decide +kernel

set_option maxHeartbeats 16000000 in
private theorem shortCent_certificate_10 : ∀ w,
    shortCent 10 w = quickTable 10 (inflate w false) := by decide +kernel

private theorem quickTable_tail : ∀ i w,
    quickTable i (inflate (cut w) false) = quickTable i w := by decide +kernel

private theorem quickTable_eq : ∀ i w,
    quickTable i w = centTable i (bits (tupleNumber w)) := by decide +kernel

private theorem cent_certificate (i : Fin 11) (w : A256Bits) :
    cent i w = centTable i w := by
  obtain ⟨n, rfl⟩ := bitsEquiv.surjective w
  obtain ⟨t, rfl⟩ := tupleEquiv.surjective n
  change cent i (bits (tupleNumber t)) = centTable i (bits (tupleNumber t))
  rw [cent_bool, bcent_quick, quickCent_short, ← quickTable_eq, ← quickTable_tail]
  fin_cases i
  · exact shortCent_certificate_0 (cut t)
  · exact shortCent_certificate_1 (cut t)
  · exact shortCent_certificate_2 (cut t)
  · exact shortCent_certificate_3 (cut t)
  · exact shortCent_certificate_4 (cut t)
  · exact shortCent_certificate_5 (cut t)
  · exact shortCent_certificate_6 (cut t)
  · exact shortCent_certificate_7 (cut t)
  · exact shortCent_certificate_8 (cut t)
  · exact shortCent_certificate_9 (cut t)
  · exact shortCent_certificate_10 (cut t)

private def fastTest (i : Fin 11) (j : Fin 2) (w : A256Bits) : Prop :=
  (if j = 0 then square i w = (1, 0) ∧ a256Pair i w ≠ (1, 0)
    else evenPairMul (square i w) (square i w) = (1, 0) ∧ square i w ≠ (1, 0)) ∧
    centTable i w = (fourTests (a256Row i) j).2.1
private instance (i : Fin 11) (j : Fin 2) (w : A256Bits) : Decidable (fastTest i j w) := by
  unfold fastTest; infer_instance

private def fastCount (i : Fin 11) (j : Fin 2) (v : FourQuotient) : ℕ :=
  (Finset.univ.filter (fun n : Fin 256 =>
    a256Coordinates i (bits n) = v ∧ fastTest i j (bits n))).card

private theorem count_fast (i : Fin 11) (j : Fin 2) (v : FourQuotient) :
    count i j v = fastCount i j v := by
  unfold count fastCount
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [test, fastTest, cent_certificate]

set_option maxHeartbeats 8000000 in
private theorem count_certificate : ∀ i n,
    (fastCount i 0 (decodeV n), fastCount i 1 (decodeV n)) =
      fourProfile (a256Row i) (decodeV n) := by
  intro i n
  fin_cases i <;> fin_cases n <;> decide +kernel

/-- Both intrinsic fiber counts of the fixed coordinates, for candidates 7–17. -/
public theorem a256CoordinateProfile_eq (i : Fin 11) (v : FourQuotient) :
    a256CoordinateProfile i v = fourProfile (a256Row i) v := by
  unfold a256CoordinateProfile
  rw [card_test, card_test, count_fast, count_fast]
  simpa only [decodeV_encodeV] using count_certificate i (encodeV v)

end ReeTwo.SylowModel
