module
public import Theory.SpecificGroups.Rudvalis.PointCoreIntersection
public import Theory.GroupTheory.PCoreIntersectionFivePointExact
public import Theory.SpecificGroups.SymmetricFive.TranspositionCentralizer

/-!
# The exact ambient point quotient in Rudvalis

Suppose the literal stabilizer of a central-class module point has order
12288 and maps onto a group of order 192 with two-core order 32. If the
kernel is the original module and that module meets the ambient point
core in order 32, the ambient S₅ quotient has kernel order 1024. Its image
is the full centralizer of a transposition, hence is actually D₁₂.
The quotient therefore kills commutators with the stabilizer's two-core.

The proof compares the two literal maps using kernel-image counting;
it never identifies the ambient kernel with the natural-action kernel.
The Chapter13 original odd-actor application supplies every hypothesis,
including the natural parabolic and original quotient marking.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
namespace Rudvalis
open Subgroup Theory.GroupTheory

/-- The actual point quotient retains a transposition from the original module. -/
theorem point_core_intersection_exact
    (C E : Subgroup Model) (hEC : E ≤ C) (z : E)
    (hED : E ≤ centralizer ({(z : Model)} : Set Model))
    (hclass : IsConj (z : Model) (b ^ 2))
    (hPcard : Nat.card ((centralizer ({(z : Model)} : Set Model)).subgroupOf C) = 12288)
    (hintersect : Nat.card (E ⊓ (centralizer ({(z : Model)} : Set Model)).pCoreIn 2 : Subgroup Model) = 32)
    {B : Type*} [Group B] [Finite B]
    (b : ((centralizer ({(z : Model)} : Set Model)).subgroupOf C) →* B)
    (hb : Function.Surjective b)
    (hbk : b.ker = (E.subgroupOf C).subgroupOf
      ((centralizer ({(z : Model)} : Set Model)).subgroupOf C))
    (hBcard : Nat.card B = 192) (hcore : Nat.card (pCore 2 B) = 32) :
    let D := centralizer ({(z : Model)} : Set Model)
    let P := D.subgroupOf C
      ∃ q : D →* Equiv.Perm (Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 D ∧
        let i : P →* D := {
          toFun := fun x => ⟨x.val.val,x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
        let r := q.comp i
        r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P ∧
        r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2 ∧
        Nat.card r.ker = 1024 ∧ Nat.card r.range = 12 ∧
        ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
          ((E.subgroupOf C).subgroupOf P).map r = zpowers t ∧
          r.range = centralizer ({t} : Set (Equiv.Perm (Fin 5))) ∧
          Nonempty ((P ⧸ r.ker) ≃* DihedralGroup 6) ∧ ⁅pCore 2 P,⊤⁆ ≤ r.ker := by
  let D := centralizer ({(z : Model)} : Set Model)
  let P := D.subgroupOf C
  dsimp only
  obtain ⟨q,hqdata⟩ :=
    Rudvalis.point_core_intersection_quotient C z hclass hPcard
  let i : P →* D := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let r := q.comp i
  have hq : Function.Surjective q := hqdata.1
  have hqk : q.ker = pCore 2 D := hqdata.2.1
  have hrk : r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P := hqdata.2.2.1
  have hrmap : r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2 := hqdata.2.2.2.1
  have hsizes : (Nat.card r.ker = 2048 ∧ Nat.card r.range = 6) ∨
      (Nat.card r.ker = 1024 ∧ Nat.card r.range = 12) ∨
      (Nat.card r.ker = 512 ∧ Nat.card r.range = 24) := hqdata.2.2.2.2
  let j := C.subtype.comp P.subtype
  have hj : Function.Injective j := C.subtype_injective.comp P.subtype_injective
  have hEP : E.subgroupOf C ≤ P := fun _ hx => hED hx
  have hbmap : b.ker.map j = E := by
    rw [hbk,←map_map,map_subgroupOf_eq_of_le hEP,map_subgroupOf_eq_of_le hEC]
  have hbcard : Nat.card b.ker = 64 := by
    have hm := b.ker.card_mul_index
    rw [index_ker,b.range_eq_top_of_surjective hb,card_top,
      hBcard] at hm
    omega
  have hinter : Nat.card (b.ker ⊓ r.ker : Subgroup P) = 32 := by
    rw [←card_map_of_injective hj,map_inf _ _ _ hj,hbmap,hrmap,
      ←inf_assoc,inf_eq_left.mpr hEC]
    exact hintersect
  have hrtwo : IsPGroup 2 r.ker := by
    have he : r.ker = (pCore 2 D).comap i := by
      change (q.comp i).ker = _
      change q.ker.comap i = _
      rw [hqk]
    rw [he]
    exact pCore_isPGroup.comap_of_injective i (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun v : D => (v : Model)) h)))
  obtain ⟨hk,hr,t,ht,hN,hR⟩ := fivePoint_image_exact_of_two_kernels
    b hb r hcore hbcard hinter hrtwo hsizes
  obtain ⟨et⟩ := Theory.SpecificGroups.SymmetricFive.transposition_centralizer_dihedral t ht
  refine ⟨q,hq,hqk,hrk,hrmap,hk,hr,t,ht,?_,hR,?_,?_⟩
  · rwa [hbk] at hN
  · exact ⟨(QuotientGroup.quotientKerEquivRange r).trans
      ((MulEquiv.subgroupCongr hR).trans et)⟩
  · exact Theory.SpecificGroups.SymmetricFive.transposition_image_twoCore_commutator r t ht hR

end Rudvalis
