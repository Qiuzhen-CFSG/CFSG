module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.QuotientGeometry
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# Full centralizers of the unprimed quotient rows

The native four-generator rows have one orbit of length eight and eight
inequivalent orbits of length two. Their point stabilizers distinguish these
orbits. Consequently every commuting permutation preserves each orbit and
squares to one. A commuting Mathieu permutation fixing a point of the long
orbit and point zero fixes nine points, hence is identity by the proved native
Mathieu involution classes. The sixteen row elements realize every pair of
images of these two points, giving the full quotient centralizer.
Source: Kleidman--Wilson (1988), Figures 1/2, Propositions 2.3.4--2.3.5.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image

def quotientProductTable : Fin 2 → Fin 16 → Fin 24 → Fin 24 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 3, 2, 14, 8, 23, 17, 5, 9, 10, 11, 12, 21, 4, 16, 15, 7, 18, 20, 19, 13, 22, 6], ![0, 1, 2, 3, 16, 7, 23, 5, 17, 22, 10, 12, 11, 13, 15, 14, 4, 8, 18, 20, 19, 21, 9, 6], ![0, 1, 3, 2, 7, 16, 23, 4, 15, 9, 18, 12, 11, 13, 17, 8, 5, 14, 10, 19, 20, 21, 22, 6], ![0, 1, 2, 3, 17, 15, 6, 14, 16, 9, 18, 12, 11, 21, 7, 5, 8, 4, 10, 20, 19, 13, 22, 23], ![0, 1, 3, 2, 15, 17, 6, 8, 7, 22, 10, 12, 11, 21, 16, 4, 14, 5, 18, 19, 20, 13, 9, 23], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![1, 0, 2, 3, 5, 4, 23, 16, 14, 9, 10, 12, 11, 21, 8, 17, 7, 15, 18, 19, 20, 13, 22, 6], ![1, 0, 3, 2, 8, 14, 6, 15, 4, 9, 10, 12, 11, 13, 5, 7, 17, 16, 18, 20, 19, 21, 22, 23], ![1, 0, 2, 3, 14, 8, 6, 17, 5, 22, 18, 12, 11, 13, 4, 16, 15, 7, 10, 19, 20, 21, 9, 23], ![1, 0, 3, 2, 16, 7, 6, 5, 17, 9, 18, 11, 12, 21, 15, 14, 4, 8, 10, 19, 20, 13, 22, 23], ![1, 0, 2, 3, 7, 16, 6, 4, 15, 22, 10, 11, 12, 21, 17, 8, 5, 14, 18, 20, 19, 13, 9, 23], ![1, 0, 3, 2, 17, 15, 23, 14, 16, 22, 10, 11, 12, 13, 7, 5, 8, 4, 18, 19, 20, 21, 9, 6], ![1, 0, 2, 3, 15, 17, 23, 8, 7, 9, 18, 11, 12, 13, 16, 4, 14, 5, 10, 20, 19, 21, 22, 6]], ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 20, 19, 4, 5, 23, 16, 8, 18, 22, 11, 12, 21, 14, 17, 7, 15, 9, 3, 2, 13, 10, 6], ![0, 1, 19, 20, 5, 4, 23, 7, 14, 10, 9, 11, 12, 21, 8, 15, 16, 17, 22, 2, 3, 13, 18, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6], ![0, 1, 18, 10, 5, 4, 23, 16, 8, 20, 3, 12, 11, 13, 14, 15, 7, 17, 2, 22, 9, 21, 19, 6], ![0, 1, 22, 9, 4, 5, 6, 16, 14, 3, 20, 12, 11, 21, 8, 15, 7, 17, 19, 18, 10, 13, 2, 23], ![0, 1, 9, 22, 5, 4, 6, 7, 8, 2, 19, 12, 11, 21, 14, 17, 16, 15, 20, 10, 18, 13, 3, 23], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![1, 0, 2, 3, 5, 4, 23, 16, 14, 9, 10, 12, 11, 21, 8, 17, 7, 15, 18, 19, 20, 13, 22, 6], ![1, 0, 19, 20, 4, 5, 6, 16, 8, 10, 9, 12, 11, 13, 14, 17, 7, 15, 22, 2, 3, 21, 18, 23], ![1, 0, 20, 19, 5, 4, 6, 7, 14, 18, 22, 12, 11, 13, 8, 15, 16, 17, 9, 3, 2, 21, 10, 23], ![1, 0, 18, 10, 4, 5, 6, 7, 14, 20, 3, 11, 12, 21, 8, 17, 16, 15, 2, 22, 9, 13, 19, 23], ![1, 0, 10, 18, 5, 4, 6, 16, 8, 19, 2, 11, 12, 21, 14, 15, 7, 17, 3, 9, 22, 13, 20, 23], ![1, 0, 9, 22, 4, 5, 23, 16, 14, 2, 19, 11, 12, 13, 8, 15, 7, 17, 20, 10, 18, 21, 3, 6], ![1, 0, 22, 9, 5, 4, 23, 7, 8, 3, 20, 11, 12, 13, 14, 17, 16, 15, 19, 18, 10, 21, 2, 6]]]

def quotientProfile : Fin 2 → Fin 24 → ℕ :=
  ![![255, 255, 43605, 43605, 257, 257, 15555, 257, 257, 38505, 26265, 61455, 61455, 52275, 257, 257, 257, 257, 26265, 23205, 23205, 52275, 38505, 15555], ![255, 255, 513, 513, 21845, 21845, 15555, 39321, 42405, 513, 513, 61455, 61455, 52275, 42405, 26985, 39321, 26985, 513, 513, 513, 52275, 513, 15555]]

def quotientBase : Fin 2 → Fin 24 := ![4, 2]

def quotientProbes : Fin 2 → Fin 9 → Fin 24 := ![![0, 4, 5, 7, 8, 14, 15, 16, 17], ![0, 2, 3, 9, 10, 18, 19, 20, 22]]

def quotientProbeWords : Fin 2 → Fin 9 → Fin 16 := ![![0, 0, 1, 5, 2, 3, 7, 4, 6], ![0, 0, 1, 7, 4, 5, 3, 2, 6]]

def quotientProduct (r : Fin 2) (k : Fin 16) : StarGroup :=
  binaryProduct (pairRowGenerator (r.castLE (by decide))) (fun i => k.val.testBit i.val)

theorem quotientProduct_table (r : Fin 2) (k : Fin 16) :
    (fun i => (quotientProduct r k).val i) = quotientProductTable r k := by
  revert r k
  decide +kernel

theorem quotientProduct_mem (r : Fin 2) (k : Fin 16) :
    quotientProduct r k ∈ pairRowImage (r.castLE (by decide)) :=
  binaryProduct_mem _ _ _ (pairRowGenerator_mem _)

private theorem table_square : ∀ r k i,
    quotientProductTable r k (quotientProductTable r k i) = i := by decide +kernel

private theorem profile_detect : ∀ r i j,
    (∀ k, (quotientProductTable r k i = i ↔ quotientProductTable r k j = j)) →
      quotientProfile r i = quotientProfile r j := by decide +kernel

private theorem profile_orbit : ∀ r i j,
    quotientProfile r i = quotientProfile r j → ∃ k, quotientProductTable r k i = j := by
  decide +kernel

private theorem profile_two_points : ∀ r i j,
    quotientProfile r i = quotientProfile r 0 →
    quotientProfile r j = quotientProfile r (quotientBase r) →
    ∃ k, quotientProductTable r k 0 = i ∧ quotientProductTable r k (quotientBase r) = j := by
  decide +kernel

private theorem probes_injective : ∀ r, Function.Injective (quotientProbes r) := by decide +kernel

private theorem probes_word : ∀ r j,
    quotientProductTable r (quotientProbeWords r j)
      (if j = 0 then 0 else quotientBase r) = quotientProbes r j := by decide +kernel

private theorem centralizer_commute (r : Fin 2) (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage (r.castLE (by decide)) : Set StarGroup))
    (k : Fin 16) (i : Fin 24) :
    p.val (quotientProductTable r k i) = quotientProductTable r k (p.val i) := by
  have h := congrArg (fun a : StarGroup => a.val i)
    ((mem_centralizer_iff.mp hp) _ (quotientProduct_mem r k))
  simpa only [coe_mul, Equiv.Perm.mul_apply, ← quotientProduct_table] using h.symm

private theorem centralizer_profile (r : Fin 2) (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage (r.castLE (by decide)) : Set StarGroup))
    (i : Fin 24) : quotientProfile r (p.val i) = quotientProfile r i := by
  apply profile_detect
  intro k
  rw [← centralizer_commute r p hp k i]
  exact p.val.injective.eq_iff

/-- Every commuting permutation has square one; the proof uses the literal
point stabilizers of the row, before the Mathieu involution bound. -/
theorem quotient_centralizer_square (r : Fin 2) (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage (r.castLE (by decide)) : Set StarGroup)) :
    p ^ 2 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨k, hk⟩ := profile_orbit r i (p.val i) (centralizer_profile r p hp i).symm
  change p.val (p.val i) = i
  calc
    p.val (p.val i) = p.val (quotientProductTable r k i) := congrArg p.val hk.symm
    _ = quotientProductTable r k (p.val i) := centralizer_commute r p hp k i
    _ = quotientProductTable r k (quotientProductTable r k i) := congrArg _ hk.symm
    _ = i := table_square r k i

private theorem centralizer_fixes_probes (r : Fin 2) (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage (r.castLE (by decide)) : Set StarGroup))
    (h0 : p.val 0 = 0) (hb : p.val (quotientBase r) = quotientBase r) (j : Fin 9) :
    p.val (quotientProbes r j) = quotientProbes r j := by
  rw [← probes_word r j, centralizer_commute r p hp]
  congr 1
  split_ifs <;> assumption

private theorem mathieu_involution_fixed_card_le (p : Sporadic.Mathieu.M24)
    (hp : orderOf p = 2) :
    (Sporadic.Mathieu.M24ChapterHStabilizers.fixedPoints p).card ≤ 8 := by
  rcases Sporadic.Mathieu.M24InvolutionCentralizers.involution_classes p hp with h | h
  · exact (Sporadic.Mathieu.m24Blocks_card _
      (Sporadic.Mathieu.M24ChapterHStabilizers.class2A_fixed_octad h)).le
  · rw [Sporadic.Mathieu.M24ChapterHStabilizers.class2B_fixed_empty h]
    decide

/-- Point zero and one point in the eight-orbit form a base for the whole
quotient centralizer, using the actual Mathieu involution classes. -/
theorem quotient_centralizer_eq_one_of_fixed (r : Fin 2) (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage (r.castLE (by decide)) : Set StarGroup))
    (h0 : p.val 0 = 0) (hb : p.val (quotientBase r) = quotientBase r) : p = 1 := by
  classical
  by_contra hn
  let q := starGroupEquivM24 p
  have hq : orderOf q = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (quotient_centralizer_square r p hp) hn
  have hfix (j : Fin 9) :
      StarOrderCertificate.relabel (quotientProbes r j) ∈
        Sporadic.Mathieu.M24ChapterHStabilizers.fixedPoints q := by
    rw [Sporadic.Mathieu.M24ChapterHStabilizers.mem_fixedPoints]
    change (starGroupEquivM24 p).val _ = _
    rw [starGroupEquivM24_apply]
    change StarOrderCertificate.relabel (p.val (StarOrderCertificate.relabel.symm
      (StarOrderCertificate.relabel (quotientProbes r j)))) = _
    rw [Equiv.symm_apply_apply, centralizer_fixes_probes r p hp h0 hb]
  let f : Fin 9 → (Sporadic.Mathieu.M24ChapterHStabilizers.fixedPoints q) :=
    fun j => ⟨StarOrderCertificate.relabel (quotientProbes r j), hfix j⟩
  have hf : Function.Injective f := by
    intro i j h
    exact probes_injective r (StarOrderCertificate.relabel.injective (congrArg Subtype.val h))
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_coe] at hc
  have hl := mathieu_involution_fixed_card_le q hq
  omega

/-- Exact full Mathieu quotient centralizers of the two unprimed rows. -/
theorem pairRow_quotient_self_centralizing (r : Fin 2) :
    centralizer (pairRowImage (r.castLE (by decide)) : Set StarGroup) =
      pairRowImage (r.castLE (by decide)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨k, hk0, hkb⟩ := profile_two_points r (p.val 0) (p.val (quotientBase r))
      (centralizer_profile r p hp 0) (centralizer_profile r p hp (quotientBase r))
    let q := quotientProduct r k
    have hq : q ∈ pairRowImage (r.castLE (by decide)) := quotientProduct_mem r k
    have he : p * q⁻¹ = 1 := by
      apply quotient_centralizer_eq_one_of_fixed r
      · exact (centralizer _).mul_mem hp ((centralizer _).inv_mem
          ((pairRowImage _).le_centralizer hq))
      · have hq0 : q.val 0 = p.val 0 := congrFun (quotientProduct_table r k) 0 |>.trans hk0
        have hc := (mem_centralizer_iff.mp hp) q hq
        have hc' : Commute p q := hc.symm
        have hi := hc'.inv_right.eq
        have hv := congrArg (fun a : StarGroup => a.val 0) hi
        change p.val (q.val.symm 0) = q.val.symm (p.val 0) at hv
        change p.val (q.val.symm 0) = 0
        rw [hv, ← hq0, q.val.symm_apply_apply]
      · have hqb : q.val (quotientBase r) = p.val (quotientBase r) :=
          (congrFun (quotientProduct_table r k) _).trans hkb
        have hc : Commute p q := ((mem_centralizer_iff.mp hp) q hq).symm
        have hv := congrArg (fun a : StarGroup => a.val (quotientBase r)) hc.inv_right.eq
        change p.val (q.val.symm (quotientBase r)) = q.val.symm (p.val (quotientBase r)) at hv
        change p.val (q.val.symm (quotientBase r)) = quotientBase r
        rw [hv, ← hqb, q.val.symm_apply_apply]
    exact (mul_inv_eq_one.mp he) ▸ hq
  · exact (pairRowImage _).le_centralizer

end Janko4.LocalStructure.ElementaryEightGeometry
