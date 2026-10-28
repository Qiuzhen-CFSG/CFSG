module

public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic

/-!
# The prime-field outer quotient and four-group intersections

Semilinear coverage over a field of prime cardinality has trivial field part:
transport a coefficient automorphism along an actual prime-field isomorphism.
The literal PGL₂ action is therefore bijective, and its canonical PSL₂ image
maps to the inner automorphism subgroup. The known index-two calculation
then proves that every elementary subgroup of order four contains an inner
involution. Faithfulness of conjugation lifts it to an involution in PSL₂.

This discharges the phrase "containing inner elements" for the prime-field
four-groups in Guralnick--Malle, *Classification of 2F-modules I*, Proposition
4.1, manuscript pp.8--9 (Aschbacher--Smith K.2, printed p.453).
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The actual projective-linear action covers every automorphism over a field
of prime cardinality. In particular there is no coefficient-field factor. -/
theorem prime_card_pgl_coverage (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (hK : IsOddPrimePower (Nat.card F)) (hc : 3 < Nat.card F) :
    Function.Surjective (pgl2InnerAutPSL2 F hK hc) := by
  classical
  intro a
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective F
    (p := p) (f := 1) (by simpa using hF) hK hc a
  let : Fintype F := Fintype.ofFinite F
  let e : ZMod p ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF])
  have hs : x.right = 1 := by
    have he : e.trans x.right = e := Subsingleton.elim _ _
    ext z
    obtain ⟨y, rfl⟩ := e.surjective z
    exact congrArg (fun k : ZMod p ≃+* F => k y) he
  refine ⟨x.left, ?_⟩
  have he : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hs
  rw [he, pGammaL2ToMulAutPSL2_inl] at hx
  exact hx

/-- Over every prime-cardinality field of order greater than three, the inner
automorphism group of PSL₂ has index two. -/
theorem prime_card_inner_index (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p) (hF : Nat.card F = p) :
    (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range.index = 2 := by
  classical
  let hK : IsOddPrimePower (Nat.card F) := ⟨p, 1, Fact.out, hp, by omega, by simpa using hF⟩
  have hc : 3 < Nat.card F := by omega
  let f := pgl2InnerAutPSL2 F hK hc
  have hsurj : Function.Surjective f := prime_card_pgl_coverage F hF hK hc
  let j : PSL(2, F) →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hcomp : f.comp j = MulAut.conj := by
    apply MonoidHom.ext
    intro x
    exact pgl2InnerAutPSL2_toPGL F hK hc x
  have hmap : j.range.map f = (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range := by
    rw [← MonoidHom.range_comp, hcomp]
  rw [← hmap, index_map_of_bijective ⟨pgl2InnerAutPSL2_injective F hK hc, hsurj⟩]
  exact pgl2_psl2Range_index_eq_two F hK

/-- An elementary four-group of automorphisms contains conjugation by an
actual nonidentity involution, including when the four-group has outer elements. -/
theorem fourGroup_has_inner_involution (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p) (hF : Nat.card F = p)
    (A : Subgroup (MulAut PSL(2, F))) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4) :
    ∃ t : PSL(2, F), t ≠ 1 ∧ t ^ 2 = 1 ∧ MulAut.conj t ∈ A := by
  let I := (MulAut.conj : PSL(2, F) →* MulAut PSL(2, F)).range
  have hindex : I.index = 2 := prime_card_inner_index F hp hlarge hF
  let : I.Normal := I.normal_of_index_eq_two hindex
  have hd : I.relIndex A ∣ 2 := by simpa only [hindex] using I.relIndex_dvd_index_of_normal A
  have hc := (I.subgroupOf A).card_mul_index
  rw [hcard] at hc
  have hnontriv : 1 < Nat.card (I.subgroupOf A) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hd | hd
    all_goals
      change (I.subgroupOf A).index = _ at hd
      rw [hd] at hc
      omega
  let : Fintype (I.subgroupOf A) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
    (by simpa only [← Nat.card_eq_fintype_card] using hnontriv) (1 : I.subgroupOf A)
  obtain ⟨t, ht⟩ := a.property
  have hta : MulAut.conj t ∈ A := ht ▸ a.val.property
  have ht1 : t ≠ 1 := by
    intro ht1
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    simpa [ht1] using ht.symm
  have hinj := Theory.GroupTheory.conj_injective_of_center_eq_bot (psl2_center_eq_bot F)
  refine ⟨t, ht1, hinj ?_, hta⟩
  let : IsElementaryAbelian 2 A := hA
  simpa only [map_pow, map_one] using elemPow_eq_one_of_isElementaryAbelian (MulAut.conj t) hta

end Theory.PSL2
