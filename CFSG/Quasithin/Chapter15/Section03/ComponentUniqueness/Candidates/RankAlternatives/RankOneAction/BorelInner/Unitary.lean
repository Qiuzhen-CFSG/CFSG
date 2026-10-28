module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.ActionKernel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelInner.Unitary.TwoCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelInner.Unitary.TorusRigidity
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelInner.Unitary.Geometry

/-!
# The unitary inner-action branch of 15.3.37

Identify the invariant Borel with M ∩ L and align it with the concrete
root--torus Borel through the actual PSU₃ equivalence. Mutual normalization
with the two-by-three group Y₊ makes each Y₊-actor fix the norm-one torus
modulo the Borel two-core. Root preservation and this fixation eliminate
the field part of its proved semilinear formula. Evenness of the exponent
eliminates the diagonal outer part.

The resulting inner automorphism is transported back to L, and
`ActionKernel.inner_witness_of_conjugation_inner` puts its discrepancy
in the published `Chapter4.sectionCentralizer L`. Thus the conclusion
uses the actual action on L/O₂(L), with no automorphism-coverage or
extra Borel premise. Simplicity is derived from the supplied component
and core hypotheses.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.3.11(4)--(8), 15.3.33(1), and the rank-one paragraph of 15.3.37,
printed pp.1123--1125 and 1134--1135.
-/

public section

open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm

theorem inner_of_standard_borel
    {G : Type*} [Group G] [Finite G] {Y B L : Subgroup G}
    [IsSimpleGroup L]
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hYL : Y ≤ normalizer (L : Set G)) (hBL : B ≤ L)
    (hYB : Y ≤ normalizer (B : Set G)) (hBY : B ≤ normalizer (Y : Set G))
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ n))
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (he : (B.subgroupOf L).map e.toMonoidHom = BorelTorus.projectiveBorel J hJ) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Y L := by
  let K := ProjectiveSpecialUnitaryMatrixGroup J
  let D := BorelTorus.projectiveBorel J hJ
  let : Finite K := Finite.of_surjective e e.surjective
  let : IsSimpleGroup K := e.isSimpleGroup_congr.mp inferInstance
  obtain ⟨_, hcore, hcomm⟩ := standard_borel_facts J hJ (by omega : 0 < n) hcard hconj
  let eB : B ≃* D := (subgroupOfEquivOfLe hBL).symm.trans (BorelTorus.subgroupEquiv e he)
  let eQ := BorelTorus.twoCoreQuotientEquiv eB
  let : IsMulCommutative (D ⧸ pCore 2 D) := hcomm
  let : IsMulCommutative (B ⧸ pCore 2 B) := IsMulCommutative.of_comm (fun x y =>
    eQ.injective (by rw [map_mul, map_mul]; exact mul_comm' _ _))
  intro y hy
  let α : MulAut L := L.normalizerMonoidHom ⟨y, hYL hy⟩
  let β : MulAut B := B.normalizerMonoidHom ⟨y, hYB hy⟩
  let a : MulAut K := MulAut.congr e α
  have hcompat (b : B) : (eB (β b) : K) = a (eB b : K) := by
    change e ⟨y * (b : G) * y⁻¹, _⟩ = e (α (e.symm (e ⟨b, hBL b.property⟩)))
    rw [e.symm_apply_apply]
    rfl
  have hD : D.map a.toMonoidHom = D := by
    apply eq_of_le_of_card_ge _ (card_map_of_injective a.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    change a x ∈ D
    obtain ⟨b, hb⟩ := eB.surjective ⟨x, hx⟩
    have hv : (eB b : K) = x := congrArg Subtype.val hb
    rw [← hv, ← hcompat]
    exact (eB (β b)).property
  have hroot : (BorelTorus.projectiveRoot J hJ).map a.toMonoidHom =
      BorelTorus.projectiveRoot J hJ := by
    rw [← hcore, map_pCoreIn_of_injective 2 _ _ a.injective, hD]
  have ha : a ∈ MulAut.innerSubgroup K := by
    apply inner_of_normOne_displacement J hJ hn heven hcard hconj a hroot
    intro k
    let t : D := ⟨hermitianTorusPSU J hJ k.val,
      (show BorelTorus.projectiveTorus J hJ ≤ D from le_sup_right) ⟨k.val, rfl⟩⟩
    let b : B := eB.symm t
    have ht : (t : K) ^ (2 ^ n + 1) = 1 := by
      change EvenInner.normOneMap J hJ k ^ (2 ^ n + 1) = 1
      rw [← map_pow, ← EvenInner.normOne_card J hcard hconj, pow_card_eq_one', map_one]
    have hbpow : b ^ (2 ^ n + 1) = 1 := by
      apply eB.injective
      apply Subtype.ext
      rw [map_pow, map_one]
      change (eB (eB.symm t) : K) ^ (2 ^ n + 1) = 1
      rw [eB.apply_symm_apply]
      exact ht
    have hcop : Nat.Coprime 3 (orderOf b) :=
      (coprime_three_normOrder heven).of_dvd_right (orderOf_dvd_of_pow_eq_one hbpow)
    have hc := coprime_displacement_mem_twoCore hY hYB hBY hy b hcop
    have hcB : β b * b⁻¹ ∈ pCore 2 B := by
      obtain ⟨z, hz, hez⟩ := hc
      exact (Subtype.ext hez : z = β b * b⁻¹) ▸ hz
    have hcD : eB (β b * b⁻¹) ∈ pCore 2 D := by
      rw [← pCore_map_iso 2 eB]
      exact mem_map_of_mem eB.toMonoidHom hcB
    have hcK := mem_map_of_mem D.subtype hcD
    change (eB (β b * b⁻¹) : K) ∈ D.pCoreIn 2 at hcK
    rw [hcore] at hcK
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hcompat,
      b, eB.apply_symm_apply] using hcK
  apply inner_witness_of_conjugation_inner (hYL hy)
  have hh : a ∈ (MulAut.innerSubgroup L).map (MulAut.congr e).toMonoidHom := by
    rwa [MulAut.map_innerSubgroup_congr]
  obtain ⟨b, hb, heq⟩ := hh
  change α ∈ MulAut.innerSubgroup L
  exact ((MulAut.congr e).injective heq) ▸ hb

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction.BorelInner.Unitary

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
open BorelInner.Unitary

theorem Setup.unitary_inner
    {G : Type*} [Group G] [Finite G] {Yplus S M I L : Subgroup G}
    (h : Setup Yplus S M I L) (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L := by
  let := h.component_simple hodd hcore
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := heven; omega
  obtain ⟨T, hT⟩ := h.component_sylow
  obtain ⟨F, _, _, J, hJ, hcard, hconj, e, he⟩ := exists_standard_borel_equiv hn hm T hT
  obtain ⟨_, hYB, hBY⟩ := h.unitary_borel_identification hodd hcore hn heven hm
  exact inner_of_standard_borel h.quotient_three
    (le_sup_left.trans h.normalizes_component) (show ChapterF.Source.borel L S ≤ L from inf_le_left)
    (le_sup_left.trans hYB) hBY J hJ hn2 heven hcard hconj e he

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
