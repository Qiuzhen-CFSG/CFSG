module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.BorelGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.ActionKernel
public import Theory.SpecificGroups.PSL2.CubicBorelInner
public import Theory.GroupTheory.TwoByThreeDisplacement


/-!
# The Borel-action reduction for the linear rank-one branch

Mutual normalization places each commutator of Y₊ with the Borel in their
intersection. The three-group quotient of Y₊ then makes its image modulo
the Borel two-core three-primary. The latter core is the actual S ∩ L.
An intrinsic cubic detector consequently makes every order-three generator
of Y₊ act innerly on L. Closure and the genuine section kernel give the
published inner-action conclusion.

The linear specialization discharges the Borel geometry from the actual
PSL₂ model and the established characteristic-two calculation. The
intrinsic detector is proved for the actual matrix model and transported
through the supplied PSL₂ equivalence; the final theorem has no additional
automorphism hypothesis.

Source: Aschbacher--Smith, the rank-one paragraph of 15.3.37, printed
p.1135, using 15.3.11(4)--(6) and 15.3.33(1), printed pp.1123 and 1134.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
variable {G : Type*} [Group G] [Finite G] {Yplus S M I L : Subgroup G}

/-- The genuine source Borel has three-primary commutator displacements. -/
theorem Setup.borel_three_primary_displacement (h : Setup Yplus S M I L)
    (hb : ChapterF.Source.RankOneBorelFacts L S)
    (hBY : ChapterF.Source.borel L S ≤ normalizer (Yplus : Set G))
    {y b : G} (hy : y ∈ Yplus) (hmem : b ∈ ChapterF.Source.borel L S) :
    ∃ k : ℕ, ⁅y, b⁆ ^ (3 ^ k) ∈ S ⊓ L := by
  have he : (ChapterF.Source.borel L S).pCoreIn 2 = S ⊓ L := hb.twoCore_eq
  rw [← he]
  exact exists_three_pow_commutator_mem_pCoreIn h.quotient_three
    (le_sup_left.trans (h.borel_invariant hb)) hBY hy hmem

/-- Order-three generation promotes the intrinsic detector to the source section action. -/
theorem Setup.inner_of_borel_cubic_detection (h : Setup Yplus S M I L)
    (hb : ChapterF.Source.RankOneBorelFacts L S)
    (hBY : ChapterF.Source.borel L S ≤ normalizer (Yplus : Set G))
    (hdetect : MulAut.CubicBorelInner L) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L := by
  obtain ⟨P, hP⟩ := h.component_sylow
  have hPL : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hnorm : (normalizer (P : Set L)).map L.subtype = ChapterF.Source.borel L S := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [← hPL, ← subgroupOf_normalizer_eq inf_le_right,
      subgroupOf, map_comap_eq, range_subtype]
    rfl
  have hYL : Yplus ≤ normalizer (L : Set G) := le_sup_left.trans h.normalizes_component
  have hYS : Yplus ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    have he : (ChapterF.Source.borel L S).pCoreIn 2 = S ⊓ L := hb.twoCore_eq
    rw [← he]
    exact (le_sup_left.trans (h.borel_invariant hb)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  let D : Subgroup G := ((MulAut.innerSubgroup L).comap L.normalizerMonoidHom).map
    (normalizer (L : Set G)).subtype
  have hYD : Yplus ≤ D := by
    rw [← h.theta_eq, theta, closure_le]
    intro y hy
    have hyY : y ∈ Yplus := h.theta_eq ▸ subset_closure hy
    have hyL := hYL hyY
    refine ⟨⟨y, hyL⟩, ?_, rfl⟩
    change L.normalizerMonoidHom ⟨y, hyL⟩ ∈ MulAut.innerSubgroup L
    apply hdetect P _
    · have hy3 : (⟨y, hyL⟩ : normalizer (L : Set G)) ^ 3 = 1 := by
        apply Subtype.ext
        change y ^ 3 = 1
        rw [← hy.2, pow_orderOf_eq_one]
      rw [← map_pow, hy3, map_one]
    · intro x hx
      change L.normalizerMonoidHom ⟨y, hyL⟩ x ∈ (P : Subgroup L)
      rw [← hPL]
      change y * (x : G) * y⁻¹ ∈ S ⊓ L
      apply (mem_normalizer_iff.mp (hYS hyY) x).mp
      have hx' := mem_map_of_mem L.subtype hx
      rwa [hP] at hx'
    · intro b hbP
      have hbB : (b : G) ∈ ChapterF.Source.borel L S :=
        hnorm ▸ mem_map_of_mem L.subtype hbP
      obtain ⟨k, hk⟩ := h.borel_three_primary_displacement hb hBY hyY hbB
      refine ⟨k, ?_⟩
      change (L.normalizerMonoidHom ⟨y, hyL⟩ b * b⁻¹) ^ (3 ^ k) ∈ (P : Subgroup L)
      rw [← hPL]
      exact hk
  intro y hy
  obtain ⟨z, hz, he⟩ := hYD hy
  subst y
  exact inner_witness_of_conjugation_inner z.property hz

/-- The linear local geometry discharges the ambient premises of the detector. -/
theorem Setup.linear_inner_of_cubicBorelInner (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n))
    (hdetect : MulAut.CubicBorelInner L) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L := by
  exact h.inner_of_borel_cubic_detection
    (h.rankOne_borel_facts (ChapterF.Source.IsRankOneModel.linear n hn hm))
    (h.linear_borel_identification hodd hcore hn heven hm).2.2 hdetect

/-- The PSL₂ branch of the inner-action deduction in source 15.3.37.
All Borel, coefficient-action and automorphism-coverage premises are discharged. -/
theorem Setup.linear_inner (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L := by
  apply h.linear_inner_of_cubicBorelInner hodd hcore hn heven hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact (Matrix.ProjectiveSpecialLinearGroup.cubicBorelInner F).of_mulEquiv e

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
