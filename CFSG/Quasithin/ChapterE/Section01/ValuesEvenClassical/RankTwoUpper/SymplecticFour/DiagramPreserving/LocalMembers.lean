module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Nonbinary
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupAction.ModelConjugation
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank

/-!
# The actual E-members in symplectic local two-extensions

A local factor joined with a normalizing Sylow subgroup need not be perfect.
Its perfect normal factor, however, is both residuals. The radical of the
join is its two-core, and the radical quotient has a faithful normal SL₂
component with two-group quotient. The component's local tau orbit is a
singleton and every nontrivial quotient actor has full commutator with it.
The full SL₂ automorphism rank bound includes the outer field action.

These calculations give E-members in the literal local join whenever the
actor survives its core. Otherwise the weak closure lies in that core and
the entire join normalizes it. No perfectness of the join is assumed.

Source: Aschbacher--Smith E.1.1--5 and E.1.14(1), printed pp.209--211, 214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.DiagramPreserving
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Both the literal component case and the radical-quotient rank bound for
a two-extension of a perfect local SL₂ cover. -/
theorem component_and_rank {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (T A K : Subgroup G) (hAK : A ≤ K) [IsElementaryAbelian 2 A]
    (D : Subgroup K) [D.Normal] [Group.IsPerfect D]
    (e : (D ⧸ pCore 2 D) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : IsPGroup 2 (K ⧸ D)) (hA : ¬ A.subgroupOf K ≤ pCore 2 K) :
    ECaseComponent T A K ∧
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) ≤ f := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hf)
  let := Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple hcard
  let : IsSimpleGroup (D ⧸ pCore 2 D) := e.isSimpleGroup
  have hRD := PerfectCoreTwoExtension.radical_eq_core (G := D)
  have hRK := PerfectCoreTwoExtension.extension_radical_eq_core D hq
  let Q := K ⧸ solvableRadical K
  let q := QuotientGroup.mk' (solvableRadical K)
  let C := D.map q
  let : C.Normal := (inferInstance : D.Normal).map q (QuotientGroup.mk'_surjective _)
  let c : C ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (normalRadicalQuotientEquivImage D).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hRD).trans e)
  let : IsSimpleGroup C := c.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap D) (q.subgroupMap_surjective D)
  have hz : center C = ⊥ := by
    rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple C := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hqC : IsPGroup 2 (Q ⧸ C) := normal_radical_image_two_quotient D hq
  have hcentral : centralizer (C : Set Q) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient C (Group.IsPerfect.not_isMulCommutative C)
      hqC (SimpleSocle.pCore_eq_bot solvableRadical_quotient_solvableRadical 2)
  have hcomp : IsComponent Q C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  have hlayer := (SimpleSocle.layer_residuals C hqC).1
  obtain ⟨hp, hs⟩ := PerfectCoreTwoExtension.residuals D hq
  let a := (A.subgroupOf K).map q
  have ha : a ≠ ⊥ := by
    intro he
    apply hA
    simpa only [q, QuotientGroup.ker_mk', hRK] using (Subgroup.map_eq_bot_iff _).mp he
  constructor
  · refine ⟨?_, ?_, hp.trans hs.symm, C, hcomp, ?_, Or.inl ?_⟩
    · rw [hRK]
      let P : Sylow 2 (pCore 2 K) :=
        (pCore_isPGroup.to_subgroup ⊤).toSylow (by simp)
      exact ⟨P, inferInstanceAs (⊤ : Subgroup (pCore 2 K)).Normal⟩
    · change HasTwoGroupQuotient (componentLayer Q)
      rw [hlayer]
      exact ⟨inferInstance, hqC⟩
    · rw [RankOneUpper.conjugateJoin_eq_of_normal, hlayer]
    · exact SimpleSocle.commutator_eq C hcentral a ha
  · let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
    let : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
    let ρ := Theory.GroupAction.ModelConjugation.action a C
      (le_normalizer_of_normal (H := C) (K := a)) c
    have hi : Function.Injective ρ := by
      apply (MonoidHom.ker_eq_bot_iff ρ).mp
      rw [Theory.GroupAction.ModelConjugation.action_ker, hcentral, bot_subgroupOf]
    let : IsElementaryAbelian 2 ρ.range :=
      IsElementaryAbelian.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    calc
      Group.rank a = Group.rank ρ.range := Group.rank_congr (MonoidHom.ofInjective hi)
      _ ≤ primeRank 2 (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) :=
        ρ.range.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 _)
      _ ≤ f := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hf hF

/-- The local overgroup is generated either through an E-member or through
the weak-closure normalizer. Its quotient by the perfect factor may be nontrivial. -/
theorem local_le_generated {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (T : Sylow 2 G) (K : Subgroup G) (hTK : (T : Subgroup G) ≤ K)
    (D : Subgroup K) [D.Normal] [Group.IsPerfect D]
    (e : (D ⧸ pCore 2 D) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : IsPGroup 2 (K ⧸ D))
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω) :
    K ≤ eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  have hcore : (pCore 2 K).map K.subtype ≤ T := by
    have h := (pCore_isPGroup (p := 2) (G := K)).le_sylow_of_normal (T.subtype hTK)
    exact (map_mono h).trans (by simp [map_subgroupOf_eq_of_le hTK])
  have hnorm : K ≤ normalizer ((pCore 2 K).map K.subtype : Set G) := by
    intro k hk
    apply le_normalizer_map K.subtype
    exact ⟨⟨k, hk⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  apply local_le_eFamily_sup_normalizer (T : Subgroup G) K _ hcore hnorm _ Ω hΩ
  intro A hA hAT hAQ
  let := hA
  have hAK := hAT.trans hTK
  have hne : ¬ A.subgroupOf K ≤ pCore 2 K := by
    intro h
    apply hAQ
    rw [← map_subgroupOf_eq_of_le hAK]
    exact map_mono h
  obtain ⟨hc, hr⟩ := component_and_rank hF hf (T : Subgroup G) A K hAK D e hq hne
  exact ⟨⟨hA, hAT, hAK, le_inf (tau_le _ _) ((tau_le _ _).trans hTK),
    ⟨T.subtype hTK, rfl⟩, Or.inr hc⟩, Or.inr ⟨hc, hr⟩⟩

/-- Apply the complete local calculation to the literal join of a perfect
SL₂ local factor and a normalizing Sylow two-subgroup. -/
theorem join_le_generated {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (T : Sylow 2 G) (D : Subgroup G) [Group.IsPerfect D]
    (hnorm : (T : Subgroup G) ≤ normalizer (D : Set G))
    (e : (D ⧸ pCore 2 D) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω) :
    D ⊔ (T : Subgroup G) ≤ eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  let K := D ⊔ (T : Subgroup G)
  let N := D.subgroupOf K
  let d : N ≃* D := subgroupOfEquivOfLe (show D ≤ K from le_sup_left)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hnorm)
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let eN : (N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e
  have hsup : N ⊔ (T : Subgroup G).subgroupOf K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ K from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  exact local_le_generated hF hf T K le_sup_right N eN
    (isPGroup_quotient_of_sup_eq_top N _ T.isPGroup'.comap_subtype hsup) Ω hΩ

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.DiagramPreserving
