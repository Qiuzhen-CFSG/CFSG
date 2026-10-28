module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationSetup

/-!
# Selecting the fixed-line alternative of C.1.34

The original four-space V lies in Z([O₂(LR),L]). Hence the natural
centers in cases (1) and (3) are too small. Case (2) has no fixed vector,
whereas V has a nontrivial fixed line. In case (4), the central four-group
would lie in Ω₁Z(T), whose order is two in the escape branch. Thus case
(5) holds, and its cardinality identifies the actual commutator with V.

This comparison takes the full five-way classification as an explicit
hypothesis. It does not assume either desired centralizer product.
Source: Aschbacher--Smith C.1.34, pp.136--137; proof of 12.4.6, p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
private theorem section_card {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] {Q C : Subgroup G} {a : L →* A}
    {rho : Representation (ZMod 2) A W} (h : HasSectionModel L Q C a rho) :
    Nat.card Q = Nat.card W * Nat.card C := by
  obtain ⟨hCQ, _, _, hn, e, _⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (C.subgroupOf Q),
    Nat.card_congr e.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv]
  rfl

omit [Finite G] in
private theorem section_fixed_eq_bot {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] {Q : Subgroup G} {a : L →* A}
    {rho : Representation (ZMod 2) A W} (ha : Function.Surjective a)
    (hf : OneCohomology.fixed rho = ⊥)
    (h : HasSectionModel L Q ⊥ a rho) : Q ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨_, _, _, hn, e, he⟩ := h
  apply bot_unique
  intro x hx
  let q : Q := ⟨x, hx.1⟩
  have hfix : (e (QuotientGroup.mk' _ q)).toAdd ∈ OneCohomology.fixed rho := by
    intro g
    obtain ⟨l,rfl⟩ := ha g
    exact (he l q q (mul_inv_eq_iff_eq_mul.mpr (hx.2 l l.property)).symm).symm
  rw [hf] at hfix
  have heq : e (QuotientGroup.mk' _ q) = 1 :=
    Multiplicative.toAdd.injective hfix
  have hq : q ∈ (⊥ : Subgroup G).subgroupOf Q :=
    (QuotientGroup.eq_one_iff q).mp (e.map_eq_one_iff.mp heq)
  exact hq

private theorem natural_pair_fixed :
    OneCohomology.fixed ((specialLinearNatural (k := ZMod 2) 3).prod
      (specialLinearNatural (k := ZMod 2) 3)) = ⊥ := by
  apply bot_unique
  intro v hv
  have h₁ : v.1 ∈ OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) :=
    fun g => congrArg Prod.fst (hv g)
  have h₂ : v.2 ∈ OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) :=
    fun g => congrArg Prod.snd (hv g)
  rw [OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at h₁ h₂
  exact Prod.ext h₁ h₂

/-- The genuine fifth alternative, retaining its common quotient and action marking. -/
def FixedMSAlternative (L R S : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop :=
  let Q := msQ L R
  let C := Q ⊓ centralizer (L : Set G)
  Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    Nonempty (C ≃* Multiplicative (ZMod 2)) ∧
    HasSectionModel L Q C (linearThreeActor e) (specialLinearNatural (k := ZMod 2) 3) ∧
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn S ≤
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (L ⊔ R) ∧
    MSPointStabilizer L R S

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- Compare all five alternatives on the original chosen indecomposable module. -/
theorem ms_fixed_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (halt : MSModuleAlternatives L d.R T 1 (ZMod 2) e) :
    FixedMSAlternative L d.R T e ∧ msQ L d.R = V := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hVc := module_card_sixteen ext hne
  have hVQ := d.module_le_msQ ext h hTV
  have hVZ := d.module_le_ms_center ext h hTV
  have ha : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hq : msQ L d.R ≤ (L ⊔ d.R).pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp
      (le_sup_left.trans ((L ⊔ d.R).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (L ⊔ d.R) (pCore 2 _))))
  have hQT : msQ L d.R ≤ (T : Subgroup G) := by
    rw [d.ms_core_eq ext h hTV] at hq
    exact hq.trans inf_le_left
  have hlast : FixedMSAlternative L d.R T e := by
    rcases halt with h₁ | h₂ | h₃ | h₄ | h₅
    · have hc := section_card h₁.2.2
      have hv := card_le_of_le hVQ
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, card_bot, mul_one] at hc
      rw [hVc, hc] at hv
      norm_num at hv
    · have hz := section_fixed_eq_bot ha natural_pair_fixed h₂.1
      apply (hne (bot_unique ?_)).elim
      exact (inf_le_inf_right _ hVQ).trans hz.le
    · have hc := section_card h₃.1
      have hv := card_le_of_le hVZ
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, card_bot, mul_one] at hc
      rw [hVc, hc] at hv
      norm_num at hv
    · let C := msQ L d.R ⊓ centralizer (L : Set G)
      let _ : IsElementaryAbelian 2 C := h₄.1
      have hCZ : C ≤ Subgroup.omegaCenterIn (T : Subgroup G) := by
        intro x hx
        refine (mem_omegaCenterIn_iff _ _).mpr
          ⟨hQT hx.1, ?_, elemPow_eq_one_of_isElementaryAbelian x hx⟩
        intro t ht
        obtain ⟨z,hz,he⟩ := h₄.2.2.1 hx
        have htJ : t ∈ L ⊔ d.R := by
          rw [d.ms_join_eq ext h hTV]
          exact mem_sup_right ht
        have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨t,htJ⟩)
        change (z : G) = x at he
        change t * (z : G) = (z : G) * t at hc
        exact he ▸ hc
      have hc := card_le_of_le hCZ
      have hz := (d.escape_geometry h structural marked hmodel hne hescape).2.1
      rw [h₄.2.1, hz] at hc
      norm_num at hc
    · exact h₅
  refine ⟨hlast, eq_of_le_of_card_ge hVQ ?_ |>.symm⟩
  have hc := section_card hlast.2.2.1
  obtain ⟨eC⟩ := hlast.2.1
  have hC : Nat.card (msQ L d.R ⊓ centralizer (L : Set G) : Subgroup G) = 2 :=
    (Nat.card_congr eC.toEquiv).trans (Nat.card_zmod 2)
  rw [hc, Nat.card_fun, Nat.card_zmod, Nat.card_fin, hC, hVc]
  norm_num

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
