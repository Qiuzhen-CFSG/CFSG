module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Source
public import Theory.GroupTheory.PResidual.SylowSupplement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Inheritance

/-!
# Residual and characteristic reductions for the L₂ pushing-up step

The embedded two-residuals of I and LR both equal the selected component L:
L is perfect, relatively normal, and supplemented by a two-group. The core
O₂(I) lies in R = O₂(Y₊S), so LR inherits characteristic two. Its SQTK
hypothesis is inherited from the actual local group I, with the catalogue
parameter retained.

For an application of C.1.26 to I, transport the nonnormality conclusion
15.3.29 along the chosen Sylow embedding P onto S. This excludes both
characteristic alternatives without asserting that characteristic subgroups
of R are characteristic in S. `blockProduct_on_I` is conditional on the
still separate minimal-parabolic argument. It returns the full central
product, rather than identifying L with a block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.6,
B.6.1, C.1.26, and 15.3.27–30, printed pp.112, 132, and 1130–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G]

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro α x hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨e.symm (α (e c)), ?_, e.apply_symm_apply _⟩
  exact characteristic_iff_le_comap.mp hC ((e.trans α).trans e.symm) hc

/-- Transport 15.3.29 along the actual Sylow embedding into I. -/
theorem characteristic_exclusion_transport {S I : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hpush : ∀ A : Subgroup S, A.Characteristic → A ≠ ⊥ →
      ¬ ((A.map S.subtype).subgroupOf I).Normal) :
    ∀ A : Subgroup P, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (P : Subgroup I).subtype).Normal := by
  let e : P ≃* S := ((P : Subgroup I).equivMapOfInjective I.subtype
    I.subtype_injective).trans (MulEquiv.subgroupCongr hP)
  have he (x : P) : ((e x : S) : G) = ((x : I) : G) := rfl
  intro A hA hne hn
  let D := A.map e.toMonoidHom
  have hD : D.Characteristic := characteristic_map_equiv e A hA
  have hDne : D ≠ ⊥ := fun h => hne ((A.map_eq_bot_iff_of_injective e.injective).mp h)
  have hmap : (D.map S.subtype).subgroupOf I = A.map (P : Subgroup I).subtype := by
    ext x
    constructor
    · rintro ⟨s, ⟨a, ha, has⟩, hsx⟩
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact (he a).symm.trans ((congrArg S.subtype has).trans hsx)
    · rintro ⟨a, ha, rfl⟩
      exact ⟨e a, ⟨a, ha, rfl⟩, he a⟩
  exact hpush D hD hDne (hmap.symm ▸ hn)

/-- Perfectness of the selected component excludes every two-group quotient. -/
theorem component_twoPerfect [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) : IsPPerfect 2 c.L := by
  let := component_isPerfect_of_containment d c h.contains
  intro N hN hp
  let := hN
  have hs : Subsingleton (c.L ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (c.L ⧸ N) hp.isNilpotent
  apply top_unique
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

/-- In I = LS the embedded two-residual is literally the chosen component. -/
theorem residual_I_eq_component [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c)
    (hI : I ∈ d.HplusMinimal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    (pResidual 2 I).map I.subtype = c.L := by
  have hYM : d.Yplus ≤ d.M :=
    (h.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left
  have hgen := (lemma_15_3_27_4_of_containment d hI c P hP h.contains hYM).1
  have hn : d.S ≤ normalizer (c.L : Set G) :=
    (le_sup_right.trans hI.1.1.2).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp h.component_normal)
  calc
    (pResidual 2 I).map I.subtype =
        (pResidual 2 (c.L ⊔ d.S : Subgroup G)).map (c.L ⊔ d.S).subtype :=
      congrArg (fun J : Subgroup G => (pResidual 2 J).map J.subtype) hgen
    _ = c.L := embedded_pResidual_join_pGroup c.L d.S (component_twoPerfect d h)
      (d.T.isPGroup'.to_le inf_le_left) hn

/-- The same residual identity for LR, with R exactly O₂(Y₊S). -/
theorem residual_LR_eq_component [Finite G] (d : LocalData G) {I : Subgroup G}
    {c : ComponentWitness d I} (h : Earlier d I c) (hI : I ∈ d.Hplus) :
    (pResidual 2 (c.L ⊔ d.R : Subgroup G)).map (c.L ⊔ d.R).subtype = c.L := by
  have hRI : d.R ≤ I := (pCoreIn_le 2 _).trans hI.1.2
  exact embedded_pResidual_join_pGroup c.L d.R (component_twoPerfect d h)
    (isPGroup_pCoreIn 2 _) (hRI.trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp h.component_normal))

/-- O₂(I) lies in R, using its normality in I and the actual Sylow S. -/
theorem core_I_le_R [Finite G] (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) : I.pCoreIn 2 ≤ d.R := by
  have hcoreS : I.pCoreIn 2 ≤ d.S := hP ▸ pCoreIn_le_sylow I P
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    (hcoreS.trans le_sup_right) (hI.1.2.trans
      (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))

/-- LR inherits the genuine generalized-Fitting equality because it
contains O₂(I). This does not require the unproved Sylow or parabolic step. -/
theorem characteristicTwo_LR [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hI : I ∈ d.Hplus)
    (hf : HasCharacteristicTwo I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    HasCharacteristicTwo (c.L ⊔ d.R) := by
  apply hasCharacteristicTwo_of_centralizer
  exact Stellmacher.characteristicTwo_of_contains_core_in I (c.L ⊔ d.R)
    (centralizer_twoCore_le hf)
    (sup_le (component_le c) ((pCoreIn_le 2 _).trans hI.1.2))
    ((core_I_le_R d hI P hP).trans le_sup_right)

/-- The genuine local catalogue hypothesis passes from I to LR. -/
theorem sqtk_LR [Finite G] {𝒦 : GroupClass.{u}} (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I) (hI : I ∈ d.Hplus)
    (hSQTK : IsSQTK 𝒦 I) : IsSQTK 𝒦 (c.L ⊔ d.R : Subgroup G) := by
  have hle : c.L ⊔ d.R ≤ I := sup_le (component_le c) ((pCoreIn_le 2 _).trans hI.1.2)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp (hSQTK.subgroup _)

/-- The characteristic bridge for an application to I uses only the
actual identification of P with S. Minimal parabolicity remains a separate
geometric obligation; no assertion about characteristic subgroups of R is used. -/
theorem blockProduct_on_I [Finite G] {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (d : LocalData G) {I : Subgroup G} (hSQTK : IsSQTK 𝒦 I)
    (hf : HasCharacteristicTwo I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hpar : ChapterB.IsMinimalParabolicOver P ⊤)
    (hpush : ∀ A : Subgroup d.S, A.Characteristic → A ≠ ⊥ →
      ¬ ((A.map d.S.subtype).subgroupOf I).Normal) :
    Nonempty (ResidualBlockProduct I P) := by
  let : Nontrivial P := sylow_nontrivial_of_minimalParabolic P hpar
  exact blockProduct_of_characteristic_exclusion P (choices.pair P P.isPGroup')
    (source I hSQTK hf P hpar) (characteristic_exclusion_transport P hP hpush)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

end
