module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LocalFactors
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.LinearRank
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# The triality upper generation bound

The two local factors, joined with T, generate G. Each is a two-extension
of a group whose quotient by its two-core is PSL₂(q³) or PSL₂(q). In the
nonabelian cases, passing to the solvable-radical quotient gives a simple
generalized Fitting subgroup with that precise PSL₂ model. Faithful
conjugation bounds all elementary actors, including outer actors. The
whole-group E2 calculation and solvable-kernel lifting give bounds 3f and f.

When q = 2 the central-node factor and its two-extension are solvable, so
E.1.13 supplies bound one. Thus E.1.12 proves the upper bound 3f uniformly,
without a generation assumption or an exclusion of outer two-extensions.
The lower obstruction remains a separate part of E.1.14(2).

Source: Aschbacher--Smith E.1.12--14, printed p.214, referring to
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7;
the genuine local quotient calculations are F.1.12(I)(4), pp.263--264.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open ValuesEvenClassical.RankOneUpper
open scoped MatrixGroups

private theorem radical_eq_core_of_simple_quotient {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup (H ⧸ pCore 2 H)] [Group.IsPerfect (H ⧸ pCore 2 H)] :
    solvableRadical H = pCore 2 H := by
  let Q := H ⧸ pCore 2 H
  let q : H →* Q := QuotientGroup.mk' (pCore 2 H)
  have hR : solvableRadical Q = ⊥ := by
    rcases (inferInstance : (solvableRadical Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hs : Group.IsSolvable (⊤ : Subgroup Q) := h ▸ inferInstance
      let := hs
      exact (Group.IsPerfect.not_isSolvable Q
        (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
          Subgroup.topEquiv.surjective)).elim
  apply le_antisymm
  · have h := map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective _)
    rw [hR] at h
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp
      ((Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp h) hx)
  · let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance

private theorem rankOne_two_extension_isEGenerated {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] {d : ℕ} (hd : 2 ≤ d)
    (e : (N ⧸ pCore 2 N) ≃* PSL2Model d) (hq : IsPGroup 2 (H ⧸ N)) :
    IsEGenerated d H := by
  have hc : 4 ≤ Nat.card (GaloisField 2 d) := by
    rw [GaloisField.card 2 d (by omega)]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  let : IsSimpleGroup (PSL2Model d) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hc
  let : Group.IsPerfect (PSL2Model d) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by omega)
  let : IsSimpleGroup (N ⧸ pCore 2 N) := e.isSimpleGroup
  let : Group.IsPerfect (N ⧸ pCore 2 N) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let b := (QuotientGroup.quotientMulEquivOfEq
    (radical_eq_core_of_simple_quotient (H := N))).trans e
  let : IsSimpleGroup (N ⧸ solvableRadical N) := b.isSimpleGroup
  let : Group.IsPerfect (N ⧸ solvableRadical N) :=
    Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have ha := Group.IsPerfect.not_isMulCommutative (N ⧸ solvableRadical N)
  let Q := H ⧸ solvableRadical H
  let c : generalizedFitting Q ≃* PSL2Model d :=
    (radicalTwoExtensionFittingEquiv N ha hq).trans b
  let : IsSimpleGroup (generalizedFitting Q) := radicalTwoExtension_fitting_simple N ha hq
  have hcna := linear_socle_not_isMulCommutative (generalizedFitting Q) c
  apply IsEGenerated.of_solvableRadical_quotient (by omega : 0 < d)
  intro S
  apply linear_isEGeneratedAt_of_top_component hd c (SimpleSocle.centralizer_eq_bot hcna) S
  intro A _ _ hne
  exact eCaseComponent_top hcna S (radicalTwoExtension_fitting_sup_sylow N ha hq S)
    (S : Subgroup Q) A hne

private theorem binary_two_extension_isSolvable {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (e : (N ⧸ pCore 2 N) ≃* PSL2Model 1) (hq : IsPGroup 2 (H ⧸ N)) :
    Group.IsSolvable H := by
  let : Group.IsSolvable (PSL2Model 1) :=
    Theory.PSL2.OuterSolvable.isSolvable_of_card_two (by
      rw [GaloisField.card 2 1 (by decide)]
      rfl)
  let : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 N) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable N :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 N)).mpr ⟨inferInstance, inferInstance⟩
  let : Group.IsNilpotent (H ⧸ N) := hq.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

variable {G : Type*} [Group G] [Finite G] {f : ℕ} {hf : 0 < f}

private def restrictedCoreQuotientEquiv (L T : Subgroup G)
    (e : L ≃* BinaryCarrier f hf) (a : Node) :
    ((ambientLocalFactor L e a).subgroupOf (localOvergroup L T e a)) ⧸
      pCore 2 ((ambientLocalFactor L e a).subgroupOf (localOvergroup L T e a)) ≃*
        ambientLocalFactor L e a ⧸ pCore 2 (ambientLocalFactor L e a) :=
  let b := subgroupOfEquivOfLe (show ambientLocalFactor L e a ≤ localOvergroup L T e a
    from le_sup_left)
  QuotientGroup.congr _ _ b (pCore_map_iso 2 b)

/-- The cubic field gives the rank-3f bound on the actual arms-node T-overgroup. -/
theorem arms_localOvergroup_isEGenerated (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) : IsEGenerated (3 * f) (localOvergroup L T e .arms) := by
  let N := (ambientLocalFactor L e .arms).subgroupOf (localOvergroup L T e .arms)
  let : N.Normal := ambientLocalFactor_normal_in_overgroup L T e he .arms
  exact rankOne_two_extension_isEGenerated N (by omega : 2 ≤ 3 * f)
    ((restrictedCoreQuotientEquiv L T e .arms).trans (armsCoreQuotientEquiv L e))
    (localOvergroup_quotient_isTwoGroup L T e he .arms)

/-- At f=1 this local overgroup is solvable; for f≥2 its simple quotient is PSL₂(2^f). -/
theorem central_localOvergroup_isEGenerated (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) : IsEGenerated f (localOvergroup L T e .central) := by
  let N := (ambientLocalFactor L e .central).subgroupOf (localOvergroup L T e .central)
  let : N.Normal := ambientLocalFactor_normal_in_overgroup L T e he .central
  let b := (restrictedCoreQuotientEquiv L T e .central).trans (centralCoreQuotientEquiv L e)
  have hq := localOvergroup_quotient_isTwoGroup L T e he .central
  by_cases hd : 2 ≤ f
  · exact rankOne_two_extension_isEGenerated N hd b hq
  · have hf1 : f = 1 := by omega
    subst f
    let : Group.IsSolvable (localOvergroup L T e .central) :=
      binary_two_extension_isSolvable N b hq
    exact isEGenerated_one_of_solvable

/-- Both literal proper T-overgroups have the bound needed by E.1.12. -/
theorem localOvergroup_isEGenerated (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    IsEGenerated (3 * f) (localOvergroup L T e a) := by
  cases a
  · exact arms_localOvergroup_isEGenerated L T e he
  · exact (central_localOvergroup_isEGenerated L T e he).mono (by omega)

/-- The full upper bound, including q=2 and every ambient outer two-extension.
Normality and G=LT suffice for this direction; simplicity and SQTK are not needed. -/
theorem isEGenerated_of_triality (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (hf : 0 < f) (hmodel : IsTrialityGroupAt (2 ^ f) L)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) : IsEGenerated (3 * f) G := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L f hf).mp hmodel
  obtain ⟨e, he⟩ := exists_sylow_aligned_equiv L T e
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget (3 * f) T Ω
  rw [← localOvergroups_generate L T e hLT]
  apply sup_le
  · exact ChiefOrbit.overgroup_le_generationTarget T _ le_sup_right hΩ
      (localOvergroup_isEGenerated L T e he .arms)
  · exact ChiefOrbit.overgroup_le_generationTarget T _ le_sup_right hΩ
      (localOvergroup_isEGenerated L T e he .central)

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality
