module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonRelativePlanes
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.TernaryRankTwo
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.CoverRank.Calculation
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.Algebra.Group.ULift
/-!
# The actual B.1.9 factors in the doubled binary argument

Three independent symmetric-three factors would give an S₃³ section of the
original SQTK cover. A.1.31(1), via the proved complementary-rank theorem,
excludes this: a transposition in the first factor cannot centralize the
independent cubics in the other two. Thus the ambient B.1.9 family has at
most two factors, without assuming rank monotonicity through a quotient.

For a normal subgroup, each minimal-offender Fitting commutator maps to the
same ambient cubic: inclusion and the two orders of three give equality.
The associated S₃ factors also agree under the original inclusion. The
source two-residual therefore normalizes every actual Thompson factor.
Applying the paired-plane supplement puts their full preimages in M,
including the original action kernel. The chosen-module application is in
NonFFSourceDoubledBinaryCubicFactors.

This proves containment of the moved Fitting product and its S₃ factors.
It does not identify that product with the entire three-core. That comparison,
quotient-component exclusions, and final assembly remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of 7.7.3, printed p.707; B.1.9, pp.71–72;
A.1.31(1), pp.27–28, refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCubicFactors
open ChapterB.SourceInduction ChapterB.FittingStructure ChapterB.QuasisimpleSource
universe u v
private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev LS3 := ULift.{u} S3

private def directProduct (A B : Type u) [Group A] [Group B] :
    InternalProduct ((⊤ : Subgroup A).prod (⊥ : Subgroup B))
      ((⊥ : Subgroup A).prod (⊤ : Subgroup B)) where
  equiv := {
    toFun := fun x => (x.1.val.1,x.2.val.2)
    invFun := fun x => (⟨(x.1,1),⟨mem_top _,rfl⟩⟩,⟨(1,x.2),⟨rfl,mem_top _⟩⟩)
    left_inv := by
      rintro ⟨a,b⟩
      exact Prod.ext (Subtype.ext (Prod.ext rfl a.property.2.symm))
        (Subtype.ext (Prod.ext b.property.1.symm rfl))
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  apply_eq := by
    intro a b
    apply Prod.ext
    · change a.val.1 = a.val.1 * b.val.1
      rw [show b.val.1 = 1 from b.property.1,mul_one]
    · change b.val.2 = a.val.2 * b.val.2
      rw [show a.val.2 = 1 from a.property.2,one_mul]

private theorem no_three_symmetric_factors
    {D : Type u} [Group D] [Finite D]
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (f : LS3.{u} × (LS3.{u} × LS3.{u}) →* D) (hf : Function.Injective f) : False := by
  let X := LS3.{u} × (LS3.{u} × LS3.{u})
  let c : SQTKQuotient KnownSimple.IsKnownSimple X :=
    { cover.subgroup f.range with
      equiv := (cover.subgroup f.range).equiv.trans (MonoidHom.ofInjective hf).symm }
  let A : Subgroup X := (⊤ : Subgroup LS3.{u}).prod ⊥
  let B : Subgroup X := (⊥ : Subgroup LS3.{u}).prod ⊤
  let j : S3 →* A := {
    toFun := fun s => ⟨(⟨s⟩,1),⟨mem_top _,rfl⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro s t he
    exact congrArg (fun a : A => a.val.1.down) he
  have hb := FactorExtraction.second_primeRank_le_one_of_symmetricThree
    earlierA131One c (directProduct LS3.{u} (LS3.{u} × LS3.{u})) j hj
  let e : B ≃* (LS3.{u} × LS3.{u}) := {
    toFun := fun b => b.val.2
    invFun := fun b => ⟨(1,b),⟨rfl,mem_top _⟩⟩
    left_inv := fun b => Subtype.ext (Prod.ext b.property.1.symm rfl)
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hpos : 0 < primeRank 3 LS3.{u} := by
    apply Nat.pos_of_ne_zero
    intro he
    apply PrimeRank.eq_zero_iff_not_dvd_card.mp he
    rw [Nat.card_congr (MulEquiv.ulift : LS3.{u} ≃* S3).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [primeRank_equiv 3 e,primeRank_prod_eq_add] at hb
  omega

/-- The B.1.9 cubic family has at most two members on an actual SQTK quotient. -/
theorem cubicCount_le_two_of_cover
    {D : Type u} [Group D] [Finite D]
    {X : Type v} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D) : cubicCount ρ ≤ 2 := by
  classical
  by_contra hn
  have hc : 3 ≤ cubicCount ρ := by omega
  have hl := localPlaneLaw ρ hf hcore
  let e (i : Fin (cubicCount ρ)) := Classical.choice
    (planeGroup_model ρ hf hl (cubicFactor_mem ρ i))
  let q : (Fin (cubicCount ρ) → LS3.{u}) ≃* planeGenerated ρ :=
    (MulEquiv.piCongrRight (fun i =>
      (MulEquiv.ulift : LS3.{u} ≃* S3).trans (e i).symm)).trans (planeProduct ρ hf hl)
  let j : LS3.{u} × (LS3.{u} × LS3.{u}) →* (Fin (cubicCount ρ) → LS3.{u}) := {
    toFun := fun x i => if i.val = 0 then x.1 else if i.val = 1 then x.2.1
      else if i.val = 2 then x.2.2 else 1
    map_one' := by funext i; simp
    map_mul' := by
      intros; funext i
      simp only [Pi.mul_apply]
      split_ifs <;> rfl }
  have hj : Function.Injective j := by
    intro x y he
    have h0 := congrFun he ⟨0,by omega⟩
    have h1 := congrFun he ⟨1,by omega⟩
    have h2 := congrFun he ⟨2,by omega⟩
    simp only [j,MonoidHom.coe_mk,OneHom.coe_mk,↓reduceIte] at h0 h1 h2
    exact Prod.ext h0 (Prod.ext h1 h2)
  exact no_three_symmetric_factors cover
    ((planeGenerated ρ).subtype.comp (q.toMonoidHom.comp j))
    ((planeGenerated ρ).subtype_injective.comp (q.injective.comp hj))

private theorem minimal_map_subtype
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (J : Subgroup D) (A : Subgroup J)
    (hA : IsMinimalBestOffender (ρ.comp J.subtype) A) :
    IsMinimalBestOffender ρ (A.map J.subtype) := by
  refine ⟨hA.1.map_subtype ρ, ?_⟩
  intro B hB hBA
  have hBJ : B ≤ J := hBA.1.trans (map_subtype_le A)
  have hle : B.subgroupOf J ≤ A := by
    intro b hb
    obtain ⟨a,ha,he⟩ := hBA.1 hb
    exact (J.subtype_injective he) ▸ ha
  have hw : weight (ρ.comp J.subtype) (B.subgroupOf J) =
      weight (ρ.comp J.subtype) A := by
    rw [weight_comp_map ρ J.subtype J.subtype_injective,
      weight_comp_map ρ J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hBJ]
    exact hBA.2
  have he := hA.2 _ (hB.subgroupOf ρ hBJ) ⟨hle,hw⟩
  exact (map_subgroupOf_eq_of_le hBJ).symm.trans (congrArg (Subgroup.map J.subtype) he)

private theorem normal_twoCore_eq_bot
    {D : Type*} [Group D] (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal] :
    pCore 2 J = ⊥ := by
  have hl : (pCore 2 J).map J.subtype ≤ pCore 2 D :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map _⟩
  exact (map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    (le_bot_iff.mp (hl.trans_eq hcore))

private theorem fitting_commutator_map
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal]
    (B : Subgroup J) (hB : IsMinimalBestOffender (ρ.comp J.subtype) B)
    (hn : ⁅fittingSubgroup J,B⁆ ≠ ⊥) :
    (⁅fittingSubgroup J,B⁆).map J.subtype = ⁅fittingSubgroup D,B.map J.subtype⁆ := by
  have hB' := minimal_map_subtype ρ J B hB
  have hfit : (fittingSubgroup J).map J.subtype ≤ fittingSubgroup D := by
    apply le_sSup
    exact ⟨ConjAct.normal_of_characteristic_of_normal,
      Group.nilpotent_of_surjective (J.subtype.subgroupMap (fittingSubgroup J))
        (J.subtype.subgroupMap_surjective (fittingSubgroup J))⟩
  have hle : (⁅fittingSubgroup J,B⁆).map J.subtype ≤
      ⁅fittingSubgroup D,B.map J.subtype⁆ := by
    rw [map_commutator]
    exact commutator_mono hfit le_rfl
  have hn' : ⁅fittingSubgroup D,B.map J.subtype⁆ ≠ ⊥ := by
    intro hz
    exact hn ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp
      (le_bot_iff.mp (hle.trans_eq hz)))
  have hJcore : pCore 2 J = ⊥ := by
    have hl : (pCore 2 J).map J.subtype ≤ pCore 2 D :=
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map _⟩
    exact (map_eq_bot_iff_of_injective _ J.subtype_injective).mp
      (le_bot_iff.mp (hl.trans_eq hcore))
  obtain ⟨d⟩ := localPlaneLaw (ρ.comp J.subtype) (hf.comp J.subtype_injective) hJcore B hB hn
  obtain ⟨d'⟩ := localPlaneLaw ρ hf hcore _ hB' hn'
  have he : (⁅fittingSubgroup J,B⁆).map J.subtype =
      ⁅fittingSubgroup D,B.map J.subtype⁆ := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective J.subtype_injective,d.odd_card,d'.odd_card])
  exact he

/-- A cubic factor of a normal subgroup's restricted action is the same
literal cubic factor in the ambient action. Normality is relative to D. -/
theorem minimalMovedFactor_map_normal
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal]
    (A : Subgroup J) (hA : A ∈ minimalMovedFactors (ρ.comp J.subtype)) :
    A.map J.subtype ∈ minimalMovedFactors ρ := by
  obtain ⟨B,hB,hn,rfl⟩ := hA
  have he := fitting_commutator_map ρ hf hcore J B hB hn
  refine ⟨B.map J.subtype,minimal_map_subtype ρ J B hB,?_,he⟩
  rw [← he]
  exact fun hz => hn ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp hz)

/-- The associated symmetric-three group also retains its original inclusion. -/
theorem planeGroup_map_normal
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal]
    (A : Subgroup J) (hA : A ∈ minimalMovedFactors (ρ.comp J.subtype)) :
    (planeGroup (ρ.comp J.subtype) A).map J.subtype =
      planeGroup ρ (A.map J.subtype) := by
  obtain ⟨B,hB,hn,rfl⟩ := hA
  have he := fitting_commutator_map ρ hf hcore J B hB hn
  have hn' : ⁅fittingSubgroup D,B.map J.subtype⁆ ≠ ⊥ := by
    rw [← he]
    exact fun hz => hn ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp hz)
  rw [planeGroup_eq_local (ρ.comp J.subtype) (hf.comp J.subtype_injective)
    (localPlaneLaw _ (hf.comp J.subtype_injective) (normal_twoCore_eq_bot hcore J))
    ⟨hB,hn,rfl⟩,Subgroup.map_sup,he,
    planeGroup_eq_local ρ hf (localPlaneLaw ρ hf hcore)
    ⟨minimal_map_subtype ρ J B hB,hn',rfl⟩]

private theorem offenderSubgroup_normalizes_plane
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) D X) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (A : Subgroup D)
    (hA : A ∈ minimalMovedFactors ρ) :
    offenderSubgroup ρ ≤ normalizer (planeGroup ρ A : Set D) := by
  apply iSup_le
  intro B
  apply iSup_le
  intro hB
  exact BestOffenderNormalization.best_normalizes_plane ρ hf hcore
    (localPlaneLaw ρ hf hcore) hB.1 hA

open ChapterB.InternalThompsonAction DoubledBinaryThompson
open DoubledBinaryThompsonRelativePlanes

/-- The full preimage of the product of the actual Thompson action’s
B.1.9 symmetric-three factors lies in M. The ambient SQTK cover supplies the cubic-count
bound; normal-subgroup transport identifies the literal factors, and the
original plane-containment result supplies every factor's full preimage. -/
theorem thompson_planeGenerated_preimage_contained
    {H : Type u} [Group H] [Finite H]
    (Y : Subgroup H) (hY : IsPReduced 2 Y) (R M : Subgroup H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hR : IsPPerfect 2 R)
    (hcontain : RelativePlaneFactorsContained Y hY R M)
    (hkernel : centralizer (Y : Set H) ≤ M) :
    let := hY.normal
    let := hY.elementary
    ((planeGenerated (thompsonAction Y)).map (thompsonImage Y).subtype).comap
      (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  let J := thompsonImage Y
  let ρ := action Y
  let q := actionMk Y
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic :=
    Stellmacher.elementaryAbelianMaxJ_top_characteristic
  let : J.Normal :=
    (inferInstance : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal).map q hq
  have hc : pCore 2 (ActionQuotient Y) = ⊥ := hY.quotient_pCore_eq_bot
  have hf := action_faithful Y
  have hlocal := localPlaneLaw ρ hf hc
  let cover : SQTKQuotient KnownSimple.IsKnownSimple (ActionQuotient Y) := {
    Cover := H
    kernel := centralizer (Y : Set H)
    sqtk := hH
    equiv := MulEquiv.refl _ }
  have hcount := cubicCount_le_two_of_cover ρ hf hc cover
  have hgen := (thompson_hypothesis Y hH hc).generated
  have hJoff : J ≤ offenderSubgroup ρ := by
    have hl : (offenderSubgroup (thompsonAction Y)).map J.subtype ≤ offenderSubgroup ρ := by
      unfold offenderSubgroup generatedBy
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro A
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro hA
      exact (hA.1.map_subtype ρ).le_offenderSubgroup ρ
    rw [hgen,← MonoidHom.range_eq_map,range_subtype] at hl
    exact hl
  have hRim : IsPPerfect 2 (R.map q) := hR.of_surjective
    (q.subgroupMap R) (q.subgroupMap_surjective R)
  have hfac (A : Subgroup J) (hA : A ∈ minimalMovedFactors (thompsonAction Y)) :
      ((planeGroup (thompsonAction Y) A).map J.subtype).comap q ≤ M := by
    have ha := minimalMovedFactor_map_normal ρ hf hc J A hA
    have he := planeGroup_map_normal ρ hf hc J A hA
    have hs := cubic_fixed_moved_complement ρ hlocal ha
    have hle : planeGroup ρ (A.map J.subtype) ≤ J := he ▸ map_subtype_le _
    rw [he]
    apply hcontain (planeGroup ρ (A.map J.subtype))
    · exact hJoff.trans (offenderSubgroup_normalizes_plane ρ hf hc _ ha)
    · exact (twoPerfect_normalizes_cubic_of_count_le_two ρ hcount _ hRim ha).trans
        (normalizer_le_normalizer_planeGroup ρ _)
    · exact hle
    · rw [show moved ρ (planeGroup ρ (A.map J.subtype)) = moved ρ (A.map J.subtype)
        from planeGroup_support_eq ρ hlocal ha]
      exact (minimalMovedFactors_subset_small ρ hlocal ha).2.2
    · apply top_unique
      rw [← hs.symm.sup_eq_top]
      exact sup_le_sup (planeGroup_support_eq ρ hlocal ha).symm.le
        (planeGroup_fixes_cubic_complement ρ hlocal ha)
  have him : (planeGenerated (thompsonAction Y)).map J.subtype ≤ M.map q := by
    unfold planeGenerated
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro i
    have hh := map_mono (f := q) (hfac _ (cubicFactor_mem (thompsonAction Y) i))
    rwa [map_comap_eq_self_of_surjective hq] at hh
  have hh := comap_mono (f := q) him
  rw [comap_map_eq] at hh
  have hk : q.ker ≤ M := by simpa only [q,actionMk,QuotientGroup.ker_mk'] using hkernel
  exact hh.trans (sup_le le_rfl hk)

/-- In particular the full preimage of the actual moved Fitting subgroup
lies in M, including the centralizer kernel. -/
theorem thompson_fittingMoved_preimage_contained
    {H : Type u} [Group H] [Finite H]
    (Y : Subgroup H) (hY : IsPReduced 2 Y) (R M : Subgroup H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hR : IsPPerfect 2 R)
    (hcontain : RelativePlaneFactorsContained Y hY R M)
    (hkernel : centralizer (Y : Set H) ≤ M) :
    let := hY.normal
    let := hY.elementary
    ((fittingMoved (thompsonAction Y)).map (thompsonImage Y).subtype).comap
      (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  exact (comap_mono (map_mono (fittingMoved_le_planeGenerated (thompsonAction Y)))).trans
    (thompson_planeGenerated_preimage_contained Y hY R M hH hR hcontain hkernel)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCubicFactors
