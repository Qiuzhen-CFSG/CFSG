module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFactorPlanes
public import Theory.GroupTheory.PCoreProduct

/-!
# The full three-core in the hyperplane Thompson alternative

The first SL₃(2) factor has trivial three-core. A nontrivial three-core
therefore forces the second factor to be SL₂(2), with its literal reduced
second-space action. Odd averaging makes the original three-core moved
space inject into that reduced quotient. Faithfulness and the orders of
GL₀(2) and GL₁(2) then force its dimension to be two.

The three-core is characteristic in the normal Thompson image, so this
actual plane actor is normal in the whole centralizer quotient. The proved
residual-plane argument contains its full inverse image in M, including
the action kernel. NonFFSourceDoubledBinaryHyperplane applies this to the
original chosen doubled orbit. Quotient-component exclusion, ambient
containment and final non-FF assembly remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, B.5.6(5), printed p.105; proof of Proposition
7.7.3, printed p.707, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryHyperplane
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open HighThreeRank.ModuleCalculation.NaturalCentralizers

private theorem simple_perfect_core {A : Type*} [Group A] [Finite A]
    [IsSimpleGroup A] [Group.IsPerfect A] : pCore 3 A = ⊥ := by
  rcases (inferInstance : (pCore 3 A).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hp : IsPGroup 3 A := (ht ▸ (pCore_isPGroup : IsPGroup 3 (pCore 3 A))).of_equiv topEquiv
    let : Group.IsNilpotent A := hp.isNilpotent
    exact (Group.IsPerfect.not_isSolvable A inferInstance).elim

private theorem linear_three_core {A : Type*} [Group A] [Finite A]
    (e : A ≃* SL(3,ZMod 2)) : pCore 3 A = ⊥ := by
  let : IsSimpleGroup PSL(3,ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  let : IsSimpleGroup A := (e.trans
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv
      BinaryField.two.card_eq (by decide))).isSimpleGroup
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact simple_perfect_core

private theorem linear_two_core {A : Type*} [Group A] [Finite A]
    (F : BinaryField) (hn : F.degree ≠ 1) (e : A ≃* SL(2,F.Carrier)) :
    pCore 3 A = ⊥ := by
  have hl : 3 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hd : 2 ≤ F.degree := by have := F.degree_pos; omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at hp
    omega
  let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Group.IsPerfect SL(2,F.Carrier) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hl
  let : IsSimpleGroup A := (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact simple_perfect_core

private theorem product_core {D : Type*} [Group D] [Finite D]
    {A B : Subgroup D} (d : InternalProduct A B) (hA : pCore 3 A = ⊥) :
    pCore 3 D = (pCore 3 B).map B.subtype := by
  rw [← pCore_map_iso 3 d.equiv, pCore_prod, hA]
  apply le_antisymm
  · rintro x ⟨⟨a,b⟩,hab,rfl⟩
    have ha : a = 1 := hab.1
    change d.equiv (a,b) ∈ _
    rw [d.apply_eq,ha]
    simpa only [OneMemClass.coe_one,one_mul,subtype_apply] using mem_map_of_mem B.subtype hab.2
  · rintro x ⟨b,hb,rfl⟩
    refine ⟨(1,b),⟨one_mem _,hb⟩,?_⟩
    change d.equiv (1,b) = _
    simp only [d.apply_eq,OneMemClass.coe_one,one_mul,subtype_apply]

/-- A nontrivial three-core in the hyperplane row comes from its binary
rank-one factor, with the literal reduced second-space action. -/
theorem hyperplane_threeCore_reduction
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (d : HyperplaneCase ρ)
    (hn : pCore 3 D ≠ ⊥) :
    pCore 3 D ≤ d.second ∧
      ∃ F : BinaryField, F.degree = 1 ∧
        IsLinearNatural (reducedAction (d.secondSpace.toRepresentation.comp d.second.subtype)) F 2 := by
  have he := product_core d.product (linear_three_core d.firstEquiv)
  refine ⟨he.trans_le (map_subtype_le _),?_⟩
  have hn' : pCore 3 d.second ≠ ⊥ := by
    intro hb
    exact hn (by rw [he,hb,Subgroup.map_bot])
  cases d.secondCase with
  | linearThree r hr h =>
    obtain ⟨e⟩ := h
    exact (hn' (linear_three_core e.groupEquiv)).elim
  | linearTwo F h =>
    refine ⟨F,?_,h⟩
    by_contra hd
    obtain ⟨e⟩ := h
    exact hn' (linear_two_core F hd e.groupEquiv)


private theorem odd_plane_of_reduced_bound
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (A B : Subgroup D) [A.Normal] (hAB : A ≤ B)
    (ho : Odd (Nat.card A)) (hn : A ≠ ⊥)
    (U : Subrepresentation ρ) (hU : moved ρ A ≤ U.toSubmodule)
    (hd : Module.finrank (ZMod 2)
      (U.toSubmodule ⧸ (fixed (U.toRepresentation.comp B.subtype)).toSubmodule) ≤ 2) :
    Module.finrank (ZMod 2) (moved ρ A) = 2 := by
  let σ : Representation (ZMod 2) B U.toSubmodule := U.toRepresentation.comp B.subtype
  let i : moved ρ A →ₗ[ZMod 2] U.toSubmodule := Submodule.inclusion hU
  let f := σ.invariants.mkQ.comp i
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    have hfix : i v ∈ σ.invariants := (Submodule.Quotient.mk_eq_zero _).mp hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp (odd_moved_complement ρ A ho).disjoint
      v v.property (fun a => congrArg Subtype.val (hfix ⟨a,hAB a.property⟩))
  have hb := (LinearMap.finrank_le_finrank_of_injective hi).trans hd
  have hdiv := Representation.card_dvd_card_GL_of_injective
    ((normalMoved ρ A).toRepresentation.comp A.subtype) (odd_moved_faithful ρ hf A ho)
  change Nat.card A ∣ Nat.card
    (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) (moved ρ A))) (ZMod 2)) at hdiv
  have hncard : Nat.card A ≠ 1 := by
    intro he
    exact hn ((Subgroup.card_eq_one).mp he)
  interval_cases he : Module.finrank (ZMod 2) (moved ρ A)
  · norm_num [he,Matrix.card_GL_field,Fin.prod_univ_succ] at hdiv
    exact (hncard (hdiv ▸ Nat.card_unique)).elim
  · rw [Matrix.card_GL_field] at hdiv
    norm_num [Fin.prod_univ_succ] at hdiv
    exact (hncard (hdiv ▸ Nat.card_unique)).elim
  · rfl

/-- The nontrivial full three-core in the hyperplane row moves a plane in
the original module, including its nonsplit hyperplane extension. -/
theorem hyperplane_threeCore_plane
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (d : HyperplaneCase ρ) (hn : pCore 3 D ≠ ⊥) :
    Module.finrank (ZMod 2) (moved ρ (pCore 3 D)) = 2 := by
  obtain ⟨hCB,F,hF,⟨e⟩⟩ := hyperplane_threeCore_reduction ρ d hn
  have ho : Odd (Nat.card (pCore 3 D)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 D)).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  apply odd_plane_of_reduced_bound ρ hf (pCore 3 D) d.second hCB ho hn d.secondSpace
  · rw [d.secondSpace_eq]
    exact Submodule.span_mono (by
      rintro _ ⟨a,ha,v,hv,rfl⟩
      exact ⟨a,hCB ha,v,hv,rfl⟩)
  · have hh := (e.linearEquiv.trans
      (ExtensionConsequences.degreeOneNaturalEquiv F hF 2).linearEquiv).finrank_eq
    exact (hh.trans (Module.finrank_fin_fun (ZMod 2))).le

open ChapterB.InternalThompsonAction DoubledBinaryThompson
open DoubledBinaryThompsonRelativePlanes

/-- The full three-core preimage, including the centralizer kernel, is
contained in M in the hyperplane alternative of the actual Thompson image. -/
theorem hyperplane_thompson_threeCore_preimage_contained
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) (hY : IsPReduced 2 Y) (R M : Subgroup H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hplanes : RelativePlaneFactorsContained Y hY R M)
    (hker : centralizer (Y : Set H) ≤ M) :
    let := hY.normal
    let := hY.elementary
    Nonempty (HyperplaneCase (thompsonAction Y)) →
      ((pCore 3 (thompsonImage Y)).map (thompsonImage Y).subtype).comap
        (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro hc
  obtain ⟨c⟩ := hc
  let J := thompsonImage Y
  let A := (pCore 3 J).map J.subtype
  let q := actionMk Y
  change ((pCore 3 J).map J.subtype).comap q ≤ M
  by_cases hn : pCore 3 J = ⊥
  · simpa only [hn,Subgroup.map_bot,MonoidHom.comap_bot,q,actionMk,QuotientGroup.ker_mk'] using hker
  let : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic :=
    Stellmacher.elementaryAbelianMaxJ_top_characteristic
  let : J.Normal :=
    (inferInstance : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal).map q
      (QuotientGroup.mk'_surjective _)
  let : A.Normal := ConjAct.normal_of_characteristic_of_normal
  have hd : Module.finrank (ZMod 2) (moved (action Y) A) = 2 := by
    have hh := hyperplane_threeCore_plane (thompsonAction Y)
      (thompson_hypothesis Y hH hY.quotient_pCore_eq_bot).faithful c hn
    change Module.finrank (ZMod 2)
      (moved ((action Y).comp J.subtype) (pCore 3 J)) = 2 at hh
    rw [moved,subspaceCommutator_comp_map] at hh
    exact hh
  have ho : Odd (Nat.card A) := by
    rw [card_map_of_injective J.subtype_injective]
    obtain ⟨n,hn⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 J)).exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hs := odd_moved_complement (action Y) A ho
  exact hplanes A le_normalizer_of_normal le_normalizer_of_normal (map_subtype_le _) hd hs.sup_eq_top

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryHyperplane
