module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOuterThreeCore
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairModule

/-!
# Symmetric cubics in the actual nonsolvable product alternative

The two source factors are intrinsically permuted by automorphisms. If one
is S₃ and the whole group is nonsolvable, they cannot be interchanged;
that factor and its two-residual are characteristic. The source quotient
summand has dimension two. Odd-order averaging makes its cubic moved space
inject into that quotient, and faithfulness excludes smaller dimensions.
Thus the cubic moves an actual plane in the original module.

For the literal Thompson image this makes the cubic ambient normal, so the
original residual-plane argument contains its full preimage in M. The
other factor models have their residuals in ordinary components. The
original Sylow supplement therefore forces a quotient-component escape
in the nonsolvable two-factor alternative. The actual chosen-module
application is NonFFSourceDoubledBinaryFactorPlanes. The remaining odd-core
case, quotient-component lifting and exclusion, and final assembly stay
with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, B.5.6(3), printed p.105; proof of Proposition
7.7.3, printed p.707, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFactorPlanes
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open HighThreeRank.ModuleCalculation.NaturalCentralizers

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem not_perfect_symmetricThree {A : Type*} [Group A]
    (e : A ≃* Equiv.Perm (Fin 3)) : ¬ Group.IsPerfect A := by
  let := symmetricThree_solvable
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  let : Nontrivial A := e.nontrivial
  intro hp
  let := hp
  exact Group.IsPerfect.not_isSolvable A inferInstance

private theorem factor_plane_dimension
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3)) :
    Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule = 2 := by
  have hp := not_perfect_symmetricThree e
  have three_perfect (F : BinaryField) (f : A ≃* SL(3,F.Carrier)) : False := by
    let : Group.IsPerfect SL(3,F.Carrier) := Atlas.sl_perfect 3 (by decide)
    exact hp (Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective)
  cases h with
  | natural he hn =>
    cases hn with
    | linearTwo F hn =>
      obtain ⟨f⟩ := hn
      have hd : F.degree = 1 := by
        by_contra hne
        have hl : 3 < Nat.card F.Carrier := by
          rw [F.card_eq]
          have htwo : 2 ≤ F.degree := by have := F.degree_pos; omega
          have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) htwo
          norm_num at hpow
          omega
        let : Group.IsPerfect SL(2,F.Carrier) :=
          GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hl
        exact hp (Group.IsPerfect.ofSurjective (f := f.groupEquiv.symm.toMonoidHom)
          f.groupEquiv.symm.surjective)
      have hh := (f.linearEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hd 2).linearEquiv).finrank_eq
      exact hh.trans (show Module.finrank (ZMod 2) (Fin 2 → BinaryField.two.Carrier) = 2 from
        Module.finrank_fin_fun (ZMod 2))
    | symmetricFive hn =>
      obtain ⟨f⟩ := hn
      have hc := Nat.card_congr (e.symm.trans f.groupEquiv).toEquiv
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hc
    | linearThree F _ hn => obtain ⟨f⟩ := hn; exact (three_perfect F f.groupEquiv).elim
  | doubleNatural F _ _ hn => obtain ⟨f⟩ := hn; exact (three_perfect F f.groupEquiv).elim
  | exceptional _ ex => exact (three_perfect BinaryField.two ex.natural.groupEquiv).elim

private theorem odd_plane_of_quotient_bound
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (A : Subgroup D) [A.Normal] (ho : Odd (Nat.card A)) (hn : Nat.card A ≠ 1)
    (U : Subrepresentation ρ) (hU : moved ρ A ≤ U.toSubmodule)
    (hd : Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule ≤ 2) :
    Module.finrank (ZMod 2) (moved ρ A) = 2 := by
  let f : moved ρ A →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule := {
    toFun := fun v => ⟨ρ.invariants.mkQ v,⟨v,hU v.property,rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    have hfix : (v : V) ∈ ρ.invariants :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
    apply Subtype.ext
    exact Submodule.disjoint_def.mp (odd_moved_complement ρ A ho).disjoint
      v v.property (fun a => hfix a)
  have hb := (LinearMap.finrank_le_finrank_of_injective hi).trans hd
  have hdiv := Representation.card_dvd_card_GL_of_injective
    ((normalMoved ρ A).toRepresentation.comp A.subtype) (odd_moved_faithful ρ hf A ho)
  change Nat.card A ∣ Nat.card
    (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) (moved ρ A))) (ZMod 2)) at hdiv
  interval_cases he : Module.finrank (ZMod 2) (moved ρ A)
  · norm_num [he,Matrix.card_GL_field,Fin.prod_univ_succ] at hdiv
    exact (hn (hdiv ▸ Nat.card_unique)).elim
  · rw [Matrix.card_GL_field] at hdiv
    norm_num [Fin.prod_univ_succ] at hdiv
    exact (hn (hdiv ▸ Nat.card_unique)).elim
  · rfl

/-- The actual cubic has a plane as its moved space, before quotienting by fixed vectors. -/
theorem source_factor_cubic_plane
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    {A : Subgroup D} [A.Normal] {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3)) :
    Module.finrank (ZMod 2) (moved ρ ((pResidual 2 A).map A.subtype)) = 2 := by
  let C := (pResidual 2 A).map A.subtype
  let : C.Normal := ConjAct.normal_of_characteristic_of_normal
  have hc : Nat.card C = 3 := by
    rw [card_map_of_injective A.subtype_injective,
      ← card_map_of_injective (K := pResidual 2 A) (f := e.toMonoidHom) e.injective,
      map_pResidual]
    exact Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card
  apply odd_plane_of_quotient_bound ρ hf C (by rw [hc]; decide) (by omega) U
  · exact (Submodule.span_mono (by
      rintro _ ⟨a,ha,v,hv,rfl⟩
      exact ⟨a,map_subtype_le _ ha,v,hv,rfl⟩)).trans h.moved_le_space
  · exact (factor_plane_dimension h e).le

private theorem nonsolvable_symmetric_factor_characteristic
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} (d : SourceTwoFactorCase ρ)
    (hcore : pCore 2 D = ⊥) (hn : ¬ Group.IsSolvable D)
    (e : d.first ≃* Equiv.Perm (Fin 3)) : d.first.Characteristic := by
  let := symmetricThree_solvable
  let : Group.IsSolvable d.first := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  apply characteristic_iff_map_eq.mpr
  intro a
  rcases d.automorphism_permutation hcore a with hh | hh
  · exact hh.1
  · let f : d.first ≃* d.second :=
      (d.first.equivMapOfInjective a.toMonoidHom a.injective).trans (MulEquiv.subgroupCongr hh.1)
    let : Group.IsSolvable d.second := Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
    exact (hn (Group.isSolvable_of_surjective (f := d.product.equiv.toMonoidHom) d.product.equiv.surjective)).elim



open ChapterB.InternalThompsonAction DoubledBinaryThompson
open DoubledBinaryThompsonRelativePlanes

/-- The full inverse image of a symmetric factor's cubic lies in the original M. -/
theorem twoFactor_symmetric_cubic_preimage_contained
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) (hY : IsPReduced 2 Y) (R M : Subgroup H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hplanes : RelativePlaneFactorsContained Y hY R M) :
    let := hY.normal
    let := hY.elementary
    ∀ (d : SourceTwoFactorCase (thompsonAction Y)),
      (¬ Group.IsSolvable (thompsonImage Y)) →
      Nonempty (d.first ≃* Equiv.Perm (Fin 3)) →
      (((pResidual 2 d.first).map d.first.subtype).map (thompsonImage Y).subtype).comap
        (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro d hn he
  obtain ⟨e⟩ := he
  let J := thompsonImage Y
  let C := (pResidual 2 d.first).map d.first.subtype
  let A := C.map J.subtype
  let q := actionMk Y
  have hyp := thompson_hypothesis Y hH hY.quotient_pCore_eq_bot
  let : d.first.Characteristic := nonsolvable_symmetric_factor_characteristic d hyp.twoCore hn e
  let : C.Characteristic := characteristic_of_characteristic_of_characteristic
  let : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic :=
    Stellmacher.elementaryAbelianMaxJ_top_characteristic
  let : J.Normal :=
    (inferInstance : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal).map q
      (QuotientGroup.mk'_surjective _)
  let : A.Normal := ConjAct.normal_of_characteristic_of_normal
  have hd : Module.finrank (ZMod 2) (moved (action Y) A) = 2 := by
    have hh := source_factor_cubic_plane (thompsonAction Y) hyp.faithful d.firstCase e
    change Module.finrank (ZMod 2) (moved ((action Y).comp J.subtype) C) = 2 at hh
    rw [moved,subspaceCommutator_comp_map] at hh
    exact hh
  have ho : Odd (Nat.card A) := by
    rw [card_map_of_injective J.subtype_injective,
      card_map_of_injective d.first.subtype_injective,
      ← card_map_of_injective (K := pResidual 2 d.first) (f := e.toMonoidHom) e.injective,
      map_pResidual,Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card]
    decide
  have hs := odd_moved_complement (action Y) A ho
  exact hplanes A le_normalizer_of_normal le_normalizer_of_normal (map_subtype_le _) hd hs.sup_eq_top

/-- In the actual nonsolvable two-factor alternative an ordinary quotient
component escapes M: all symmetric cubics are already contained. -/
theorem twoFactor_thompson_component_escape
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) (hY : IsPReduced 2 Y) (S : Sylow 2 H) (R M : Subgroup H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hplanes : RelativePlaneFactorsContained Y hY R M)
    (hSM : (S : Subgroup H) ≤ M)
    (hker : centralizer (Y : Set H) ≤ M)
    (hnot : ¬ Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ M) :
    let := hY.normal
    let := hY.elementary
    (¬ Group.IsSolvable (thompsonImage Y)) →
    Nonempty (SourceTwoFactorCase (thompsonAction Y)) →
    ∃ K : Subgroup (thompsonImage Y), IsComponent (thompsonImage Y) K ∧
      IsComponent (ActionQuotient Y) (K.map (thompsonImage Y).subtype) ∧
      ¬ (K.map (thompsonImage Y).subtype).comap (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro hn hd
  obtain ⟨d⟩ := hd
  let J := thompsonImage Y
  let q := actionMk Y
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic :=
    Stellmacher.elementaryAbelianMaxJ_top_characteristic
  let : J.Normal :=
    (inferInstance : (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal).map q hq
  let M' := (M.map q).subgroupOf J
  have hM : M' ≠ ⊤ := by
    intro he
    have hJM : J ≤ M.map q := subgroupOf_eq_top.mp he
    have hh := map_le_iff_le_comap.mp hJM
    rw [comap_map_eq] at hh
    have hk : q.ker ≤ M := by simpa only [q,actionMk,QuotientGroup.ker_mk'] using hker
    exact hnot (hh.trans (sup_le le_rfl hk))
  obtain ⟨P,hP⟩ := (S.mapSurjective hq).exists_subgroupOf_eq_of_normal J
  have hPM : (P : Subgroup J) ≤ M' := by
    rw [hP]
    exact subgroupOf_mono J (map_mono hSM)
  have contained (A : Subgroup J) (ha : (A.map J.subtype).comap q ≤ M) : A ≤ M' := by
    have hh := map_mono (f := q) ha
    rw [map_comap_eq_self_of_surjective hq] at hh
    exact map_le_iff_le_comap.mp hh
  by_contra! hc
  have hK (K : Subgroup J) (hk : IsComponent J K) : K ≤ M' := by
    let := hk.2
    exact contained K (hc K hk ⟨hk.1.trans' (inferInstance : J.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (K.equivMapOfInjective J.subtype J.subtype_injective)⟩)
  let := d.product.second_normal
  let := d.product.swap.second_normal
  have hres : pResidual 2 J ≤ M' := by
    rw [← embedded_pResidual_sup_eq_of_normal_sup_top 2 d.first d.second d.product.sup_eq_top]
    apply sup_le
    · apply DoubledBinaryThompsonEscape.model_residual_contained d.first M' d.firstCase.group_models hK
      intro he
      exact contained _ (twoFactor_symmetric_cubic_preimage_contained Y hY R M hH hplanes d hn he)
    · apply DoubledBinaryThompsonEscape.model_residual_contained d.second M' d.secondCase.group_models hK
      intro he
      let ds : SourceTwoFactorCase (thompsonAction Y) := {
        first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
      exact contained _ (twoFactor_symmetric_cubic_preimage_contained Y hY R M hH hplanes ds hn he)
  exact hM (top_unique ((pResidual_sup_sylow_eq_top P).symm ▸ sup_le hres hPM))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFactorPlanes
