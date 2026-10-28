module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Field
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Selection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Localization
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Ratio
/-!
# The maximum elementary field witness on the original seed

The natural actor coordinates extend to the whole centralizer quotient.
Its Sylow image and perfect seed both centralize the Thompson transposition,
so the five-letter calculation supplies an outer seed transposition in that
Sylow image. Equality of the original two-ranks permits a maximum elementary
lift. Kernel conjugacy puts this lift in the original Sylow while preserving
its image. Normalization of the original L1 and the involutory semilinear
calculation then give the literal field-action equation.

The chosen-flag consumer discharges the FF and Sylow-normalization inputs.
The earlier actual L1/O2(L1) marking remains explicit for upstream discharge.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher Equiv
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Removing the actor restriction retains the very same transposition coordinates. -/
theorem thompsonImage_map_quotientEquiv (htop : offenderGroup E = ⊤)
    (t : MovedSection (action E) (componentImage E))
    (a : MarkedActionEquiv t.space.toRepresentation (offenderGroup E) (componentImage E)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    (thompsonImage E).map (quotientEquiv E htop t a).toMonoidHom =
      ((thompsonImage E).subgroupOf (offenderGroup E)).map a.action.groupEquiv.toMonoidHom := by
  conv_lhs => rw [←map_subgroupOf_eq_of_le (thompsonImage_le_offenders E),map_map]
  rfl

/-- The marked seed has an outer transposition in the literal Sylow image. -/
theorem exists_outer_transposition
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (c : ActionQuotient E ≃* Perm (Fin 7))
    (s : Perm (Fin 7)) (hs : s.IsSwap)
    (hJ : (thompsonImage E).map c.toMonoidHom = zpowers s) :
    ∃ x ∈ (sylow E : Subgroup (localGroup E)).map (c.toMonoidHom.comp (projection E)),
      x.IsSwap ∧ ∃ hn : c.symm x ∈ normalizer (seedImage E : Set (ActionQuotient E)),
        ¬ ∃ b : seedImage E,
          (seedImage E).normalizerMonoidHom ⟨c.symm x,hn⟩ = MulAut.conj b := by
  let q := c.toMonoidHom.comp (projection E)
  have hq : Function.Surjective q := c.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := (sylow E).mapSurjective hq
  let B := (seedImage E).map c.toMonoidHom
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsPerfect (seedImage E) := Group.IsPerfect.ofSurjective (seedProjection_surjective E)
  let : Group.IsPerfect B := Group.IsPerfect.map _
  have hBcard : Nat.card B = 60 := by
    have hF : Nat.card E.input.field.Carrier = 4 := by rw [E.input.field.card_eq,hmodel.1]; rfl
    let d := Classical.choice (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF)
    rw [card_map_of_injective c.injective,
      Nat.card_congr ((seedImageEquiv E hstar hmodel e).trans d).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hJq : (elementaryAbelianMaxJ (radical E)).map q = zpowers s := by
    rw [←map_map]
    exact hJ
  have hsP : s ∈ P := by
    have hle : (elementaryAbelianMaxJ (radical E)).map q ≤ (P : Subgroup (Perm (Fin 7))) :=
      map_mono ((show elementaryAbelianMaxJ (radical E) ≤ radical E from sSup_le fun _ hA => hA.1).trans (fun _ hx => radical_le_sylow E hx))
    exact hle (hJq ▸ mem_zpowers s)
  have hPC : (P : Subgroup (Perm (Fin 7))) ≤ centralizer ({s} : Set (Perm (Fin 7))) := by
    have hn := (map_mono (f := q) ((sylow_normalizes_radical E).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ (radical E)))).trans (le_normalizer_map q)
    rw [hJq] at hn
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((normalizer_le_centralizer_of_card_two (zpowers s)
        (by rw [Nat.card_zpowers,hs.orderOf]) (hn hx) s (mem_zpowers s)).symm)
  have hBC : B ≤ centralizer ({s} : Set (Perm (Fin 7))) := by
    have hn := (map_mono (f := c.toMonoidHom) (seedImage_normalizes_thompsonImage E)).trans
      (le_normalizer_map c.toMonoidHom)
    rw [hJ] at hn
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((normalizer_le_centralizer_of_card_two (zpowers s)
        (by rw [Nat.card_zpowers,hs.orderOf]) (hn hx) s (mem_zpowers s)).symm)
  obtain ⟨x,hx,hxs,hn,ho⟩ := Permutation.exists_outer_swap P B hBcard s hsP hs hPC hBC
  have hn' : c.symm x ∈ normalizer (seedImage E : Set (ActionQuotient E)) := by
    have hh : x ∈ (normalizer (seedImage E : Set (ActionQuotient E))).map c.toMonoidHom := by
      rw [map_equiv_normalizer_eq]
      exact hn
    obtain ⟨y,hy,hye⟩ := hh
    have he : y = c.symm x := c.injective (hye.trans (c.apply_symm_apply x).symm)
    exact he ▸ hy
  refine ⟨x,hx,hxs,hn',?_⟩
  apply outer_transport c (seedImage E) B rfl (c.symm x) hn'
    (by simpa only [c.apply_symm_apply] using hn)
  simpa only [c.apply_symm_apply] using ho

/-- Construct the actual maximum elementary field witness. Only the original
normalization of L1 by T is used in passing back from the local Sylow. -/
theorem hasMaximalFieldWitness
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hline : E.V₁ = ⁅zpowers E.z, E.X⁆) (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E) (hff : IsFFModule (action E))
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (hnT : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G)) :
    HasMaximalFieldWitness E := by
  obtain ⟨t,_,_,⟨a⟩,_⟩ := natural_moved E h hf hne hstar hcent hmodel hff e
  have htop := offenderGroup_eq_top E h hf hne hstar hcent hmodel t a
  let c := quotientEquiv E htop t a
  obtain ⟨s,hs,hJs⟩ := transposition_image E h hf hne hstar hcent hline hXR hmodel e t a
  have hJ : (thompsonImage E).map c.toMonoidHom = zpowers s :=
    (thompsonImage_map_quotientEquiv E htop t a).trans hJs
  obtain ⟨x,hx,hxs,hn,ho⟩ := exists_outer_transposition E hstar hmodel e c s hs hJ
  let q := c.toMonoidHom.comp (projection E)
  have hq : Function.Surjective q := c.surjective.comp (QuotientGroup.mk'_surjective _)
  have hr := twoRank_radical_eq_sylow_of_ratio E h hf hne hstar hcent
    (quadraticRatio_eq_one E h hf hne hstar hcent hmodel hff e).ge
  have hRmap : (radical E).map (localGroup E).subtype = E.R₁ :=
    map_subgroupOf_eq_of_le ((radical_le_sylow E).trans le_sup_right)
  have hPmap : (sylow E : Subgroup (localGroup E)).map (localGroup E).subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hr' : ChapterB.twoRank (radical E) = ChapterB.twoRank (sylow E : Subgroup (localGroup E)) := by
    rw [←hRmap,←hPmap,ChapterB.twoRank_map_injective _ (localGroup E).subtype_injective,
      ChapterB.twoRank_map_injective _ (localGroup E).subtype_injective] at hr
    exact hr
  have hJq : (elementaryAbelianMaxJ (radical E)).map q = zpowers s := by
    rw [←map_map]
    exact hJ
  obtain ⟨A,hA,b,hb,hbx⟩ := exists_maxFamily_lift_swap (sylow E) (radical E)
    (fun _ hx => radical_le_sylow E hx) hr' q hq s hs hJq x hxs hx
  have hAG : A.map (localGroup E).subtype ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    rw [←hPmap]
    exact (maxFamily_map_injective_iff _ (localGroup E).subtype_injective _ _).mpr hA
  have hbq : projection E b = c.symm x := by
    apply c.injective
    exact hbx.trans (c.apply_symm_apply x).symm
  refine ⟨A.map (localGroup E).subtype,hAG,b,mem_map_of_mem _ hb,hnT (hA.1 hb),?_⟩
  have hbn : projection E b ∈ normalizer (seedImage E : Set (ActionQuotient E)) := hbq ▸ hn
  let : IsElementaryAbelian 2 A := hA.2.1
  apply isFieldElement_of_outer_involution E (seedImageEquiv E hstar hmodel e) b
    (elemPow_eq_one_of_isElementaryAbelian b hb) hbn
  simpa only [hbq] using ho

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
