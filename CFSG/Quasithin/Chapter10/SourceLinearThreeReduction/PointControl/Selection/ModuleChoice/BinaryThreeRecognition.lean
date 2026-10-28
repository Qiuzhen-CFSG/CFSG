module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ComponentModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FullMovedRows

/-!
# Literal binary-three rows on the original moved subgroup

Full commutator generation excludes the exceptional four-space in B.5.6.
The ambient odd-prime ranks restrict the remaining SL₃ field to F₂; the
actual SL₃(2) component cannot be an SL₂ or symmetric-five factor. Thus its
specified quotient summand is natural or doubled natural. The canonical
quotient bridge gives either row on the original [V,L], retaining exactly
C_[V,L](L) as its kernel and the original map L → L/O₂(L).

The applications in ModuleChoice.Source replace the unrecognized SL₃(2)
component by these literal coordinates. Doubled-row exclusion, quiet support
and even positive-kernel stabilization remain source obligations of
qt-d-10-nona5-point-selection; the final selection assembly remains with
qt-d-10-nona5-point-control.
Source: Aschbacher--Smith B.5.6(3), 3.2.6 and10.1.1--2,
printed pp.105,581,741--742.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

open Chapter3.Section02 Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem full_action_moved
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    letI : U.Normal := (source_full_module_reduced D).normal
    letI : IsElementaryAbelian 2 U := (source_full_module_reduced D).elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    moved (ρ.comp (offenderSubgroup ρ).subtype) ⊤ = ⊤ := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let X := (localOrbit T L).subgroupOf M
  have hmU : ⁅U,X⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le
      (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer),
      map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer]
    exact (D.fullModule_eq_commutator (source_module_nonsolvable_uniqueness D)).symm
  have hmX : subspaceCommutator ρ ⊤ (X.map q) = ⊤ := by
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (X.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) X]
    ext w
    change (w.toMul : M) ∈ ⁅U,X⁆ ↔ True
    rw [hmU]
    exact iff_true_intro w.toMul.property
  change subspaceCommutator (ρ.comp Y.subtype) ⊤ ⊤ = ⊤
  rw [subspaceCommutator_comp_map,←MonoidHom.range_eq_map,range_subtype]
  apply top_unique
  calc
    ⊤ = subspaceCommutator ρ ⊤ (X.map q) := hmX.symm
    _ ≤ subspaceCommutator ρ ⊤ Y := Submodule.span_mono (by
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact ⟨g,full_orbit_image_le_offender D hJ hg,v,hv,rfl⟩)

private theorem binary_three_factor
    {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} (d : SourceTwoFactorCase ρ)
    (hm : moved ρ ⊤ = ⊤) (e : d.first ≃* SL(3,ZMod 2))
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p d.first ≤ 1) :
    d.firstSpace.toSubmodule = moved ρ d.first ∧
      (IsLinearNatural (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype)
        BinaryField.two 3 ∨
       IsRepeatedLinearNatural (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype)
        BinaryField.two 3 2) := by
  have hd (F : BinaryField) (f : d.first ≃* SL(3,F.Carrier)) : F.degree = 1 := by
    apply Matrix.SL3.BinaryOddRankOne.degree_eq_one_of_odd_primeRanks_le_one
      F.Carrier F.degree_pos F.card_eq
    intro p hp ho
    rw [←primeRank_equiv p f]
    exact hr p hp ho
  obtain ⟨he,hn | hn⟩ := d.first_ordinary_of_moved_eq_top hm
  · refine ⟨he,?_⟩
    cases hn with
    | linearTwo F hn =>
      obtain ⟨f⟩ := hn
      let a := e.symm.trans f.groupEquiv
      exact (Matrix.SpecialLinearGroup.not_injective_linearThree_to_binaryLinearTwo
        a.toMonoidHom a.injective).elim
    | symmetricFive hn =>
      obtain ⟨f⟩ := hn
      let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
      let : Group.IsPerfect (Equiv.Perm (Fin 5)) := Group.IsPerfect.ofSurjective
        (f := (e.symm.trans f.groupEquiv).toMonoidHom) (e.symm.trans f.groupEquiv).surjective
      have hc := Group.IsPerfect.commutator_eq_top (G := Equiv.Perm (Fin 5))
      have hle := alternatingGroup.commutator_perm_le (α := Fin 5)
      rw [hc] at hle
      have hs := hle (show Equiv.swap (0 : Fin 5) 1 ∈ (⊤ : Subgroup (Equiv.Perm (Fin 5))) from mem_top _)
      rw [Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap (by decide)] at hs
      exact ((by decide : (-1 : ℤˣ) ≠ 1) hs).elim
    | linearThree F _ hn =>
      obtain ⟨f⟩ := hn
      let a := ExtensionConsequences.degreeOneNaturalEquiv F (hd F f.groupEquiv) 3
      exact Or.inl ⟨⟨f.groupEquiv.trans a.groupEquiv,f.linearEquiv.trans a.linearEquiv,
        fun g v => (congrArg a.linearEquiv (f.intertwines g v)).trans
          (a.intertwines (f.groupEquiv g) (f.linearEquiv v))⟩⟩
  · obtain ⟨F,_,⟨f⟩⟩ := hn
    let a := ExtensionConsequences.degreeOneRepeatedEquiv F (hd F f.groupEquiv) 3 2
    exact ⟨he,Or.inr ⟨⟨f.groupEquiv.trans a.groupEquiv,f.linearEquiv.trans a.linearEquiv,
      fun g v => (congrArg a.linearEquiv (f.intertwines g v)).trans
        (a.intertwines (f.groupEquiv g) (f.linearEquiv v))⟩⟩⟩

/-- Natural or doubled coordinates on the same full-action factor. -/
structure BinaryThreeFactorRow {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) where
  space : Subrepresentation ρ
  space_eq : space.toSubmodule = moved ρ A
  models : IsLinearNatural (((fixed ρ).quotientImage space).toRepresentation.comp A.subtype) BinaryField.two 3 ∨
    IsRepeatedLinearNatural (((fixed ρ).quotientImage space).toRepresentation.comp A.subtype) BinaryField.two 3 2

set_option backward.isDefEq.respectTransparency false in
/-- The specified full-action factor has natural or doubled binary-three coordinates. -/
theorem full_binary_three_factor
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    let M := D.maximalLocal
    let U := D.fullModule.subgroupOf M
    letI : U.Normal := (source_full_module_reduced D).normal
    letI : IsElementaryAbelian 2 U := (source_full_module_reduced D).elementary
    let q := ChapterB.InternalThompsonAction.actionMk U
    let ρ := ChapterB.InternalThompsonAction.action U
    let Y := offenderSubgroup ρ
    let σ : Representation (ZMod 2) Y (Additive U) := ρ.comp Y.subtype
    let A := ((L.subgroupOf M).map q).subgroupOf Y
    Nonempty (BinaryThreeFactorRow σ A) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let A := ((L.subgroupOf M).map q).subgroupOf Y
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hAX : L.subgroupOf M ≤ (localOrbit T L).subgroupOf M := comap_mono (le_componentOrbit L T)
  have hAY : (L.subgroupOf M).map q ≤ Y :=
    (map_mono (f := q) hAX).trans (full_orbit_image_le_offender D hJ)
  obtain ⟨a⟩ := full_action_original_component_equiv D hn
  let f : A ≃* (L ⧸ pCore 2 L) := (subgroupOfEquivOfLe hAY).trans a
  obtain ⟨d⟩ := full_module_two_factor_case D hn hJ
  have hex : ∃ d : SourceTwoFactorCase (ρ.comp Y.subtype), d.first = A := by
    rcases full_module_factor_alignment D hna hJ ht htn d with ⟨ha,_⟩ | ⟨ha,_⟩
    · exact ⟨d,ha.symm⟩
    · let ds : SourceTwoFactorCase (ρ.comp Y.subtype) := {
        first := d.second
        second := d.first
        product := d.product.swap
        firstSpace := d.secondSpace
        secondSpace := d.firstSpace
        decomposition := d.decomposition.symm
        firstCase := d.secondCase
        secondCase := d.firstCase }
      exact ⟨ds,ha.symm⟩
  obtain ⟨d,hd⟩ := hex
  have hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p d.first ≤ 1 := by
    intro p hp ho
    rw [hd,primeRank_equiv p f]
    exact component_quotient_odd_rank_le_one D hn p hp ho
  obtain ⟨hm,hrow⟩ := binary_three_factor d (full_action_moved D hJ)
    ((MulEquiv.subgroupCongr hd).trans (f.trans e)) hr
  have hr : Nonempty (BinaryThreeFactorRow (ρ.comp Y.subtype) d.first) :=
    ⟨⟨d.firstSpace,hm,hrow⟩⟩
  simpa only [hd] using hr

/-- The doubled alternative keeps the same original moved kernel. -/
def BinaryThreeDoubled (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2),
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      ((repeated (linearNatural BinaryField.two 3) 2).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

private def relabel_section
    {H A B : Subgroup G} {Q R X Y : Type*} [Group Q] [Group R]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) Q X} {τ : Representation (ZMod 2) R Y}
    (a : ActionEquiv ρ τ) (q : H →* Q)
    (c : BinaryConjugationSection H A B (ρ.comp q)) :
    BinaryConjugationSection H A B (τ.comp (a.groupEquiv.toMonoidHom.comp q)) := by
  let E : ρ.Equiv (τ.comp a.groupEquiv.toMonoidHom) :=
    Representation.Equiv.mk a.linearEquiv (fun g => by ext v; exact a.intertwines g v)
  exact c.relabel q E

/-- A binary-three component has a natural or doubled natural action on the
original moved subgroup, with the original full fixed kernel retained. -/
theorem binaryThreeNatural_or_doubled_of_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) : BinaryThreeNatural D ∨ BinaryThreeDoubled D := by
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  obtain ⟨r⟩ := full_binary_three_factor D hn hna hJ e
  obtain ⟨a,⟨c⟩⟩ := full_moved_quotient_section D hn hna hJ r.space r.space_eq
  rcases r.models with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨a.trans f.groupEquiv,⟨relabel_section f
      (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) c⟩⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨a.trans f.groupEquiv,⟨relabel_section f
      (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) c⟩⟩

/-- All moving local Thompson components now have literal section coordinates.
Only the doubled row still needs exclusion by the original ambient hypotheses. -/
theorem moving_local_natural_or_doubled
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    RankOneNatural D ∨ BinaryThreeNatural D ∨ BinaryThreeDoubled D := by
  rcases rankOneNatural_or_binaryThree_component D hn hna hJ with h | h
  · exact Or.inl h
  · obtain ⟨e⟩ := h
    exact Or.inr (binaryThreeNatural_or_doubled_of_component D hn hna hJ e)
end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
