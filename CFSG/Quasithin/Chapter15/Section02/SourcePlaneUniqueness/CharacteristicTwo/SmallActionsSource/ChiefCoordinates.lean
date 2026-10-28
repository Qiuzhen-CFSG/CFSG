module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefPair
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefMarking

/-!
# Faithful natural coordinates on the original noncentral chief factors

The kernel of every noncentral chief action is O₂(H): the wreath Sylow
maximality puts the kernel inside a Sylow, while irreducibility gives the
reverse inclusion. The original whole-action classification then supplies
the natural wreath coordinates; actor orders exclude its other rows.
The coordinates retain the literal H-action and its kernel, for the
centralizer marking in ChiefMarking.

Source: Aschbacher--Smith,15.1.12(3), Notation15.2.9 and15.2.21(1),
printed pp.1090,1110,1114; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor

private theorem whole_wreath_coordinates
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hs : ChapterB.ChiefSmallWholeAction ρ) (hc : Nat.card D = 72) :
    ∃ (e : D ≃* ChiefWreathActor) (c : Multiplicative W ≃* ChiefWreathSpace),
      ∀ g v i, c (Multiplicative.ofAdd (ρ g v.toAdd)) i =
        Multiplicative.ofAdd (Matrix.mulVec ((e g).left i).1
          ((c v ((e g).right⁻¹ * i)).toAdd)) := by
  rcases hs with ⟨hs,hw⟩ | hf
  · rcases hs with ⟨c,e,he⟩ | ⟨e,c,he⟩
    · obtain ⟨a⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      have hh := Nat.card_congr (e.trans a).toEquiv
      rw [hc] at hh
      norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · let a : W ≃+ subspaceCommutator ρ ⊤ (offenderSubgroup ρ) :=
        { toFun := fun v => ⟨v, by rw [hw]; trivial⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun _ => Subtype.ext rfl
          map_add' := fun _ _ => rfl }
      refine ⟨e,a.toMultiplicative.trans c,?_⟩
      intro g v i
      exact he g (Multiplicative.ofAdd (a v.toAdd)) i
  · rcases hf with hf | hf
    · obtain ⟨e⟩ := hf
      have hh := Nat.card_congr e.groupEquiv.toEquiv
      rw [hc] at hh
      norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · obtain ⟨e⟩ := hf
      have hh := Nat.card_congr e.groupEquiv.toEquiv
      rw [hc,RegularWreathProduct.card] at hh
      norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The kernel of any actual noncentral chief action is the original two-core. -/
theorem chief_action_kernel_eq_core :
    let h := hsource.prepared
    let := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      (actionHom (s.factorRepresentation i)).ker = pCore 2 H := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  let q := actionHom (s.factorRepresentation i)
  have hq : Function.Surjective q := (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective
  have hn : q.ker ≠ ⊤ := by
    intro hn
    apply hi
    rw [s.central_iff_action]
    intro g x
    have hg : q g = 1 := by
      change g ∈ q.ker
      rw [hn]
      exact mem_top g
    exact congrArg Additive.toMul ((actionHom_eq_one_iff _ g).mp hg (Additive.ofMul x))
  let S := T.subtype d.geometry.outside.1.1.2
  have hp := (source_centralizing_minimalParabolic hsource.ambient T hsource.maximal
    hsource.centralizing H d.geometry.outside).2.1
  have hred := (ChapterB.minimalParabolic_reduced_image S hp q hq
    (irreducible_image_twoCore_eq_bot (s.factorRepresentation i)) hn).2
  have hkerS : q.ker ≤ (S : Subgroup H) := by
    have hc := WreathTwoResidual.sylow_isCoatom_of_core_quotient S
      (d.geometry.quotient.some.trans ChosenGeometry.matrixWreathEquiv)
    rcases hc.le_iff.mp (le_sup_left : (S : Subgroup H) ≤ (S : Subgroup H) ⊔ q.ker) with he | he
    · have hm := congrArg (Subgroup.map q) he
      have hz : q.ker.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
      rw [Subgroup.map_sup,hz,sup_bot_eq,map_top_of_surjective _ hq] at hm
      exact (((ChapterB.isMinimalParabolicOver_top_iff _).mp hred).2 (by
        change ((S : Subgroup H).map q).Normal
        rw [hm]
        infer_instance)).elim
    · exact le_sup_right.trans he.le
  exact le_antisymm (le_sSup ⟨inferInstance,S.isPGroup'.to_le hkerS⟩) (by
    change pCore 2 H ≤ (actionHom (s.factorRepresentation i)).ker
    rw [actionHom_ker_eq]
    exact normal_p_subgroup_le_ker (s.factorRepresentation i) _ pCore_isPGroup)

/-- Every original noncentral chief factor has the full natural wreath action. -/
theorem chief_wreath_coordinates :
    let h := hsource.prepared
    let := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      Nonempty (ChiefWreathCoordinates (s.factorRepresentation i)) := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  let ρ := s.factorRepresentation i
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hk := chief_action_kernel_eq_core d s i hi
  have hc : Nat.card (actionImage ρ) = 72 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,
      hk,Nat.card_congr d.geometry.quotient.some.toEquiv,RegularWreathProduct.card]
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  obtain ⟨e,c,he⟩ := whole_wreath_coordinates (imageRepresentation ρ)
    (h.chief_small_whole_action hsource.ambient T hsource.empty hsource.maximal
      hsource.centralizing d.geometry.outside s i hi) hc
  refine ⟨⟨e.toMonoidHom.comp q,e.surjective.comp hq,?_,c,?_⟩⟩
  · ext g
    change e (q g) = 1 ↔ q g = 1
    rw [← e.map_one,e.injective.eq_iff]
  · intro g v j
    exact he (q g) v j

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
