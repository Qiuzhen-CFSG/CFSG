module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefKernel
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedThompsonChiefActions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefMarking

/-!
# Natural coordinates and marked bases on both original chief factors

The preceding residual-overgroup uniqueness identifies the kernel of every
noncentral chief action with O₂(H). The actual wreath quotient then excludes
the other small whole-action rows and supplies natural four-dimensional
coordinates. Pulling the two coordinate planes back gives complementary
four-groups whose pointwise centralizers are the marked factors in H.
The quotient equivalence preserves every literal offender image.

The source Thompson-image equality identifies the join of the marked factors
with J(H)O₂(H), independently of the chief interval or choice of coordinates.
The final consumer selects the two actual noncentral intervals and supplies
both coordinate systems with that common base. Alignment of the individual
factors and order-two images of original Delta members remain with the
qt-e-152-offender-plane owner. The preceding uniqueness and wreath hypotheses
come from qt-e-152-small-parabolic; qt-e-152-plane-geometry retains their final
discharge.

Source: Aschbacher--Smith 3.1.9(5), 15.1.12(3), and Notation 15.2.9,
printed pp.578,1090,1110; refs/quasithin.pdf.
-/

public section

open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 ChapterD ChapterD.UniqueFactor SmallActionsSource
private theorem chief_whole_wreath_coordinates
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

/-- Literal action quotient: kernel equality is transported before any action coordinates. -/
theorem ChosenSmallSource.chief_image_equiv_wreath
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      Nonempty (actionImage (s.factorRepresentation i) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  let q := actionHom (s.factorRepresentation i)
  have hq : Function.Surjective q := (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective
  have hk := h.chief_kernel_of_residual_unique hunique hH s i hi
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective q hq).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans he.some)⟩


/-- Both original noncentral chief factors have actual natural wreath coordinates. -/
theorem ChosenSmallSource.chief_natural_wreath_coordinates
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      Nonempty (ChiefWreathCoordinates (s.factorRepresentation i)) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  let ρ := s.factorRepresentation i
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc : Nat.card (actionImage ρ) = 72 := by
    obtain ⟨e⟩ := h.chief_image_equiv_wreath hunique hH he s i hi
    rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card]
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  obtain ⟨e,c,hec⟩ := chief_whole_wreath_coordinates (imageRepresentation ρ)
    (h.prepared.chief_small_whole_action h.ambient T h.empty h.maximal
      h.centralizing hH s i hi) hc
  refine ⟨⟨e.toMonoidHom.comp q,e.surjective.comp hq,?_,c,?_⟩⟩
  · ext g
    change e (q g) = 1 ↔ q g = 1
    rw [←e.map_one,e.injective.eq_iff]
  · intro g v j
    exact hec (q g) v j


/-- The original chief planes are complementary four-groups, with the actual
pointwise centralizers as their marked wreath factors. -/
theorem ChosenSmallSource.chief_marked_planes
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ∃ c : ChiefWreathCoordinates (s.factorRepresentation i),
        c.actor.ker = pCore 2 H ∧
        (∃ e : (H ⧸ pCore 2 H) ≃* ChiefWreathActor,
          (∀ g : H, e (QuotientGroup.mk' (pCore 2 H) g) = c.actor g) ∧
          ∀ A : Subgroup G, (ChosenGeometry.offenderImage H A).map e.toMonoidHom =
            (A.subgroupOf H).map c.actor) ∧
        IsCompl (c.plane 1) (c.plane ChiefWreath.flip) ∧
        (∀ j, Nat.card (c.plane j) = 4) ∧
        (letI := BinaryGroupAction.action (s.factorRepresentation i)
          ∀ j, fixingSubgroup H (c.plane j : Set (Multiplicative (Additive (s.Factor i)))) =
            c.factor (ChiefWreath.flip*j)) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  obtain ⟨c⟩ := h.chief_natural_wreath_coordinates hunique hH he s i hi
  have hk := c.kernel.trans (h.chief_kernel_of_residual_unique hunique hH s i hi)
  let e := QuotientGroup.liftEquiv (pCore 2 H) c.surjective hk.symm
  refine ⟨c,hk,⟨e,fun _ => rfl,?_⟩,c.planes_compl,c.plane_card,c.fixing_plane_eq⟩
  intro A
  change ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = _
  rw [map_map]
  rfl


/-- Each literal noncentral chief factor has binary dimension four. -/
theorem ChosenSmallSource.chief_factor_finrank_four
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      Module.finrank (ZMod 2) (Additive (s.Factor i)) = 4 := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  obtain ⟨c⟩ := h.chief_natural_wreath_coordinates hunique hH he s i hi
  have hc : Nat.card (Additive (s.Factor i)) = 16 := by
    change Nat.card (Multiplicative (Additive (s.Factor i))) = 16
    rw [Nat.card_congr c.vectors.toEquiv]
    change Nat.card (ZMod 2 → Fin 2 → ZMod 2) = 16
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    rfl
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (s.Factor i))
  rw [Nat.card_zmod,hc] at hp
  exact (Nat.pow_right_injective (by decide : 1 < 2) hp).symm

/-- The actual Thompson image has the paired S₃ type on every chief factor. -/
theorem ChosenSmallSource.chief_thompson_image_pair
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      Nonempty (((elementaryAbelianMaxJ (⊤ : Subgroup H)).map
        (actionHom (s.factorRepresentation i))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  let q := actionHom (s.factorRepresentation i)
  have hk := h.chief_kernel_of_residual_unique hunique hH s i hi
  have hc : Nat.card (H ⧸ q.ker) = 72 := by
    rw [hk,Nat.card_congr he.some.toEquiv,RegularWreathProduct.card]
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have ht := h.prepared.chief_thompson_actor_layer_types h.ambient T h.empty
    h.maximal h.centralizing hH s i hi
  rcases ht with ⟨⟨a⟩,_⟩ | ⟨_,ha⟩ | ⟨⟨a⟩,_⟩ | ⟨⟨a⟩,_⟩
  · have hh := Nat.card_congr a.toEquiv
    rw [hc] at hh
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
  · exact ha
  · have hh := Nat.card_congr a.toEquiv
    rw [hc] at hh
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
  · have hh := Nat.card_congr a.toEquiv
    rw [hc,RegularWreathProduct.card] at hh
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh

/-- The join of the two marked factors is intrinsic and thus the same for
both chief factors: it is the original Thompson subgroup joined with O₂(H). -/
theorem ChosenSmallSource.chief_marked_base
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ∀ c : ChiefWreathCoordinates (s.factorRepresentation i),
        c.factor 1 ⊔ c.factor ChiefWreath.flip =
          elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔ pCore 2 H := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s i hi c
  let ρ := s.factorRepresentation i
  let J := elementaryAbelianMaxJ (⊤ : Subgroup H)
  have hec : c.imageEquiv.toMonoidHom.comp (actionHom ρ) = c.actor := by
    apply MonoidHom.ext
    intro g
    exact c.imageEquiv_actionHom g
  have hc : Nat.card (J.map c.actor) = 36 := by
    rw [←hec,←map_map,card_map_of_injective (f := c.imageEquiv.toMonoidHom) c.imageEquiv.injective]
    obtain ⟨a⟩ := h.chief_thompson_image_pair hunique hH he s i hi
    rw [Nat.card_congr a.toEquiv]
    norm_num [Nat.card_prod,Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have ht := h.prepared.chief_thompson_image_eq h.ambient T h.empty h.maximal
    h.centralizing hH s i hi
  have hb : ChiefWreath.base ≤ J.map c.actor := by
    have hh := c.base_le_image_offenders
    rw [←ht,map_map,hec] at hh
    exact hh
  have hJ : J.map c.actor = ChiefWreath.base :=
    (eq_of_le_of_card_ge hb (by rw [hc,ChiefWreath.base_card])).symm
  rw [c.factor_sup_eq_base,←hJ,comap_map_eq,c.kernel,
    h.chief_kernel_of_residual_unique hunique hH s i hi]

/-- Choose the two actual noncentral chief intervals with natural coordinates
whose paired bases agree in H. Individual factor alignment is a separate step. -/
theorem ChosenSmallSource.two_chief_coordinates_with_common_base
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    letI := h.prepared.elementary
    let U := (conjugateSpan H V).subgroupOf H
    letI := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
    ∀ s : SeriesOn U, ∃ (i j : Fin s.series.length), i ≠ j ∧
      ¬ s.Central i ∧ ¬ s.Central j ∧
      ∃ (c : ChiefWreathCoordinates (s.factorRepresentation i))
        (d : ChiefWreathCoordinates (s.factorRepresentation j)),
        c.actor.ker = pCore 2 H ∧ d.actor.ker = pCore 2 H ∧
        c.factor 1 ⊔ c.factor ChiefWreath.flip =
          d.factor 1 ⊔ d.factor ChiefWreath.flip := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  dsimp only
  intro s
  have hcount := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).2 s
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  obtain ⟨c⟩ := h.chief_natural_wreath_coordinates hunique hH he s i hi
  obtain ⟨d⟩ := h.chief_natural_wreath_coordinates hunique hH he s j hj
  refine ⟨i,j,hij,hi,hj,c,d,
    c.kernel.trans (h.chief_kernel_of_residual_unique hunique hH s i hi),
    d.kernel.trans (h.chief_kernel_of_residual_unique hunique hH s j hj),?_⟩
  rw [h.chief_marked_base hunique hH he s i hi c,
    h.chief_marked_base hunique hH he s j hj d]

end CFSG.Quasithin.Chapter15.Section02
