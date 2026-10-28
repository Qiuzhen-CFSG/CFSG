module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Product
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.ModelFacts
public import Theory.Representation.SL2NaturalOffenders
public import Theory.Representation.SL3OddNaturalNormalizer
public import Theory.Representation.SL3DoubledNaturalOffenders
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.Supplements
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Offender localization for component action images

For the linear-two branch of B.5.9, the natural action is on the central
quotient of W=[V,L]. Perfectness makes every invariant linear map out of W
zero. Consequently the action kernels on W and W/C_W(L) coincide whenever
L acts faithfully on the latter. We construct this quotient action on the
literal `subspaceActionImage`, transport the marked component isomorphism,
and apply the intrinsic SL2 offender theorem.

For the four-dimensional cover, the same kernel comparison reduces the whole
ambient image to the natural SL3(2) action. Over F2 the full linear group is
already special linear, so the component fills the image. This also settles
the natural-three endpoint. The consumer applications use the established
model and supplement theorems to construct the actual B.5.10 configuration.

For general odd field degree, the natural SL3 normalizer has odd component
index, so every two-subgroup of the ambient image lies in the component. In
the doubled-natural case, coordinate conjugation identifies the marked component
with the same matrix action on both copies. Normality puts the transported
offender inside its binary normalizer, where the intrinsic multiplicity estimate
forces component containment. Both arguments include the field of order two.
All four branches feed the actual product constructor, without a localization,
product decomposition, or earlier classification premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9–10,
printed pp.107–109, especially the application of B.4.2 on p.109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry.Localization
variable {G V U : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) G V}

/-- Perfectness says that W=[V,L] has no trivial quotient. -/
theorem invariant_map_eq_zero {L : Subgroup G} [Group.IsPerfect L]
    (s : MovedSection ρ L) (f : s.space.toSubmodule →ₗ[ZMod 2] U)
    (hf : ∀ (l : L) (w : s.space.toSubmodule), f (s.space.toRepresentation l w) = f w)
    (w : s.space.toSubmodule) : f w = 0 := by
  have hm (l : L) (v : V) : ρ l v - v ∈ s.space.toSubmodule := by
    rw [s.space_eq]
    exact Submodule.subset_span ⟨l, l.property, v, Submodule.mem_top, rfl⟩
  have hd (l : L) (v : V) : f ⟨ρ l v - v, hm l v⟩ = 0 := by
    let d : L →* Multiplicative U :=
      { toFun := fun l => Multiplicative.ofAdd (f ⟨ρ l v - v, hm l v⟩)
        map_one' := by
          change f ⟨ρ 1 v - v, _⟩ = 0
          have hz : (⟨ρ 1 v - v, hm 1 v⟩ : s.space.toSubmodule) = 0 := by
            apply Subtype.ext
            simp
          rw [hz, map_zero]
        map_mul' := by
          intro a b
          apply Multiplicative.toAdd.injective
          change f ⟨ρ (a * b) v - v, _⟩ = f ⟨ρ a v - v, _⟩ + f ⟨ρ b v - v, _⟩
          have he : (⟨ρ (a * b) v - v, hm (a * b) v⟩ : s.space.toSubmodule) =
              s.space.toRepresentation a ⟨ρ b v - v, hm b v⟩ + ⟨ρ a v - v, hm a v⟩ := by
            apply Subtype.ext
            change ρ ((a : G) * (b : G)) v - v =
              ρ a (ρ b v - v) + (ρ a v - v)
            simp only [map_mul, Module.End.mul_apply, map_sub]
            abel
          rw [he, map_add, hf, add_comm] }
    let : Group.IsPerfect d.range := Group.IsPerfect.range d
    have he : d l = 1 := congrArg Subtype.val
      (Subsingleton.elim (⟨d l, l, rfl⟩ : d.range) 1)
    exact congrArg Multiplicative.toAdd he
  have hw : (w : V) ∈ moved ρ L := s.space_eq ▸ w.property
  generalize hv : (w : V) = v at hw
  induction hw using Submodule.span_induction generalizing w with
  | mem v hv' =>
    obtain ⟨l, hl, x, _, rfl⟩ := hv'
    exact (congrArg f (Subtype.ext hv)).trans (hd ⟨l, hl⟩ x)
  | zero =>
    have he : w = 0 := Subtype.ext hv
    simp [he]
  | add x y hx hy ihx ihy =>
    have hx' : x ∈ s.space.toSubmodule := s.space_eq ▸ hx
    have hy' : y ∈ s.space.toSubmodule := s.space_eq ▸ hy
    have he : w = (⟨x, hx'⟩ : s.space.toSubmodule) + ⟨y, hy'⟩ := Subtype.ext hv
    rw [he, map_add, ihx _ rfl, ihy _ rfl, add_zero]
  | smul a x hx ih =>
    have hx' : x ∈ s.space.toSubmodule := s.space_eq ▸ hx
    have he : w = a • (⟨x, hx'⟩ : s.space.toSubmodule) := Subtype.ext hv
    rw [he, map_smul, ih _ rfl, smul_zero]

/-- The central quotient has the same ambient kernel as W. -/
theorem section_kernel_eq {L : Subgroup G} [L.Normal] [Group.IsPerfect L]
    (s : MovedSection ρ L) (hf : Function.Injective (s.action.comp L.subtype)) :
    s.action.ker = s.space.toRepresentation.ker := by
  apply le_antisymm
  · intro g hg
    have hg' : s.central.quotientRepresentation g = 1 := hg
    have hc (l : L) : g * (l : G) = (l : G) * g := by
      have he : (⟨g * l * g⁻¹, (inferInstance : L.Normal).conj_mem l l.property g⟩ : L) = l := by
        apply hf
        change s.central.quotientRepresentation (g * l * g⁻¹) = s.central.quotientRepresentation l
        simp only [map_mul, hg', one_mul]
        have hgi : s.central.quotientRepresentation g⁻¹ = 1 := by
          have he := s.central.quotientRepresentation.map_mul g g⁻¹
          simpa only [mul_inv_cancel, map_one, hg', one_mul] using he.symm
        rw [hgi, mul_one]
      exact (mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val he)
    let f : s.space.toSubmodule →ₗ[ZMod 2] s.space.toSubmodule :=
      s.space.toRepresentation g - LinearMap.id
    have hfixed (w : s.space.toSubmodule) : f w ∈ fixedSpace s.space.toRepresentation L := by
      rw [← s.central_eq]
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change s.central.toSubmodule.mkQ (s.space.toRepresentation g w - w) = 0
      rw [map_sub]
      change s.central.quotientRepresentation g (s.central.toSubmodule.mkQ w) - s.central.toSubmodule.mkQ w = 0
      rw [hg']
      exact sub_self _
    have hi (l : L) (w : s.space.toSubmodule) :
        f (s.space.toRepresentation l w) = f w := by
      calc
        _ = s.space.toRepresentation l (f w) := by
          change s.space.toRepresentation g (s.space.toRepresentation l w) -
            s.space.toRepresentation l w = s.space.toRepresentation l
              (s.space.toRepresentation g w - w)
          rw [map_sub, ← Module.End.mul_apply, ← map_mul, hc,
            map_mul, Module.End.mul_apply]
        _ = f w := hfixed w l
    apply LinearMap.ext
    intro w
    exact sub_eq_zero.mp (invariant_map_eq_zero s f hi w)
  · intro g hg
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ w => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun hg w)


/-- Coordinate transport of the intrinsic SL2 offender theorem, including F2. -/
theorem natural_two_offender_le [Finite G] (σ : Representation (ZMod 2) G U)
    (hfaith : Function.Injective σ) (L : Subgroup G) [L.Normal] (F : BinaryField)
    (e : ActionEquiv (σ.comp L.subtype) (linearNatural F 2))
    {D : Subgroup G} (hD : IsOffender σ D) : D ≤ L := by
  let τ : Representation (ZMod 2) G (Fin 2 → F.Carrier) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp σ
  have ht (g : G) (v : U) : e.linearEquiv (σ g v) = τ g (e.linearEquiv v) := by
    change _ = e.linearEquiv (σ g (e.linearEquiv.symm (e.linearEquiv v)))
    rw [e.linearEquiv.symm_apply_apply]
  have hf : Function.Injective τ := e.linearEquiv.conjRingEquiv.injective.comp hfaith
  have hn (g : L) (v : Fin 2 → F.Carrier) :
      τ g v = Matrix.mulVec (e.groupEquiv g).val v := by
    change e.linearEquiv (σ g (e.linearEquiv.symm v)) = _
    exact (e.intertwines g (e.linearEquiv.symm v)).trans
      (congrArg (linearNatural F 2 (e.groupEquiv g)) (e.linearEquiv.apply_symm_apply v))
  have hd : IsOffender τ D := by
    simpa only [Subgroup.map_id] using hD.map_equivariant σ τ (MonoidHom.id G)
      Function.injective_id e.linearEquiv ht
  have hcont : ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = D := by
    by_cases hF : 2 < Nat.card F.Carrier
    · exact SL2NaturalOffenders.exists_sylow hF L e.groupEquiv τ hf hn hd
    · apply SL2NaturalOffenders.exists_sylow_of_linear L e.groupEquiv τ hf hn hd
      intro a _ c v
      have hs : Function.Surjective (algebraMap (ZMod 2) F.Carrier) :=
        ((algebraMap (ZMod 2) F.Carrier).injective.bijective_of_nat_card_le
          (by simpa using Nat.le_of_not_gt hF)).2
      obtain ⟨c, rfl⟩ := hs c
      simp only [algebraMap_smul, map_smul]
  obtain ⟨P, rfl⟩ := hcont
  rintro _ ⟨g, _, rfl⟩
  exact g.property


noncomputable def imageMap (W : Subrepresentation ρ) :
    G →* subspaceActionImage ρ W.toSubmodule :=
  invariantActionHom ρ W.toSubmodule
    (le_subspaceStabilizer ρ _ (fun g _ _ hv => W.apply_mem_toSubmodule g hv))

theorem imageMap_surjective (W : Subrepresentation ρ) :
    Function.Surjective (imageMap W) := invariantActionHom_surjective ρ _ _

theorem imageMap_map (W : Subrepresentation ρ) (L : Subgroup G) :
    L.map (imageMap W) = restrictedSubgroup ρ W.toSubmodule L :=
  invariantActionHom_map ρ _ _ L

noncomputable def imageCentral {L : Subgroup G} (s : MovedSection ρ L) :
    Subrepresentation (subspaceImageRepresentation ρ s.space.toSubmodule) where
  toSubmodule := s.central.toSubmodule
  apply_mem_toSubmodule d w hw := by
    obtain ⟨g, rfl⟩ := imageMap_surjective s.space d
    exact s.central.apply_mem_toSubmodule g hw

theorem imageCentral_faithful {L : Subgroup G} [L.Normal] [Group.IsPerfect L]
    (s : MovedSection ρ L) (hf : Function.Injective (s.action.comp L.subtype)) :
    Function.Injective (imageCentral s).quotientRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro d hd
  obtain ⟨g, rfl⟩ := imageMap_surjective s.space d
  have hg : g ∈ s.action.ker := hd
  rw [section_kernel_eq s hf] at hg
  apply subspaceImageRepresentation_injective ρ s.space.toSubmodule
  exact hg

noncomputable def imageComponentEquiv {L : Subgroup G} (W : Subrepresentation ρ)
    (hf : Function.Injective (W.toRepresentation.comp L.subtype)) :
    L ≃* restrictedSubgroup ρ W.toSubmodule L := by
  have hi : Function.Injective ((imageMap W).subgroupMap L) := by
    intro x y h
    apply hf
    exact congrArg (fun d => subspaceImageRepresentation ρ W.toSubmodule d)
      (congrArg Subtype.val h)
  exact (MulEquiv.ofBijective _ ⟨hi, (imageMap W).subgroupMap_surjective L⟩).trans
    (MulEquiv.subgroupCongr (imageMap_map W L))

theorem imageComponentEquiv_apply {L : Subgroup G} (W : Subrepresentation ρ)
    (hf : Function.Injective (W.toRepresentation.comp L.subtype)) (l : L) :
    (imageComponentEquiv W hf l : subspaceActionImage ρ W.toSubmodule) = imageMap W l := rfl

theorem imageComponent_normal {L : Subgroup G} [L.Normal] (W : Subrepresentation ρ) :
    (restrictedSubgroup ρ W.toSubmodule L).Normal := by
  rw [← imageMap_map W L]
  exact (inferInstance : L.Normal).map _ (imageMap_surjective W)


private theorem natural_faithful (σ : Representation (ZMod 2) G U)
    (F : BinaryField) (d : ℕ) (e : ActionEquiv σ (linearNatural F d)) :
    Function.Injective σ := by
  intro g h he
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective d
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := e.linearEquiv.surjective v
  exact (e.intertwines g w).symm.trans
    ((congrArg e.linearEquiv (LinearMap.congr_fun he w)).trans (e.intertwines h w))

set_option backward.isDefEq.respectTransparency false in
noncomputable def imageCentral_natural {L : Subgroup G}
    (s : MovedSection ρ L) (hf : Function.Injective (s.space.toRepresentation.comp L.subtype))
    (F : BinaryField) (d : ℕ) (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F d)) :
    ActionEquiv ((imageCentral s).quotientRepresentation.comp
      (restrictedSubgroup ρ s.space.toSubmodule L).subtype) (linearNatural F d) where
  groupEquiv := (imageComponentEquiv s.space hf).symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines l w := by
    obtain ⟨g, rfl⟩ := (imageComponentEquiv s.space hf).surjective l
    simp only [MonoidHom.comp_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change e.linearEquiv ((imageCentral s).quotientRepresentation
      (imageComponentEquiv s.space hf g : subspaceActionImage ρ s.space.toSubmodule) w) = _
    rw [imageComponentEquiv_apply]
    have he : (imageCentral s).quotientRepresentation (imageMap s.space g) w =
        s.central.quotientRepresentation g w := by
      induction w using Submodule.Quotient.induction_on with
      | _ v => rfl
    rw [he]
    exact e.intertwines g w

/-- Localization in the literal action image, with the natural action on
W/C_W(L), as required in B.5.9(1). -/
theorem linearTwo [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {L : Subgroup G} [L.Normal] (hL : IsComponent G L) (s : MovedSection ρ L)
    (F : BinaryField) (hn : IsLinearNatural (s.action.comp L.subtype) F 2)
    (D : Subgroup (subspaceActionImage ρ s.space.toSubmodule))
    (hD : IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D) :
    D ≤ restrictedSubgroup ρ s.space.toSubmodule L := by
  let := hyp.finite_module
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : Group.IsPerfect L := inferInstance
  let : (restrictedSubgroup ρ s.space.toSubmodule L).Normal := imageComponent_normal s.space
  obtain ⟨e⟩ := hn
  have hf := (linearTwo_faithful_center s F ⟨e⟩).1
  have hq := natural_faithful (s.action.comp L.subtype) F 2 e
  have hd : IsOffender (imageCentral s).quotientRepresentation D := by
    refine ⟨hD.1, ?_⟩
    have hb := fixedCodim_quotient_add_subrepresentation_le
      (subspaceImageRepresentation ρ s.space.toSubmodule) (imageCentral s) D
    have hc := (hD.isOffender _).2
    omega
  exact natural_two_offender_le _ (imageCentral_faithful s hq) _ F
    (imageCentral_natural s hf F 2 e) hd

/-- Actual application to the B.5.10 constructor, now without a localization premise. -/
theorem linearTwo_configuration [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} [L.Normal] (hL : IsComponent G L) (s : MovedSection ρ L)
    (F : BinaryField) (hn : IsLinearNatural (s.action.comp L.subtype) F 2)
    (hsyl : ∃ T : Sylow 2 L, A = (T : Subgroup L).map L.subtype)
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := linearTwo_faithful_center s F hn
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz
    (linearTwo hyp hL s F hn) (Or.inl (sylow_supplement s hsyl hs))


/-- Over F2 the natural SL group is already the entire linear group. -/
theorem binary_natural_eq_top (σ : Representation (ZMod 2) G U)
    (hfaith : Function.Injective σ) (L : Subgroup G) (d : ℕ)
    (e : ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two d)) : L = ⊤ := by
  apply top_unique
  intro g _
  let τ : Representation (ZMod 2) G (Fin d → ZMod 2) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp σ
  let M := Matrix.GeneralLinearGroup.toLin.symm (τ.asGroupHom g)
  have hdet : M.val.det = 1 := by
    have hn := M.det_ne_zero
    have he (x : ZMod 2) : x = 0 ∨ x = 1 := by
      fin_cases x
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact (he M.val.det).resolve_left hn
  let m : Matrix.SpecialLinearGroup (Fin d) (ZMod 2) := ⟨M.val, hdet⟩
  let l : L := e.groupEquiv.symm m
  have he : σ g = σ l := by
    apply e.linearEquiv.conjRingEquiv.injective
    change τ g = τ l
    apply LinearMap.ext
    intro v
    have hn := e.intertwines l (e.linearEquiv.symm v)
    have hv : τ l v = Matrix.mulVec m.val v := by
      exact hn.trans (congrArg₂ (fun a w => linearNatural BinaryField.two d a w)
        (e.groupEquiv.apply_symm_apply m) (e.linearEquiv.apply_symm_apply v))
    rw [hv]
    have hm := congrArg (fun t : LinearMap.GeneralLinearGroup (ZMod 2) (Fin d → ZMod 2) =>
      t.val v) (Matrix.GeneralLinearGroup.toLin.apply_symm_apply (τ.asGroupHom g))
    exact hm.symm
  exact hfaith he ▸ l.property

noncomputable def central_natural_of_reduced {L : Subgroup G}
    (s : MovedSection ρ L) (F : BinaryField) (d : ℕ)
    (e : ActionEquiv (reducedAction (s.space.toRepresentation.comp L.subtype))
      (linearNatural F d)) :
    ActionEquiv (s.action.comp L.subtype) (linearNatural F d) := by
  let E := Submodule.quotEquivOfEq s.central.toSubmodule
    (fixed (s.space.toRepresentation.comp L.subtype)).toSubmodule s.central_eq
  exact
    { groupEquiv := e.groupEquiv
      linearEquiv := E.trans e.linearEquiv
      intertwines := by
        intro g w
        have he : E (s.central.quotientRepresentation g w) =
            (fixed (s.space.toRepresentation.comp L.subtype)).quotientRepresentation g (E w) := by
          induction w using Submodule.Quotient.induction_on with
          | _ v => rfl
        exact (congrArg e.linearEquiv he).trans (e.intertwines g (E w)) }


/-- The entire image on the four-dimensional cover equals the component image. -/
theorem fourCover_image_eq_top {L : Subgroup G} [L.Normal] (hL : IsComponent G L)
    (s : MovedSection ρ L)
    (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype)) :
    restrictedSubgroup ρ s.space.toSubmodule L = ⊤ := by
  let : IsQuasisimple L := hL.2
  let e := central_natural_of_reduced s BinaryField.two 3 cover.natural
  have hf := (fourCover_faithful_center s cover).1
  have hq := natural_faithful (s.action.comp L.subtype) BinaryField.two 3 e
  exact binary_natural_eq_top (imageCentral s).quotientRepresentation
    (imageCentral_faithful s hq) _ 3 (imageCentral_natural s hf BinaryField.two 3 e)

/-- The B.5.9(5) offender-localization conclusion on the original action image. -/
theorem fourCover {L : Subgroup G} [L.Normal] (hL : IsComponent G L)
    (s : MovedSection ρ L)
    (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype))
    (D : Subgroup (subspaceActionImage ρ s.space.toSubmodule))
    (_hD : IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D) :
    D ≤ restrictedSubgroup ρ s.space.toSubmodule L := by
  rw [fourCover_image_eq_top hL s cover]
  exact le_top

/-- Actual cover-branch application, with both localization and the supplement discharged. -/
theorem fourCover_configuration [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} [L.Normal] (hL : IsComponent G L) (s : MovedSection ρ L)
    (hA : IsBestOffender ρ A) (hAL : A ≤ L)
    (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype)) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := fourCover_faithful_center s cover
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz
    (fourCover hL s cover) (Or.inl (fourCover_supplement s hyp.faithful hA hAL cover))

set_option backward.isDefEq.respectTransparency false in
noncomputable def imageSpace_natural {L : Subgroup G}
    (W : Subrepresentation ρ) (hf : Function.Injective (W.toRepresentation.comp L.subtype))
    (F : BinaryField) (d : ℕ) (e : ActionEquiv (W.toRepresentation.comp L.subtype) (linearNatural F d)) :
    ActionEquiv ((subspaceImageRepresentation ρ W.toSubmodule).comp
      (restrictedSubgroup ρ W.toSubmodule L).subtype) (linearNatural F d) where
  groupEquiv := (imageComponentEquiv W hf).symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines l w := by
    obtain ⟨g, rfl⟩ := (imageComponentEquiv W hf).surjective l
    simp only [MonoidHom.comp_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change e.linearEquiv (subspaceImageRepresentation ρ W.toSubmodule
      (imageComponentEquiv W hf g : subspaceActionImage ρ W.toSubmodule) w) = _
    rw [imageComponentEquiv_apply]
    exact e.intertwines g w

/-- The endpoint of B.5.9(4): every binary automorphism is already in SL3(2). -/
theorem naturalThree_two_image_eq_top {L : Subgroup G} (s : MovedSection ρ L)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two 3) :
    restrictedSubgroup ρ s.space.toSubmodule L = ⊤ := by
  obtain ⟨e⟩ := hn
  have hf := (naturalThree_faithful_center s BinaryField.two (by decide) ⟨e⟩).1
  exact binary_natural_eq_top (subspaceImageRepresentation ρ s.space.toSubmodule)
    (subspaceImageRepresentation_injective ρ s.space.toSubmodule) _ 3
    (imageSpace_natural s.space hf BinaryField.two 3 e)

/-- The actual exceptional-endpoint application to B.5.10. -/
theorem naturalThree_two_configuration [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two 3) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := naturalThree_faithful_center s BinaryField.two (by decide) hn
  apply configuration_of_offender_image ρ hyp.generated s.space L hf hz
  · intro D _
    rw [naturalThree_two_image_eq_top s hn]
    exact le_top
  · exact naturalThree_supplement_or_exceptional s BinaryField.two hn

private theorem natural_three_two_subgroup_le (σ : Representation (ZMod 2) G U)
    (hfaith : Function.Injective σ) (L : Subgroup G) [L.Normal]
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (σ.comp L.subtype) (linearNatural F 3))
    (D : Subgroup G) (hD : IsPGroup 2 D) : D ≤ L := by
  let τ : Representation (ZMod 2) G (Fin 3 → F.Carrier) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp σ
  have hf : Function.Injective τ := e.linearEquiv.conjRingEquiv.injective.comp hfaith
  have hn (g : L) (v : Fin 3 → F.Carrier) :
      τ g v = Matrix.mulVec (e.groupEquiv g).val v := by
    change e.linearEquiv (σ g (e.linearEquiv.symm v)) = _
    exact (e.intertwines g (e.linearEquiv.symm v)).trans
      (congrArg (linearNatural F 3 (e.groupEquiv g)) (e.linearEquiv.apply_symm_apply v))
  exact SL3OddNaturalNormalizer.two_subgroup_le_of_natural
    F.degree_pos ho F.card_eq L e.groupEquiv τ hf hn D hD

/-- The natural-three localization on the literal ambient action image, for
all positive odd field degrees. -/
theorem naturalThree [Finite G] {L : Subgroup G} [L.Normal]
    (s : MovedSection ρ L) (F : BinaryField) (ho : Odd F.degree)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) F 3)
    (D : Subgroup (subspaceActionImage ρ s.space.toSubmodule))
    (hD : IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D) :
    D ≤ restrictedSubgroup ρ s.space.toSubmodule L := by
  let : (restrictedSubgroup ρ s.space.toSubmodule L).Normal := imageComponent_normal s.space
  let : IsElementaryAbelian 2 D := hD.1.2
  obtain ⟨e⟩ := hn
  have hf := (naturalThree_faithful_center s F ho ⟨e⟩).1
  exact natural_three_two_subgroup_le _
    (subspaceImageRepresentation_injective ρ s.space.toSubmodule) _ F ho
    (imageSpace_natural s.space hf F 3 e) D (IsElementaryAbelian.isPGroup 2 D)

/-- B.5.10 in the natural-three branch, with localization and the exact
fixed-supplement or exceptional-hyperplane conclusion proved. -/
theorem naturalThree_configuration [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (ho : Odd F.degree)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) F 3) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := naturalThree_faithful_center s F ho hn
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz
    (naturalThree s F ho hn) (naturalThree_supplement_or_exceptional s F hn)

set_option backward.isDefEq.respectTransparency false in
/-- Transport both identically marked copies to the literal component image. -/
noncomputable def imageSpace_repeated {L : Subgroup G}
    (W : Subrepresentation ρ) (hf : Function.Injective (W.toRepresentation.comp L.subtype))
    (F : BinaryField) (d r : ℕ)
    (e : ActionEquiv (W.toRepresentation.comp L.subtype) (repeated (linearNatural F d) r)) :
    ActionEquiv ((subspaceImageRepresentation ρ W.toSubmodule).comp
      (restrictedSubgroup ρ W.toSubmodule L).subtype) (repeated (linearNatural F d) r) where
  groupEquiv := (imageComponentEquiv W hf).symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines l w := by
    obtain ⟨g, rfl⟩ := (imageComponentEquiv W hf).surjective l
    simp only [MonoidHom.comp_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change e.linearEquiv (subspaceImageRepresentation ρ W.toSubmodule
      (imageComponentEquiv W hf g : subspaceActionImage ρ W.toSubmodule) w) = _
    rw [imageComponentEquiv_apply]
    exact e.intertwines g w

private theorem double_natural_offender_le (σ : Representation (ZMod 2) G U)
    (hfaith : Function.Injective σ) (L : Subgroup G) [L.Normal]
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (σ.comp L.subtype) (repeated (linearNatural F 3) 2))
    {D : Subgroup G} (hD : IsOffender σ D) : D ≤ L := by
  let τ : Representation (ZMod 2) G (SL3DoubledNaturalOffenders.Space F.Carrier) :=
    e.linearEquiv.conjRingEquiv.toMonoidHom.comp σ
  let f := τ.asGroupHom
  have hf : Function.Injective f := by
    intro g h he
    apply e.linearEquiv.conjRingEquiv.injective.comp hfaith
    exact congrArg Units.val he
  have ht (g : G) (v : U) :
      e.linearEquiv (σ g v) = SL3DoubledNaturalOffenders.action F.Carrier (f g)
        (e.linearEquiv v) := by
    change _ = e.linearEquiv (σ g (e.linearEquiv.symm (e.linearEquiv v)))
    rw [e.linearEquiv.symm_apply_apply]
  have hn (g : L) : f g =
      (SL3DoubledNaturalOffenders.representation F.Carrier).asGroupHom (e.groupEquiv g) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change e.linearEquiv (σ g (e.linearEquiv.symm v)) = _
    exact (e.intertwines g (e.linearEquiv.symm v)).trans
      (congrArg (repeated (linearNatural F 3) 2 (e.groupEquiv g))
        (e.linearEquiv.apply_symm_apply v))
  have he : L.map f = SL3DoubledNaturalOffenders.component F.Carrier := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨e.groupEquiv ⟨g, hg⟩, (hn ⟨g, hg⟩).symm⟩
    · rintro _ ⟨g, rfl⟩
      exact ⟨e.groupEquiv.symm g, (e.groupEquiv.symm g).property,
        (hn (e.groupEquiv.symm g)).trans
          (congrArg (SL3DoubledNaturalOffenders.representation F.Carrier).asGroupHom
            (e.groupEquiv.apply_symm_apply g))⟩
  have hDN : D.map f ≤ SL3DoubledNaturalOffenders.normalizer F.Carrier := by
    change D.map f ≤ Subgroup.normalizer (SL3DoubledNaturalOffenders.component F.Carrier)
    rw [← he]
    exact (Subgroup.map_mono (show D ≤ Subgroup.normalizer L by
      rw [Subgroup.normalizer_eq_top]; exact le_top)).trans (Subgroup.le_normalizer_map f)
  have hd := SL3DoubledNaturalOffenders.offender_le_component_of_le_normalizer
    F.card_eq F.degree_pos ho
    (hD.map_equivariant σ (SL3DoubledNaturalOffenders.action F.Carrier) f hf e.linearEquiv ht) hDN
  rw [← he] at hd
  intro g hg
  obtain ⟨l, hl, heq⟩ := hd (Subgroup.mem_map_of_mem f hg)
  exact hf heq ▸ hl

/-- Offenders on W=[V,L] lie in the component image when W consists of two
identically marked natural SL₃ modules of odd binary field degree. -/
theorem doubleThree [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (ho : Odd F.degree)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2)
    (D : Subgroup (subspaceActionImage ρ s.space.toSubmodule))
    (hD : IsBestOffender (subspaceImageRepresentation ρ s.space.toSubmodule) D) :
    D ≤ restrictedSubgroup ρ s.space.toSubmodule L := by
  let := hyp.finite_module
  let : (restrictedSubgroup ρ s.space.toSubmodule L).Normal := imageComponent_normal s.space
  obtain ⟨e⟩ := hn
  have hf := (doubleThree_faithful_center s F ho ⟨e⟩).1
  exact double_natural_offender_le _
    (subspaceImageRepresentation_injective ρ s.space.toSubmodule) _ F ho
    (imageSpace_repeated s.space hf F 3 2 e) (hD.isOffender _)

/-- B.5.10 in the doubled-natural branch, using the actual contained offender
for the supplement and the intrinsic multiplicity estimate for localization. -/
theorem doubleThree_configuration [Finite G] {K : GroupClass} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (ho : Odd F.degree) (hA : IsBestOffender ρ A) (hAL : A ≤ L)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2) :
    Nonempty (ProductConfiguration ρ L s.space) := by
  let := hyp.finite_module
  obtain ⟨hf, hz⟩ := doubleThree_faithful_center s F ho hn
  exact configuration_of_offender_image ρ hyp.generated s.space L hf hz
    (doubleThree hyp s F ho hn) (Or.inl (doubleThree_supplement s F hA hAL hn))

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry.Localization
