module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Branches
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Cover
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting

/-!
# Root and radical commutators on the original symplectic cover

The marked action on V is a central cover of the natural symplectic module.
The universal-cover root calculation identifies the root displacement with
the full point preimage, including C_V(L). Since this displacement already
contains the central kernel, the native radical displacement lifts to the
full hyperplane preimage. Fixed-vector lifting proves that the literal root
preimage centralizes that hyperplane.

The three commutator identities apply to the original subgroup actions and
feed the proof that U is abelian. Compatible point and hyperplane coordinates
remain preceding flag inputs; the final source assembly belongs to
qt-d-1222-natural-closure-sp4. No splitting or trivial central attachment is
assumed.

Source: Aschbacher--Smith 11.5.7, printed pp.782--783, using I.2.3(1).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CoverGeometry
open Subgroup Representation Representation.OneCohomology LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open scoped IsMulCommutative

private theorem coinvariants_map {k H J W : Type*} [Field k] [Group H] [Group J]
    [AddCommGroup W] [Module k W] (ρ : Representation k H W)
    (f : J →* H) (A : Subgroup J) :
    Coinvariants.ker (ρ.comp (A.map f).subtype) =
      Coinvariants.ker ((ρ.comp f).comp A.subtype) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨b,hb,he⟩ := a.property
    change ρ a.val w - w ∈ _
    rw [← he]
    exact Coinvariants.sub_mem_ker (ρ := (ρ.comp f).comp A.subtype) ⟨b,hb⟩ w
  · rintro _ ⟨⟨a,w⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp (A.map f).subtype)
      ⟨f a.val,mem_map_of_mem f a.property⟩ w

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

abbrev action := Preliminary.markedAction D m.action
abbrev projection := Preliminary.markedProjection D m.action
abbrev coverAction := LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.sp4CoverAction D E.input m.action
abbrev coverProjection := LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.sp4CoverProjection D E.input m.action

theorem field_large : 2 < Nat.card E.input.field.Carrier := by
  rw [E.input.field.card_eq]
  simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) E.input.nonbinary

def derivedElement (g : Sp E.input.field.Carrier) : Representation.SymplecticFourOrthogonalCover.L (K := E.input.field.Carrier) :=
  ⟨g, by rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top
    (field_large (E := E))]; trivial⟩

theorem conjugate_root_map (g : Sp E.input.field.Carrier) :
    (Representation.SymplecticFourOrthogonalCover.Roots.conjugateGroup (derivedElement (E := E) g)).map (commutator _).subtype =
      (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom := by
  ext a
  constructor
  · rintro ⟨b,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨c.val,hc,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨derivedElement (E := E) g * derivedElement (E := E) b *
      (derivedElement (E := E) g)⁻¹,
      ⟨derivedElement (E := E) b,hb,rfl⟩,rfl⟩

theorem root_moved (g : Sp E.input.field.Carrier) :
    Coinvariants.ker ((action m).comp
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).subtype) =
      (((point E.input.field.Carrier).map (toLinear g).toLinearMap).restrictScalars
        (ZMod 2)).comap (projection m).toLinearMap := by
  rw [← conjugate_root_map (E := E) g, coinvariants_map]
  exact (Representation.SymplecticFourOrthogonalCover.Roots.cover_conjugate_root_geometry (field_large (E := E))
    (derivedElement (E := E) g) (coverProjection m)
    (LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.sp4CoverProjection_isCover D E.input m.action)).2.1.symm

theorem fixed_of_projection_fixed (a : Sp E.input.field.Carrier) (w : D.space)
    (hw : a • projection m w = projection m w) : action m a w = w := by
  exact Representation.SymplecticFourOrthogonalCover.cover_fixed_of_projection_fixed (coverProjection m)
    (LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.sp4CoverProjection_isCover D E.input m.action) (derivedElement (E := E) a) w hw

/-- The literal chosen-space embedding in the ambient group. -/
def spaceMap : Multiplicative D.space →* G := V.subtype.comp D.spaceEquiv.toMonoidHom

theorem spaceMap_action (l : L) (w : D.space) :
    spaceMap (D := D) (Multiplicative.ofAdd (action m (PointModel.quotientMap m l) w)) =
      l.val * spaceMap (D := D) (Multiplicative.ofAdd w) * l.val⁻¹ := by
  rw [show action m (PointModel.quotientMap m l) w = D.chosenAction l w from
    Preliminary.markedAction_mk D m.action l w]
  change (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) : G) = _
  rw [D.spaceEquiv_apply]
  change l.val * (w.val.toMul.val : G) * l.val⁻¹ = _
  rw [← D.spaceEquiv_apply]
  rfl

/-- Coinvariants of the actual marked image give the original ambient commutator. -/
theorem commutator_eq (A : Subgroup G) (hA : A ≤ L) :
    ⁅V,A⁆ = (Coinvariants.ker ((action m).comp (PointModel.image m A).subtype)).toAddSubgroup.toSubgroup.map (spaceMap (D := D)) := by
  rw [commutator_comm]
  let C : Submodule (ZMod 2) D.space := AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm (⁅A,V⁆.comap (spaceMap (D := D))))
  have hc : Coinvariants.ker ((action m).comp (PointModel.image m A).subtype) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨l,hl,he⟩ := a.property
    change spaceMap (D := D) (Multiplicative.ofAdd (action m a.val w - w)) ∈ ⁅A,V⁆
    rw [← he, ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, spaceMap_action]
    exact commutator_mem_commutator hl (D.spaceEquiv (Multiplicative.ofAdd w)).property
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha v hv
    let w := D.spaceEquiv.symm ⟨v,hv⟩
    have hw : spaceMap (D := D) w = v := congrArg Subtype.val
      (D.spaceEquiv.apply_symm_apply ⟨v,hv⟩)
    refine ⟨Multiplicative.ofAdd (action m (PointModel.quotientMap m ⟨a,hA ha⟩)
      w.toAdd - w.toAdd), ?_, ?_⟩
    · exact Coinvariants.sub_mem_ker (ρ := (action m).comp (PointModel.image m A).subtype)
        ⟨PointModel.quotientMap m ⟨a,hA ha⟩,⟨⟨a,hA ha⟩,ha,rfl⟩⟩ w.toAdd
    · rw [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, spaceMap_action]
      change a * spaceMap (D := D) w * a⁻¹ * (spaceMap (D := D) w)⁻¹ = _
      rw [hw]
      rfl
  · rintro _ ⟨w,hw,rfl⟩
    exact hc hw

/-- Linear pullback under the original cover equals the original subgroup pullback. -/
theorem preimage_eq (W : Submodule E.input.field.Carrier (Vector E.input.field.Carrier)) :
    ((W.restrictScalars (ZMod 2)).comap (projection m).toLinearMap).toAddSubgroup.toSubgroup.map (spaceMap (D := D)) =
        (Coordinates.sp4 m.action).preimage W := by
  ext x
  constructor
  · rintro ⟨w,hw,rfl⟩
    apply ((Coordinates.sp4 m.action).mem_preimage W (D.spaceEquiv w)).mpr
    change m.action.linearEquiv (Submodule.Quotient.mk
      (D.spaceEquiv.symm (D.spaceEquiv w)).toAdd) ∈ W
    rw [D.spaceEquiv.symm_apply_apply]
    exact hw
  · intro hx
    let v : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
    refine ⟨D.spaceEquiv.symm v,?_,congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v)⟩
    exact ((Coordinates.sp4 m.action).mem_preimage W v).mp hx

/-- The literal root preimage has precisely the conjugate-root quotient image. -/
theorem root_image (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    PointModel.image m (FullAction.rootPreimage (E := E)) =
      (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom := by
  have he : (PointModel.image m (FullAction.rootPreimage (E := E))).map (FullAction.modelHom m) =
      ((RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m) := by
    rw [FullAction.image_eq m _ FullAction.rootPreimage_le, FullAction.rootPreimage_image m,
      FullAction.center_eq_marked_root m g hlocal]
  have hh := congrArg (Subgroup.comap (FullAction.modelHom m)) he
  simpa only [comap_map_eq_self_of_injective (FullAction.modelHom_injective m)] using hh



private theorem moved_mono (A B : Subgroup (Sp E.input.field.Carrier)) (h : A ≤ B) :
    Coinvariants.ker ((action m).comp A.subtype) ≤
      Coinvariants.ker ((action m).comp B.subtype) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a,w⟩,rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := (action m).comp B.subtype) ⟨a.val,h a.property⟩ w

private theorem projection_moved (A : Subgroup (Sp E.input.field.Carrier)) :
    (Coinvariants.ker ((action m).comp A.subtype)).map (projection m).toLinearMap =
      (displacementSpace A).restrictScalars (ZMod 2) := by
  let p : Representation.IntertwiningMap ((action m).comp A.subtype)
      ((restrictScalars (k := ZMod 2)
        (symplecticNatural (k := E.input.field.Carrier) 2)).comp A.subtype) :=
    (projection m).toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun a w => LinearMap.congr_fun ((projection m).isIntertwining' a.val) w)
  have h := map_coinvariants_of_surjective p (Preliminary.markedProjection_isCover D m.action).1
  exact h.trans (coinvariants_restrictScalars ((symplecticNatural 2).comp A.subtype))

/-- The central kernel is already in the root displacement, so the native
radical displacement determines the entire hyperplane preimage. -/
theorem core_moved (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom) :
    Coinvariants.ker ((action m).comp (PointModel.image m (E.L₁.pCoreIn 2)).subtype) =
      ((((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap).restrictScalars (ZMod 2)).comap (projection m).toLinearMap := by
  have hrootle : (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom ≤
      PointModel.image m (E.L₁.pCoreIn 2) := by
    rw [← PointModel.center_identification m g hlocal]
    exact (PointModel.chief_series m g hlocal).2.le
  have hk : (projection m).toLinearMap.ker ≤
      Coinvariants.ker ((action m).comp (PointModel.image m (E.L₁.pCoreIn 2)).subtype) := by
    apply le_trans _ (moved_mono m _ _ hrootle)
    rw [root_moved m g]
    intro w hw
    change projection m w ∈ (point E.input.field.Carrier).map (toLinear g).toLinearMap
    rw [show projection m w = 0 from hw]
    exact Submodule.zero_mem _
  rw [← Submodule.comap_map_eq_self hk, projection_moved, PointModel.core_displacement m g hlocal]

/-- The literal root preimage moves exactly the full original point preimage. -/
theorem root_commutator (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    ⁅V,FullAction.rootPreimage (E := E)⁆ = E.V₁ := by
  rw [commutator_eq m _ FullAction.rootPreimage_le,
    root_image m g (PointModel.local_identification m g hpoint), root_moved, preimage_eq,
    m.point_preimage]
  change (Coordinates.sp4 m.action).preimage _ = (Coordinates.sp4 m.action).preimage _
  rw [hpoint]

/-- The original local two-core moves exactly the full original three-space. -/
theorem radical_commutator (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap) :
    ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃ := by
  rw [commutator_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le),
    core_moved m g (PointModel.local_identification m g hpoint), preimage_eq,
    m.threeSpace_preimage]
  change (Coordinates.sp4 m.action).preimage _ = (Coordinates.sp4 m.action).preimage _
  rw [hthree]

/-- Fixed natural vectors lift to fixed vectors of the nonsplit original cover. -/
theorem root_centralizes_threeSpace (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap) :
    ⁅E.V₃,FullAction.rootPreimage (E := E)⁆ = ⊥ := by
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro a ha v hv
  have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
  let l : L := ⟨a,FullAction.rootPreimage_le ha⟩
  let w : Multiplicative D.space := D.spaceEquiv.symm ⟨v,hvV⟩
  have hw : spaceMap (D := D) w = v :=
    congrArg Subtype.val (D.spaceEquiv.apply_symm_apply _)
  have hv' : projection m w.toAdd ∈
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap := by
    have hvflag : v ∈ m.flag.Vi 2 := by
      rw [← m.threeSpace_preimage]
      exact hv
    have hh := ((Coordinates.sp4 m.action).mem_preimage (m.flag.space 2)
      ⟨v,hvV⟩).mp hvflag
    exact hthree ▸ hh
  have ha' : PointModel.quotientMap m l ∈
      (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom := by
    rw [← root_image m g (PointModel.local_identification m g hpoint)]
    exact ⟨l,ha,rfl⟩
  have hfix : PointModel.quotientMap m l ∈ fixingSubgroup (Sp E.input.field.Carrier)
      (((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier)) := by
    rw [PointRadicalAction.fixer_conjugate, PointRadicalAction.hyperplane_fixer]
    exact ha'
  have he := fixed_of_projection_fixed m (PointModel.quotientMap m l) w.toAdd
    ((mem_fixingSubgroup_iff _).mp hfix _ hv')
  have he' := spaceMap_action m l w.toAdd
  rw [he] at he'
  change spaceMap (D := D) w = l.val * spaceMap (D := D) w * l.val⁻¹ at he'
  rw [hw] at he'
  exact (mul_inv_eq_iff_eq_mul.mp he'.symm).symm

/-- Application to the original closure argument: the cover geometry supplies
both commutator premises used to prove U abelian. The ambient image comparison,
Cartan image, and preceding core bounds belong to their independent producers. -/
theorem U_abelian (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hR : actionImage (V := V) E.R₁ ≤ actionImage (V := V) (E.L₁.pCoreIn 2))
    (hV : V ≤ E.G₁.pCoreIn 2) (hU : E.U ≤ E.G₁.pCoreIn 2)
    (hc : ⁅E.U,E.G₁.pCoreIn 2⁆ ≤ E.V₁) : IsMulCommutative E.U :=
  RadicalAction.U_abelian_of_action_comparisons E m g
    (PointModel.local_identification m g hpoint) hcartan hXL hXG hR hV hU hc
    (root_centralizes_threeSpace m g hpoint hthree)
    (radical_commutator m g hpoint hthree)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CoverGeometry
