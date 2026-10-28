module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import Theory.Representation.SymplecticFourOrthogonalCover.Roots.Conjugates

/-!
# Original-conjugate realization of the symplectic root-cover calculation

The marked chosen module restricts to a central cover of the actual derived
symplectic group. Its projection is unchanged. Under a surjective root-action
map that agrees with ambient conjugation on the literal embedded module,
the coinvariant kernel maps onto the ambient commutator. Applying I.2.3 to
this same projection identifies that commutator with the full field-line
preimage in Vᵍ, including the possibly nonsplit central kernel.

The final small-action consumer uses the proved field-line orbit to obtain
the required ambient alignment. Constructing the root-action map from the
small-action hypotheses remains the separate recognition obligation.

Source: Aschbacher--Smith, I.2.3(1b), printed p.413, applied in the first
claim of 11.2.4, printed p.769.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic

private theorem coinvariants_comp_eq {H J X : Type*} [Group H] [Group J]
    [AddCommGroup X] [Module (ZMod 2) X] (ρ : Representation (ZMod 2) H X)
    (a : J →* H) (ha : Function.Surjective a) :
    Coinvariants.ker (ρ.comp a) = Coinvariants.ker ρ := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨j, x⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (a j) x
  · rintro _ ⟨⟨h, x⟩, rfl⟩
    obtain ⟨j, rfl⟩ := ha h
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp a) j x

private theorem embedded_coinvariants {G H X : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) H X) (A V : Subgroup G)
    (j : Multiplicative X →* G) (hj : j.range = V)
    (a : A →* H) (ha : Function.Surjective a)
    (he : ∀ (w : A) x, j (Multiplicative.ofAdd (σ (a w) x)) =
      w.val * j (Multiplicative.ofAdd x) * w.val⁻¹) :
    (Coinvariants.ker σ).toAddSubgroup.toSubgroup.map j = ⁅A, V⁆ := by
  let C : Submodule (ZMod 2) X := AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm (⁅A, V⁆.comap j))
  have hC : Coinvariants.ker σ ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h, x⟩, rfl⟩
    obtain ⟨w, rfl⟩ := ha h
    change j (Multiplicative.ofAdd (σ (a w) x - x)) ∈ ⁅A, V⁆
    have hsub : Multiplicative.ofAdd (σ (a w) x - x) =
        Multiplicative.ofAdd (σ (a w) x) * (Multiplicative.ofAdd x)⁻¹ := by
      rw [ofAdd_sub, div_eq_mul_inv]
    rw [hsub, map_mul, map_inv, he]
    exact commutator_mem_commutator w.property
      (hj ▸ (show j (Multiplicative.ofAdd x) ∈ j.range from ⟨_, rfl⟩))
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hC hx
  · apply commutator_le.mpr
    intro w hw v hv
    obtain ⟨x, rfl⟩ := (show v ∈ j.range from hj.symm ▸ hv)
    refine ⟨Multiplicative.ofAdd (σ (a ⟨w, hw⟩) x.toAdd - x.toAdd),
      Coinvariants.sub_mem_ker (a ⟨w, hw⟩) x.toAdd, ?_⟩
    rw [ofAdd_sub, div_eq_mul_inv, map_mul, map_inv, he]
    rfl

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original chosen action restricted to the actual symplectic derived group. -/
@[expose] def sp4CoverAction
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    Representation (ZMod 2) (SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) D.space :=
  (Preliminary.markedAction D m).comp (commutator _).subtype

/-- The same original fixed-space projection, with its acting group restricted. -/
@[expose] def sp4CoverProjection
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    (sp4CoverAction D S m).IntertwiningMap
      (SymplecticFourOrthogonalCover.binaryNatural (K := S.field.Carrier)) where
  toLinearMap := (Preliminary.markedProjection D m).toLinearMap
  isIntertwining' h := (Preliminary.markedProjection D m).isIntertwining' h.val

/-- Perfectness makes the restriction a cover over its unchanged projection. -/
theorem sp4CoverProjection_isCover
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    IsCover (sp4CoverProjection D S m) := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  have hp := Preliminary.markedProjection_isCover D m
  refine ⟨hp.1, ?_, ?_⟩
  · intro x hx h
    exact hp.2.1 hx h.val
  · change Coinvariants.ker ((Preliminary.markedAction D m).comp (commutator _).subtype) = ⊤
    rw [coinvariants_comp_eq _ _ (fun h => ⟨⟨h, Group.IsPerfect.mem_commutator⟩, rfl⟩)]
    exact hp.2.2

/-- The inclusion of the chosen module, followed by the original conjugation. -/
@[expose] def conjugateSpaceMap (g : G) : Multiplicative D.space →* G :=
  (MulAut.conj g).toMonoidHom.comp (V.subtype.comp D.spaceEquiv.toMonoidHom)

omit [Finite G] in
theorem conjugateSpaceMap_range (g : G) :
    (conjugateSpaceMap D g).range = V.map (MulAut.conj g).toMonoidHom := by
  rw [conjugateSpaceMap, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr D.spaceEquiv.surjective]
  have hV : (⊤ : Subgroup V).map V.subtype = V := by
    ext x
    exact ⟨fun ⟨v, _, hv⟩ => hv ▸ v.property, fun hx => ⟨⟨x, hx⟩, mem_top _, rfl⟩⟩
  rw [hV]

/-- Applying I.2.3 to an actual root action gives the full preimage in the
original conjugate, without a splitting or a kernel-containment premise. -/
theorem commutator_preimage_of_sp4_root_action
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (g : G) (W : Subgroup G)
    (z : SymplecticFourOrthogonalCover.L (K := S.field.Carrier))
    (a : W →* SymplecticFourOrthogonalCover.Roots.conjugateGroup z)
    (ha : Function.Surjective a)
    (hact : ∀ (w : W) x,
      conjugateSpaceMap D g (Multiplicative.ofAdd (sp4CoverAction D S m (a w).val x)) =
        w.val * conjugateSpaceMap D g (Multiplicative.ofAdd x) * w.val⁻¹) :
    ⁅W, V.map (MulAut.conj g).toMonoidHom⁆ =
      ((Coordinates.sp4 m).preimage (SymplecticFourOrthogonalCover.Roots.conjugateLine z)).map
        (MulAut.conj g).toMonoidHom := by
  have hcard : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    have hp := pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) S.nonbinary
    simpa only [pow_one] using hp
  have hr := (SymplecticFourOrthogonalCover.Roots.cover_conjugate_root_geometry
    hcard z (sp4CoverProjection D S m) (sp4CoverProjection_isCover D S m)).2.1
  rw [← embedded_coinvariants
    ((sp4CoverAction D S m).comp (SymplecticFourOrthogonalCover.Roots.conjugateGroup z).subtype)
    W _ (conjugateSpaceMap D g) (conjugateSpaceMap_range D g) a ha hact, ← hr]
  rw [conjugateSpaceMap, ← map_map, ← map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    apply ((Coordinates.sp4 m).mem_preimage _ (D.spaceEquiv w)).mpr
    change m.linearEquiv (Submodule.Quotient.mk
      (D.spaceEquiv.symm (D.spaceEquiv w)).toAdd) ∈ _
    rw [D.spaceEquiv.symm_apply_apply]
    exact hw
  · intro hx
    let v : V := ⟨x, D.centralQuotientPreimage_le _ hx⟩
    refine ⟨v, ⟨D.spaceEquiv.symm v, ?_, D.spaceEquiv.apply_symm_apply v⟩, rfl⟩
    exact ((Coordinates.sp4 m).mem_preimage _ v).mp hx

/-- The root direction is a field line in the original symplectic marking. -/
theorem sp4_root_line_finrank
    (z : SymplecticFourOrthogonalCover.L (K := S.field.Carrier)) :
    Module.finrank S.field.Carrier
      (SymplecticFourOrthogonalCover.Roots.conjugateLine z) = 1 := by
  rw [SymplecticFourOrthogonalCover.Roots.conjugateLine,
    ← (Submodule.equivMapOfInjective (symplecticDerivedNatural 2 z)
      ((symplecticDerivedNatural (k := S.field.Carrier) 2).apply_bijective z).1
      SymplecticFourOrthogonalCover.firstLine).finrank_eq]
  apply finrank_span_singleton
  intro hz
  have h := congrFun hz (.inl 0)
  simp [ClassicalOrthogonal.e] at h

/-- Actual source consumer of the nonsplit root-cover calculation. A faithful
root-action recognition still has to construct the surjection and its literal
ambient action equation; no commutator or central-kernel conclusion is assumed. -/
theorem sp4_small_alignment_of_root_action
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (W : Subgroup G)
    (hsmall : SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W)
    (z : SymplecticFourOrthogonalCover.L (K := S.field.Carrier))
    (a : W →* SymplecticFourOrthogonalCover.Roots.conjugateGroup z)
    (ha : Function.Surjective a)
    (hact : ∀ (w : W) x,
      conjugateSpaceMap D g (Multiplicative.ofAdd (sp4CoverAction D S m (a w).val x)) =
        w.val * conjugateSpaceMap D g (Multiplicative.ofAdd x) * w.val⁻¹) :
    Alignment (f.Vi 0) V g := by
  apply alignment_of_small_commutator_line f hG2 g hsmall
  exact ⟨SymplecticFourOrthogonalCover.Roots.conjugateLine z,
    sp4_root_line_finrank D S z, commutator_preimage_of_sp4_root_action D S m g W z a ha hact⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
