module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.Reductions
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# Field-line transport for the first claim in 11.2.4

The actual SL₃ and Sp₄ markings give transitivity on field lines. The
coordinate projection intertwines conjugation by the original component,
so its full preimages have equal orders. If root recognition identifies
[W,A] with such a preimage in A, the small-action quotient condition
therefore forces [W,A] = V₁ upstairs. Conjugating the original line orbit
by g supplies the required element of N_G(A). No splitting of C_V(L) is
used. Recognition of that full preimage remains a separate obligation.

Source: Aschbacher--Smith, 11.2.4, printed p.769, first claim.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Conjugating a full preimage in the actual component is the preimage of
its image under the same marked field action. -/
theorem preimage_map_component (c : Coordinates D S.field)
    (U : Submodule S.field.Carrier c.Space) (l : L) :
    (c.preimage U).map (MulAut.conj (l : G)).toMonoidHom =
      c.preimage (U.map (c.modelAction (c.quotientMap l))) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    apply (c.mem_preimage _ (V.normalizerMonoidHom (inclusion D.normalizes l) v')).mpr
    change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v')).toAdd ∈ _
    rw [c.projection_component_conjugation]
    exact Submodule.mem_map_of_mem ((c.mem_preimage U v').mp hv)
  · intro hx
    let x' : V := ⟨x, D.centralQuotientPreimage_le _ hx⟩
    obtain ⟨u, hu, he⟩ := (c.mem_preimage _ x').mp hx
    let w := V.normalizerMonoidHom (inclusion D.normalizes l⁻¹) x'
    have hw : (w : G) ∈ c.preimage U := by
      apply (c.mem_preimage U w).mpr
      change (c.projection w).toAdd ∈ U
      dsimp only [w]
      rw [c.projection_component_conjugation, map_inv]
      change c.modelAction (c.quotientMap l)⁻¹ (c.projection x').toAdd ∈ U
      change c.modelAction (c.quotientMap l) u = (c.projection x').toAdd at he
      rw [← he, inv_self_apply]
      exact hu
    refine ⟨w, hw, ?_⟩
    change (V.normalizerMonoidHom (inclusion D.normalizes l) w : G) = x
    have hwx : V.normalizerMonoidHom (inclusion D.normalizes l) w = x' := by
      change V.normalizerMonoidHom (inclusion D.normalizes l)
        (V.normalizerMonoidHom (inclusion D.normalizes l⁻¹) x') = x'
      rw [map_inv, map_inv]
      exact MulEquiv.apply_symm_apply _ _
    exact congrArg Subtype.val hwx

private theorem line_map_of_transitive
    {k H M : Type*} [Field k] [Group H] [AddCommGroup M] [Module k M]
    (ρ : Representation k H M)
    (htrans : ∀ x y : M, x ≠ 0 → y ≠ 0 → ∃ h, ρ h x = y)
    (U W : Submodule k M) (hU : Module.finrank k U = 1)
    (hW : Module.finrank k W = 1) : ∃ h, U.map (ρ h) = W := by
  obtain ⟨u, hu0, hu⟩ := (finrank_eq_one_iff').mp hU
  obtain ⟨w, hw0, hw⟩ := (finrank_eq_one_iff').mp hW
  have hu0' : (u : M) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hw0' : (w : M) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨h, hh⟩ := htrans u w hu0' hw0'
  refine ⟨h, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := hu ⟨y, hy⟩
    have he : y = a • (u : M) := (congrArg Subtype.val ha).symm
    rw [he, map_smul, hh]
    exact W.smul_mem a w.property
  · intro hx
    obtain ⟨a, ha⟩ := hw ⟨x, hx⟩
    refine ⟨a • u.val, U.smul_mem a u.property, ?_⟩
    rw [map_smul, hh]
    exact congrArg Subtype.val ha

/-- The two surviving natural models are transitive on field lines. -/
theorem field_line_orbit (c : Coordinates D S.field)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (U W : Submodule S.field.Carrier c.Space)
    (hU : Module.finrank S.field.Carrier U = 1)
    (hW : Module.finrank S.field.Carrier W = 1) :
    ∃ l : L, (c.preimage U).map (MulAut.conj (l : G)).toMonoidHom = c.preimage W := by
  have ht : ∀ x y : c.Space, x ≠ 0 → y ≠ 0 →
      ∃ h : c.ModelGroup, c.modelAction h x = y := by
    cases c with
    | sl3 m =>
      intro x y hx hy
      exact Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy
    | sp4 m =>
      intro x y hx hy
      exact Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive hx hy
    | g2 m => exact (hG2 ⟨m⟩).elim
  obtain ⟨h, hh⟩ := line_map_of_transitive c.modelAction ht U W hU hW
  obtain ⟨l, rfl⟩ := c.quotientMap_surjective h
  exact ⟨l, (preimage_map_component c U l).trans (congrArg c.preimage hh)⟩

/-- A recognized line in the actual conjugate has the same order as V₁.
Consequently the original quotient-line condition gives equality upstairs,
including the entire possibly nonsplit central kernel. -/
theorem small_commutator_eq_point {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) {W : Subgroup G}
    (hsmall : SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W)
    (U : Submodule S.field.Carrier c.Space) (hU : Module.finrank S.field.Carrier U = 1)
    (hcomm : ⁅W, V.map (MulAut.conj g).toMonoidHom⁆ =
      (c.preimage U).map (MulAut.conj g).toMonoidHom) :
    ⁅W, V.map (MulAut.conj g).toMonoidHom⁆ = f.Vi 0 := by
  obtain ⟨l, hl⟩ := field_line_orbit c hG2 U (f.space 0) hU (f.dimension 0)
  apply Subgroup.eq_of_le_of_card_ge
  · exact le_sup_left.trans hsmall.quotient_line.le
  · rw [hcomm, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    change Nat.card (c.preimage (f.space 0)) ≤ Nat.card (c.preimage U)
    rw [← hl, Subgroup.card_map_of_injective (MulAut.conj (l : G)).injective]

/-- Transport the field-line orbit into the normalizer of the same conjugate.
The conjugator is g*l*g⁻¹, as required by the left-conjugation convention. -/
theorem alignment_of_conjugate_line {c : Coordinates D S.field} (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) (U : Submodule S.field.Carrier c.Space)
    (hU : Module.finrank S.field.Carrier U = 1)
    (he : (c.preimage U).map (MulAut.conj g).toMonoidHom = f.Vi 0) :
    Alignment (f.Vi 0) V g := by
  obtain ⟨l, hl⟩ := field_line_orbit c hG2 (f.space 0) U (f.dimension 0) hU
  have hn : (l : G) ∈ normalizer (V : Set G) := D.normalizes l.property
  refine ⟨g * l * g⁻¹, ?_, ?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (g * (l : G) * g⁻¹)).toMonoidHom = _
    rw [offender_map_conj_map]
    have heq : g * (l : G) * g⁻¹ * g = g * l := by group
    rw [heq, ← offender_map_conj_map]
    have hlV : V.map (MulAut.conj (l : G)).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [hlV]
  · rw [offender_map_conj_map]
    have heq : g * (l : G) * g⁻¹ * g = g * l := by group
    rw [heq, ← offender_map_conj_map]
    change ((c.preimage (f.space 0)).map _).map _ = _
    rw [hl, he]

/-- Root recognition need only identify the commutator as a full preimage of
a field line in the conjugate. Equality with V₁ and alignment are proved here. -/
theorem alignment_of_small_commutator_line {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (g : G) {W : Subgroup G}
    (hsmall : SmallSymmetricAction f (V.map (MulAut.conj g).toMonoidHom) W)
    (hline : ∃ U : Submodule S.field.Carrier c.Space,
      Module.finrank S.field.Carrier U = 1 ∧
      ⁅W, V.map (MulAut.conj g).toMonoidHom⁆ =
        (c.preimage U).map (MulAut.conj g).toMonoidHom) :
    Alignment (f.Vi 0) V g := by
  obtain ⟨U, hU, hc⟩ := hline
  exact alignment_of_conjugate_line f hG2 g U hU
    (hc.symm.trans (small_commutator_eq_point f hG2 g hsmall U hU hc))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
