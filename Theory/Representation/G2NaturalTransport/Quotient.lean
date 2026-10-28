module

public import Theory.Representation.G2NaturalTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.SubspaceQuotient

/-!
# The literal natural quotient under its original ambient group

A full G₂ marking and its compatible normal derived marking act on the
literal quotient V/C_V(L). The derived natural action has no fixed vectors,
so C_V(L)=C_V(H). Normality of H therefore makes the original denominator
ambient invariant, even without assuming normality of L.

The induced action keeps the original quotient map. Its commutant, ambient
semilinearity and nonzero orbit follow from the concrete derived action.
Fixed spaces, their quotient maps and offender comparisons transport using
the full L-marking, preserving the distinction at field order two.
The Layer extension constructs the derived marking from the full one.

Source: Aschbacher--Smith I.2.3, p.413, and B.4.6, pp.88--90. These results
concern the natural quotient; they do not assert that every quotient fixed
vector lifts to a fixed vector in an arbitrary covering module.
-/

@[expose] public section

namespace Atlas.G2.Natural.Transport
open Representation Representation.BinaryOffender
noncomputable section
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A marking of the source natural quotient. Both the full group and its
normal derived subgroup are marked, and the two maps commute with inclusion. -/
structure QuotientMarking (ρ : Representation (ZMod 2) G V) (L H : Subgroup G) where
  le : H ≤ L
  full : L ≃* Model F
  derived : H ≃* commutator (Model F)
  compatible : ∀ h : H, (derived h).val = full ⟨h, le h.property⟩
  quotient : (V ⧸ fixedSpace ρ L) ≃ₗ[ZMod 2] Space F
  intertwines : ∀ l : L, ∀ v,
    quotient ((fixedSpace ρ L).mkQ (ρ l v)) =
      action F (full l) (quotient ((fixedSpace ρ L).mkQ v))

namespace QuotientMarking
variable {ρ : Representation (ZMod 2) G V} {L H : Subgroup G}
  (d : QuotientMarking (F := F) ρ L H)

omit [Finite F] in
/-- Restriction uses the actual derived embedding, including over F₂. -/
theorem intertwines_derived (h : H) (v : V) :
    d.quotient ((fixedSpace ρ L).mkQ (ρ h v)) =
      derivedAction F (d.derived h) (d.quotient ((fixedSpace ρ L).mkQ v)) := by
  rw [derivedAction_apply, d.compatible]
  exact d.intertwines ⟨h, d.le h.property⟩ v

include d in
/-- The source denominator is the fixed space of the normal derived subgroup.
This follows from the fixed-point-free natural quotient, without normality of L. -/
theorem fixedSpace_eq : fixedSpace ρ L = fixedSpace ρ H := by
  apply le_antisymm
  · intro v hv h
    exact hv ⟨h, d.le h.property⟩
  · intro v hv
    apply (Submodule.Quotient.mk_eq_zero (fixedSpace ρ L)).mp
    apply d.quotient.map_eq_zero_iff.mp
    apply fixed_eq_zero
    intro g
    obtain ⟨h, rfl⟩ := d.derived.surjective g
    change derivedAction F (d.derived h) (d.quotient ((fixedSpace ρ L).mkQ v)) = _
    rw [← d.intertwines_derived, show ρ h v = v from hv h]
    rfl

/-- The original denominator, now proved stable under the ambient group. -/
def kernel [H.Normal] : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ L
  apply_mem_toSubmodule g := by
    change fixedSpace ρ L ≤ (fixedSpace ρ L).comap (ρ g)
    rw [d.fixedSpace_eq]
    exact Representation.le_comap_invariants ρ H g

/-- The induced action on the literal V/C_V(L), with its original quotient map. -/
abbrev quotientAction [H.Normal] : Representation (ZMod 2) G (V ⧸ fixedSpace ρ L) :=
  d.kernel.quotientRepresentation

@[simp] theorem quotientAction_mk [H.Normal] (g : G) (v : V) :
    d.quotientAction g ((fixedSpace ρ L).mkQ v) = (fixedSpace ρ L).mkQ (ρ g v) := rfl

theorem quotient_equivariant [H.Normal] (l : L) (x : V ⧸ fixedSpace ρ L) :
    d.quotient (d.quotientAction l x) = action F (d.full l) (d.quotient x) := by
  obtain ⟨v, rfl⟩ := (fixedSpace ρ L).mkQ_surjective x
  exact d.intertwines l v

theorem quotient_derived_equivariant [H.Normal] (h : H) (x : V ⧸ fixedSpace ρ L) :
    d.quotient (d.quotientAction h x) = derivedAction F (d.derived h) (d.quotient x) := by
  obtain ⟨v, rfl⟩ := (fixedSpace ρ L).mkQ_surjective x
  exact d.intertwines_derived h v

/-- B.4.6(2) on the literal source quotient; the witness lies in L. -/
theorem transitive [H.Normal] {x y : V ⧸ fixedSpace ρ L} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ l : L, d.quotientAction l x = y := by
  obtain ⟨h, hh⟩ := Transport.transitive (d.quotientAction.comp H.subtype)
    d.derived d.quotient d.quotient_derived_equivariant hx hy
  exact ⟨⟨h, d.le h.property⟩, hh⟩

/-- The source quotient's additive L-commutant is precisely the transported field. -/
theorem scalar_commutant [H.Normal] (f : (V ⧸ fixedSpace ρ L) →+ (V ⧸ fixedSpace ρ L))
    (hf : ∀ l : L, ∀ x, f (d.quotientAction l x) = d.quotientAction l (f x)) :
    ∃ c : F, ∀ x, d.quotient (f x) = c • d.quotient x :=
  Transport.scalar_commutant (d.quotientAction.comp H.subtype) d.derived d.quotient
    d.quotient_derived_equivariant f (fun h x => hf ⟨h, d.le h.property⟩ x)

/-- I.2.3's semilinearity mechanism applies to the original ambient quotient action. -/
theorem semilinear [H.Normal] (g : G) :
    ∃ s : F ≃+* F, ∀ c x,
      d.quotient (d.quotientAction g (d.quotient.symm (c • d.quotient x))) =
        s c • d.quotient (d.quotientAction g x) :=
  ambient_semilinear H d.quotientAction d.derived d.quotient d.quotient_derived_equivariant g

/-- Fixed spaces for every subgroup of the full L, not just of E(L). -/
theorem fixedSpace_map [H.Normal] (A : Subgroup L) :
    (fixedSpace d.quotientAction (A.map L.subtype)).map d.quotient.toLinearMap =
      fixedSpace (restrictScalars (k := ZMod 2) (action F)) (A.map d.full.toMonoidHom) := by
  rw [← fixedSpace_comp_map]
  exact fixedSpace_map_equivariant (d.quotientAction.comp L.subtype)
    (restrictScalars (k := ZMod 2) (action F)) d.full.toMonoidHom d.quotient
    d.quotient_equivariant A

/-- An actual equivalence of fixed-space quotients, retaining the ambient inclusion. -/
def fixedQuotientEquiv [H.Normal] (A : Subgroup L) :
    ((V ⧸ fixedSpace ρ L) ⧸ fixedSpace d.quotientAction (A.map L.subtype)) ≃ₗ[ZMod 2]
      (Space F ⧸ fixedSpace (restrictScalars (k := ZMod 2) (action F))
        (A.map d.full.toMonoidHom)) :=
  Submodule.Quotient.equiv _ _ d.quotient (d.fixedSpace_map A)

@[simp] theorem fixedQuotientEquiv_mk [H.Normal] (A : Subgroup L)
    (x : V ⧸ fixedSpace ρ L) :
    d.fixedQuotientEquiv A ((fixedSpace d.quotientAction (A.map L.subtype)).mkQ x) =
      (fixedSpace (restrictScalars (k := ZMod 2) (action F))
        (A.map d.full.toMonoidHom)).mkQ (d.quotient x) := rfl

theorem fixedCodim_eq [H.Normal] (A : Subgroup L) :
    fixedCodim d.quotientAction (A.map L.subtype) =
      fixedCodim (restrictScalars (k := ZMod 2) (action F)) (A.map d.full.toMonoidHom) :=
  (d.fixedQuotientEquiv A).finrank_eq

/-- Source offender comparisons use the full L-marking, even in the binary case. -/
theorem offender_forward [H.Normal] {A : Subgroup L}
    (hA : IsOffender (d.quotientAction.comp L.subtype) A) :
    IsOffender (restrictScalars (k := ZMod 2) (action F)) (A.map d.full.toMonoidHom) :=
  hA.map_equivariant _ _ d.full.toMonoidHom d.full.injective d.quotient d.quotient_equivariant

end QuotientMarking
end
end Atlas.G2.Natural.Transport

namespace Atlas.G2.Natural.Transport.QuotientMarking
open Representation Representation.BinaryOffender
noncomputable section
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L H : Subgroup G} [H.Normal]
  (d : QuotientMarking (F := F) ρ L H)

private theorem inverse_equivariant (g : Model F) (v : Space F) :
    d.quotient.symm (action F g v) =
      d.quotientAction (d.full.symm g) (d.quotient.symm v) := by
  apply d.quotient.injective
  rw [d.quotient.apply_symm_apply, d.quotient_equivariant,
    d.full.apply_symm_apply, d.quotient.apply_symm_apply]

/-- Both directions of offender transport for the whole G₂ group. -/
theorem offender_iff (A : Subgroup L) :
    IsOffender (d.quotientAction.comp L.subtype) A ↔
      IsOffender (restrictScalars (k := ZMod 2) (action F)) (A.map d.full.toMonoidHom) := by
  constructor
  · exact d.offender_forward
  · intro h
    have hh := IsOffender.map_equivariant
      (restrictScalars (k := ZMod 2) (action F)) (d.quotientAction.comp L.subtype)
      d.full.symm.toMonoidHom d.full.symm.injective d.quotient.symm d.inverse_equivariant h
    have he : d.full.symm.toMonoidHom.comp d.full.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro g
      exact d.full.symm_apply_apply g
    simpa only [Subgroup.map_map, he, Subgroup.map_id] using hh

/-- Best-offender comparisons over all subgroups are preserved by the same marking. -/
theorem bestOffender_iff (A : Subgroup L) :
    IsBestOffender (d.quotientAction.comp L.subtype) A ↔
      IsBestOffender (restrictScalars (k := ZMod 2) (action F)) (A.map d.full.toMonoidHom) := by
  let : Module.Finite (ZMod 2) (V ⧸ fixedSpace ρ L) := Module.Finite.equiv d.quotient.symm
  constructor
  · intro h
    exact IsBestOffender.map_of_fixedCodim (d.quotientAction.comp L.subtype)
      (restrictScalars (k := ZMod 2) (action F)) d.full.toMonoidHom d.full.injective
      (fixedCodim_map_equivariant _ _ d.full.toMonoidHom d.quotient d.quotient_equivariant) h
  · intro h
    have hh := IsBestOffender.map_of_fixedCodim
      (restrictScalars (k := ZMod 2) (action F)) (d.quotientAction.comp L.subtype)
      d.full.symm.toMonoidHom d.full.symm.injective
      (fixedCodim_map_equivariant _ _ d.full.symm.toMonoidHom
        d.quotient.symm d.inverse_equivariant) h
    have he : d.full.symm.toMonoidHom.comp d.full.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro g
      exact d.full.symm_apply_apply g
    simpa only [Subgroup.map_map, he, Subgroup.map_id] using hh

/-- Every transported scalar commutes, so the commutant statement is an equality,
not just a necessary condition on commuting maps. -/
theorem commutes_iff_scalar (f : (V ⧸ fixedSpace ρ L) →+ (V ⧸ fixedSpace ρ L)) :
    (∀ l : L, ∀ x, f (d.quotientAction l x) = d.quotientAction l (f x)) ↔
      ∃ c : F, ∀ x, d.quotient (f x) = c • d.quotient x := by
  constructor
  · exact d.scalar_commutant f
  · rintro ⟨c, hc⟩ l x
    apply d.quotient.injective
    rw [hc, d.quotient_equivariant, d.quotient_equivariant, hc, map_smul]
end
end Atlas.G2.Natural.Transport.QuotientMarking
