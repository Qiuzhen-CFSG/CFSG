module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Marking

/-!
# Scalar action on the literal common plane

The ordered orthogonal marking gives the same additive section marking and
shows that the two quotient factors commute on P. Restricting a first-factor
Cartan actor to P intersect V and applying the natural SL2 commutant calculation
makes it scalar for precisely the constructed compatible field on P. This uses
action commutation, not commutation of the original ambient elements.

The source application retains D, S, the SL3 marking and the original flag.
Earlier core and action geometry are explicit outputs of the common-core and
marked-section owners. No scalar or spectrum premise is introduced.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights

private theorem scalar_on_natural_range {F M : Type*} [Field F] [AddCommGroup M]
    (e : (Fin 2 → F) →+ M) (he : Function.Injective e) (t : M →+ M)
    (hi : ∀ v, ∃ w, e w = t (e v))
    (α : Matrix.SpecialLinearGroup (Fin 2) F → M →+ M)
    (ha : ∀ g v, e (g.val.mulVec v) = α g (e v))
    (hc : ∀ g v, t (α g v) = α g (t v)) :
    ∃ c : F, ∀ v, t (e v) = e (c • v) := by
  let s : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => (hi v).choose
      map_zero' := by
        apply he
        rw [(hi 0).choose_spec, map_zero, map_zero]
      map_add' := by
        intro v w
        apply he
        rw [(hi (v + w)).choose_spec, map_add, map_add, map_add,
          (hi v).choose_spec, (hi w).choose_spec] }
  have hs (v) : e (s v) = t (e v) := (hi v).choose_spec
  obtain ⟨c, hcs⟩ := SL2NaturalOffenders.centralizer_scalar s (by
    intro g v
    apply he
    rw [hs, ha, hc, ha, hs])
  exact ⟨c, fun v => (hs v).symm.trans (congrArg e (hcs v))⟩

open CFSG.Quasithin.ChapterB.QuasisimpleSource
section Ordered
variable {G : Type*} [Group G] {E : BinaryField} {Y P K A : Subgroup G}
    [IsMulCommutative P] (o : CommonCore.OrthogonalMarking Y P K A E)

/-- Forget the ordered factors while retaining precisely the same projection
and additive coordinates on the original P. -/
def orderedSection : MarkedSections.OrthogonalMarking E P Y where
  core_le := o.core_le
  actors := o.projection
  surjective := o.surjective
  kernel := o.kernel
  coordinates := o.coordinates.toAdditiveLeft
  intertwines y v := by
    have h : o.coordinates
        (P.normalizerMonoidHom (inclusion o.normalizes y)
          (o.coordinates.symm (Multiplicative.ofAdd v))) =
        Multiplicative.ofAdd (ClassicalOrthogonal.FourPlusMatrix.matrixAction (o.projection y) v) := by
      apply Multiplicative.toAdd.injective
      simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
        o.intertwines y (o.coordinates.symm (Multiplicative.ofAdd v))
    have hh := congrArg o.coordinates.symm h
    rw [MulEquiv.symm_apply_apply] at hh
    exact congrArg (fun p : P => (p : G)) hh.symm

/-- The ordered quotient factors commute on P; no ambient commutation is asserted. -/
theorem ordered_first_commutes (y : Y) (hy : (y : G) ∈ K) (a : A) (p : Additive P) :
    let := (orderedSection o).moduleStructure
    (orderedSection o).action y ((orderedSection o).action ⟨a,o.second_le a.property⟩ p) =
      (orderedSection o).action ⟨a,o.second_le a.property⟩ ((orderedSection o).action y p) := by
  let := (orderedSection o).moduleStructure
  have hfirst : (o.projection y).2 = 1 := by
    have h := mem_map_of_mem o.projection (show y ∈ K.subgroupOf Y from hy)
    rw [o.first_factor] at h
    exact h
  have hsecond : (o.projection ⟨a,o.second_le a.property⟩).1 = 1 := by
    have h := mem_map_of_mem o.projection
      (show (⟨a,o.second_le a.property⟩ : Y) ∈ A.subgroupOf Y from a.property)
    rw [o.second_factor] at h
    exact h
  have hc : Commute (o.projection y) (o.projection ⟨a,o.second_le a.property⟩) := by
    apply Prod.ext <;> simp [hfirst,hsecond]
  let e := ((orderedSection o).coordinates.linearEquiv E.Carrier)
  have hh := congrArg (fun t : Module.End E.Carrier (ClassicalOrthogonal.FourPlusMatrix.Mat
    (F := E.Carrier)) => t (e p))
      (hc.map ClassicalOrthogonal.FourPlusMatrix.representation).eq
  apply e.injective
  have he (z : Y) (v : Additive P) : e ((orderedSection o).action z v) =
      ClassicalOrthogonal.FourPlusMatrix.representation (o.projection z) (e v) :=
    e.apply_symm_apply _
  rw [he,he,he,he]
  exact hh
end Ordered

section Separate
variable {G E F : Type*} [Group G] [Field E] [Field F] [Finite F]
    {P V A Y : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
    [Module E (Additive P)] [Module F (Additive V)]
    (d : SeparatePlaneActions (E := E) (F := F) P V A)
    (hc : Nat.card E = Nat.card F)
    (ρ : Representation E Y (Additive P))
    (hρ : ∀ (y : Y) (p : Additive P),
      ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G))

include hρ in
/-- A plane-preserving actor commuting with the actual natural action is
scalar for the canonical compatible field. -/
theorem common_plane_scalar (y : Y)
    (hn : (y : G) ∈ normalizer ((P ⊓ V : Subgroup G) : Set G))
    (hcomm : ∀ (a : A) (p : Additive P), ρ y (d.action a p) = d.action a (ρ y p)) :
    let := d.compatibleModule hc
    ∃ c : F, ∀ p : Additive P, (p.toMul : G) ∈ V →
      d.restrictionDatum.compatibleRepresentation hc ρ y p = c • p := by
  let := d.compatibleModule hc
  have hi : Function.Injective d.inclusion := by
    intro v w h
    apply d.plane.symm.injective
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun p : Additive P => (p.toMul : G)) h
  have hp (v : Fin 2 → F) : ∃ w, d.inclusion w = ρ y (d.inclusion v) := by
    have hm : ((ρ y (d.inclusion v)).toMul : G) ∈ P ⊓ V := by
      rw [hρ]
      exact (mem_normalizer_iff.mp hn _).mp (d.plane.symm v).toMul.property
    let z : Additive (P ⊓ V : Subgroup G) := Additive.ofMul
      ⟨(ρ y (d.inclusion v)).toMul, hm⟩
    refine ⟨d.plane z, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((d.plane.symm (d.plane z)).toMul : G) = _
    rw [d.plane.symm_apply_apply]
    rfl
  obtain ⟨c,hc'⟩ := scalar_on_natural_range d.inclusion hi (ρ y).toAddMonoidHom hp
    (fun g => (d.restrictionDatum.actor g).toAddMonoidHom)
    d.restrictionDatum.intertwines (fun g p => hcomm _ p)
  refine ⟨c,fun p hp => ?_⟩
  let z : Additive (P ⊓ V : Subgroup G) := Additive.ofMul ⟨p.toMul,p.toMul.property,hp⟩
  have hz : d.inclusion (d.plane z) = p := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((d.plane.symm (d.plane z)).toMul : G) = _
    rw [d.plane.symm_apply_apply]
    rfl
  change ρ y p = c • p
  rw [←hz]
  exact (hc' (d.plane z)).trans (d.restrictionDatum.compatible_smul hc c (d.plane z)).symm
end Separate

section Source
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) {P I K X : Subgroup G}
    [IsMulCommutative P] [IsMulCommutative V]
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (E : BinaryField) (o : CommonCore.OrthogonalMarking (f.Li 1 ⊔ I) P K (f.Li 1) E)
    (hcard : Nat.card E.Carrier = Nat.card S.field.Carrier)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = f.Vi 1) (hVI : V ≤ I)
    (hX : IsCartan T L X) (hXY : X ≤ f.Li 1 ⊔ I)

include hX in
/-- Every actual X-intersect-K actor is scalar on the literal V₂, with the
field on P constructed from the two separate source markings. -/
theorem source_common_plane_scalar (y : (X ⊓ K : Subgroup G)) :
    let := originalModule D (.sl3 m) hfixed
    let s := orderedSection o
    let := s.moduleStructure
    let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
    let := d.compatibleModule hcard
    let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
    ∃ a : S.field.Carrier, ∀ p ∈ SeparatePlaneActions.fixedPlane (V := V) σ,
      σ ⟨y,hXY y.property.1⟩ p = a • p := by
  let := originalModule D (.sl3 m) hfixed
  let s := orderedSection o
  let := s.moduleStructure
  let d := MarkedSections.extractedPlaneActions D S m f P I hfixed E s hP hcore hPV hVI
  let := d.compatibleModule hcard
  let σ := d.restrictionDatum.compatibleRepresentation hcard s.action
  have hn : (y : G) ∈ normalizer ((P ⊓ V : Subgroup G) : Set G) := by
    rw [hPV]
    exact MarkedSections.cartan_normalizes_plane D S m f hX y.property.1
  obtain ⟨a,ha⟩ := common_plane_scalar d hcard s.action s.action_conj
    ⟨y,hXY y.property.1⟩ hn (fun a p => ordered_first_commutes o _ y.property.2 a p)
  refine ⟨a,fun p hp => ha p ?_⟩
  exact (SeparatePlaneActions.mem_fixedPlane σ s.action_conj (hVI.trans le_sup_right)
    (MarkedSections.fixed_plane D S m f P hP hcore) p).mp hp
end Source
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
