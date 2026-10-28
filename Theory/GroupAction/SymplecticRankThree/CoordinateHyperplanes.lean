module
public import Theory.GroupAction.SymplecticRankThree.PolarityDesign
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.Incidence
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Lines

/-!
# Hyperplanes and the transported null polarity

Ordinary projective line coordinates transport each source block to a vector
subspace. The source block cardinality proves that its dimension is three.
Taking its perpendicular in the standard four-space constructs its native
pole. Distinct blocks have distinct poles, and finite cardinality makes the
pole map bijective. Double perpendiculars recover lines, so composing this
polarity with the native polarity gives a projective collineation. Every point
is absolute because the original incidence is reflexive.

No orthogonality formula for the supplied line coordinates is assumed.
Constructing those ordinary coordinates from the incidence geometry remains
necessary. These results realize the duality part of Higman's Lemma 10 and
Theorem 2(i), *Finite permutation groups of rank 3* (1964), pp.153–154.
-/

public noncomputable section
open Projectivization Module
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω F : Type*} [Finite Ω] [Field F] [Finite F]
variable (D : PolarityDesign Ω (Nat.card F)) (C : Ω ≃ ProjectivePoint F)
variable (hC : ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔ z ∈ D.line x y)

/-- The vector hyperplane obtained from one incidence block. -/
@[expose] def coordinateBlock (a : Ω) : Submodule F (Vector F) where
  carrier := {v | ∀ hv : v ≠ 0, D.incident a (C.symm (Projectivization.mk F v hv))}
  zero_mem' := fun h => (h rfl).elim
  add_mem' := by
    intro v w hp hq hvw
    by_cases hv : v = 0
    · subst v
      simpa only [zero_add] using hq (by simpa only [zero_add] using hvw)
    by_cases hw : w = 0
    · subst w
      simpa only [add_zero] using hp (by simpa only [add_zero] using hvw)
    apply (hC (C.symm (Projectivization.mk F v hv)) (C.symm (Projectivization.mk F w hw)) (C.symm (Projectivization.mk F (v+w) hvw))).mp ?_ a (hp hv) (hq hw)
    simp only [C.apply_symm_apply,submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  smul_mem' := by
    intro c v hp hcv
    have hv : v ≠ 0 := right_ne_zero_of_smul hcv
    have he : Projectivization.mk F (c • v) hcv = Projectivization.mk F v hv := (mk_eq_mk_iff' F _ _ _ _).mpr ⟨c,rfl⟩
    simpa only [he] using hp hv

omit [Finite F] in
@[simp] theorem le_coordinateBlock_iff (a x : Ω) :
    (C x).submodule ≤ D.coordinateBlock C hC a ↔ D.incident a x := by
  rw [← mk_rep (C x),submodule_mk,Submodule.span_singleton_le_iff_mem]
  change (∀ hv, D.incident a (C.symm (Projectivization.mk F (C x).rep hv))) ↔ _
  simp only [mk_rep,C.symm_apply_apply]
  exact ⟨fun h => h (C x).rep_nonzero,fun h _ => h⟩

omit [Finite F] in
private theorem coordinateBlock_points_card (a : Ω) :
    Nat.card (Projectivization F (D.coordinateBlock C hC a)) = (Nat.card F)^2 + Nat.card F + 1 := by
  let e := Matrix.PSp4Three.projectiveSubmoduleEquiv (D.coordinateBlock C hC a)
  have hh (p : ProjectivePoint F) : p.rep ∈ D.coordinateBlock C hC a ↔ D.incident a (C.symm p) := by
    change (∀ hv, D.incident a (C.symm (Projectivization.mk F p.rep hv))) ↔ _
    simp only [mk_rep]
    exact ⟨fun h => h p.rep_nonzero,fun h _ => h⟩
  let e' : {p : ProjectivePoint F // p.rep ∈ D.coordinateBlock C hC a} ≃ D.block a :=
    { toFun := fun p => ⟨C.symm p,(hh p).mp p.property⟩
      invFun := fun p => ⟨C p,(hh (C p)).mpr (by simpa only [C.symm_apply_apply] using (D.mem_block.mp p.property))⟩
      left_inv := fun p => Subtype.ext (C.apply_symm_apply p)
      right_inv := fun p => Subtype.ext (C.symm_apply_apply p) }
  exact (Nat.card_congr (e.trans e')).trans (D.block_card a)

/-- Every polar block becomes an actual vector hyperplane, by its source cardinality. -/
theorem coordinateBlock_finrank (a : Ω) :
    finrank F (D.coordinateBlock C hC a) = 3 := by
  let W := D.coordinateBlock C hC a
  have hc := Projectivization.card' F W
  rw [D.coordinateBlock_points_card C hC a] at hc
  have hw : Nat.card W = Nat.card F ^ finrank F W := by
    let e := LinearEquiv.ofFinrankEq (R := F) W (Fin (finrank F W) → F) (by simp)
    rw [Nat.card_congr e.toEquiv,Nat.card_fun,Nat.card_fin]
  rw [hw] at hc
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hp : (Nat.card F)^finrank F W = (Nat.card F)^3 := by
    rw [hc]
    have hsub : Nat.card F - 1 + 1 = Nat.card F := by omega
    nlinarith
  exact (Nat.pow_right_injective hq) hp

/-- The native pole of a transported source block. -/
@[expose] def coordinatePole (a : Ω) : ProjectivePoint F :=
  mk'' ((form F).orthogonal (D.coordinateBlock C hC a)) (by
    rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,
      D.coordinateBlock_finrank C hC a]
    simp [Theory.SpecificGroups.SymplecticFour.Vector])

@[simp] theorem coordinatePole_submodule (a : Ω) :
    (D.coordinatePole C hC a).submodule = (form F).orthogonal (D.coordinateBlock C hC a) :=
  submodule_mk'' _ _

omit [Finite F] in
private theorem orthogonal_iff_le (p r : ProjectivePoint F) :
    Orthogonal p r ↔ r.submodule ≤ (form F).orthogonal p.submodule := by
  constructor
  · intro h v hv u hu
    exact h u hu v hv
  · intro h u hu v hv
    exact h hv u hu

/-- Incidence is the native pairing with the newly constructed pole. -/
theorem coordinatePole_incident (a x : Ω) :
    Orthogonal (D.coordinatePole C hC a) (C x) ↔ D.incident a x := by
  rw [orthogonal_iff_le,coordinatePole_submodule,
    LinearMap.BilinForm.orthogonal_orthogonal TwoLocalCover.form_nondegenerate
      TwoLocalCover.form_alternating.isRefl,le_coordinateBlock_iff]

/-- Distinct source blocks have distinct native poles. -/
theorem coordinatePole_injective : Function.Injective (D.coordinatePole C hC) := by
  intro a b he
  by_contra hab
  have hblock : D.block a = D.block b := by
    ext x
    rw [mem_block,mem_block,← D.coordinatePole_incident C hC a x,
      ← D.coordinatePole_incident C hC b x,he]
  have hc := D.intersection_card hab
  change (D.block a ∩ D.block b).ncard = Nat.card F + 1 at hc
  rw [← hblock,Set.inter_self,show (D.block a).ncard = _ from D.block_card a] at hc
  have hq := Finite.one_lt_card (α := F)
  nlinarith

/-- The null polarity becomes a permutation of native points; it is not assumed. -/
@[expose] def coordinatePolarity : Equiv.Perm (ProjectivePoint F) :=
  C.symm.trans (Equiv.ofBijective (D.coordinatePole C hC)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨D.coordinatePole_injective C hC,Nat.card_congr C⟩))

@[simp] theorem coordinatePolarity_apply (a : Ω) :
    D.coordinatePolarity C hC (C a) = D.coordinatePole C hC a := by
  change D.coordinatePole C hC (C.symm (C a)) = _
  rw [C.symm_apply_apply]

/-- The composition of the transported null polarity with the native polarity
is a projective collineation. -/
theorem coordinatePolarity_preserves_lines :
    Collineation.PreservesLines (D.coordinatePolarity C hC) := by
  intro p r s
  obtain ⟨a,rfl⟩ := C.surjective p
  obtain ⟨b,rfl⟩ := C.surjective r
  obtain ⟨c,rfl⟩ := C.surjective s
  rw [coordinatePolarity_apply,coordinatePolarity_apply,coordinatePolarity_apply,
    projective_le_sup_iff_double_orthogonal,hC]
  constructor
  · intro hh z hza hzb
    exact D.symm ((D.coordinatePole_incident C hC c z).mp
      (hh (C z) ((D.coordinatePole_incident C hC a z).mpr (D.symm hza))
        ((D.coordinatePole_incident C hC b z).mpr (D.symm hzb))))
  · intro hh p hpa hpb
    obtain ⟨z,rfl⟩ := C.surjective p
    rw [D.coordinatePole_incident C hC] at hpa hpb ⊢
    exact D.symm (hh z (D.symm hpa) (D.symm hpb))

/-- Every point is absolute for the transported polarity. -/
theorem coordinatePolarity_null (p : ProjectivePoint F) :
    Orthogonal (D.coordinatePolarity C hC p) p := by
  obtain ⟨a,rfl⟩ := C.surjective p
  rw [coordinatePolarity_apply,coordinatePole_incident]
  exact D.refl a

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
