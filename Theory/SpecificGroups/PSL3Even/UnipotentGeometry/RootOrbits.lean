module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The SL₂ orbit of highest-root subgroups

Each root plane is the additive group of the natural two-dimensional F-space.
Its one-dimensional F-subspaces are actual subgroups. Conjugating the natural
SL₂ action through the coordinate equivalence gives their orbit, of cardinality
|F|+1. The highest-root subgroup is the second coordinate line in both planes.
This proves the local orbit calculation used in Aschbacher--Smith 5.3.6(2),
printed p. 660 (PDF p. 677); ambient fusion is not asserted here.
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Even.UnipotentGeometry
open scoped LinearAlgebra.Projectivization
variable (F : Type*) [Field F]

section Natural
variable {H : Type*} [Group H] (e : Multiplicative (Fin 2 → F) ≃* H)

/-- A projective point denotes a subgroup, not a nonzero vector. -/
def lineSubgroup (p : ℙ F (Fin 2 → F)) : Subgroup H :=
  p.submodule.toAddSubgroup.toSubgroup.map e.toMonoidHom

theorem lineSubgroup_injective : Function.Injective (lineSubgroup F e) := by
  intro p q h
  apply Projectivization.submodule_injective
  apply Submodule.toAddSubgroup_injective
  apply AddSubgroup.toSubgroup.injective
  exact Subgroup.map_injective e.injective h

@[simp] theorem mem_lineSubgroup (p : ℙ F (Fin 2 → F)) (h : H) :
    h ∈ lineSubgroup F e p ↔ (e.symm h).toAdd ∈ p.submodule :=
  Subgroup.mem_map_equiv

/-- The natural matrix action, transported through the actual plane coordinates. -/
def naturalAut (g : Matrix.SpecialLinearGroup (Fin 2) F) : MulAut H :=
  e.symm.trans ((AddEquiv.toMultiplicative
    (DistribMulAction.toLinearEquiv F (Fin 2 → F) g).toAddEquiv).trans e)

@[simp] theorem naturalAut_apply (g : Matrix.SpecialLinearGroup (Fin 2) F) (h : H) :
    naturalAut F e g h = e (Multiplicative.ofAdd (g • (e.symm h).toAdd)) := rfl

def naturalAction : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut H where
  toFun := naturalAut F e
  map_one' := by ext h; simp
  map_mul' g k := by ext h; simp [mul_smul]

private theorem mem_smul_line (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (p : ℙ F (Fin 2 → F)) (v : Fin 2 → F) :
    v ∈ (g • p).submodule ↔ g⁻¹ • v ∈ p.submodule := by
  induction p using Projectivization.ind with | h w hw =>
    simp only [Projectivization.smul_mk, Projectivization.submodule_mk,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c,rfl⟩
      exact ⟨c, by rw [smul_comm, inv_smul_smul]⟩
    · rintro ⟨c,hc⟩
      refine ⟨c, ?_⟩
      rw [← smul_comm g c w, hc, smul_inv_smul]

/-- The subgroup action agrees with the projective action. -/
theorem lineSubgroup_smul (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (p : ℙ F (Fin 2 → F)) :
    lineSubgroup F e (g • p) = (lineSubgroup F e p).map (naturalAction F e g) := by
  ext h
  change h ∈ lineSubgroup F e (g • p) ↔
    h ∈ (lineSubgroup F e p).map (naturalAut F e g).toMonoidHom
  rw [mem_lineSubgroup, mem_smul_line, Subgroup.mem_map_equiv, mem_lineSubgroup]
  simp [naturalAut, DistribMulAction.toLinearEquiv]

/-- The orbit is a set of subgroups of the plane. -/
def lineOrbit (p : ℙ F (Fin 2 → F)) : Set (Subgroup H) :=
  Set.range (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (lineSubgroup F e p).map (naturalAction F e g))

theorem lineOrbit_eq_range (p : ℙ F (Fin 2 → F)) :
    lineOrbit F e p = Set.range (lineSubgroup F e) := by
  ext A
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g • p, lineSubgroup_smul F e g p⟩
  · rintro ⟨q,rfl⟩
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F) p q
    exact ⟨g,(lineSubgroup_smul F e g p).symm⟩

theorem card_lineOrbit [Finite F] (p : ℙ F (Fin 2 → F)) :
    Nat.card (lineOrbit F e p) = Nat.card F + 1 := by
  rw [lineOrbit_eq_range, ← Nat.card_congr (Equiv.ofInjective _ (lineSubgroup_injective F e))]
  exact Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)

/-- The same count holds after embedding the plane in an ambient group. -/
theorem card_mapped_lineOrbit [Finite F] {G : Type*} [Group G]
    (f : H →* G) (hf : Function.Injective f) (p : ℙ F (Fin 2 → F)) :
    Nat.card (Subgroup.map f '' lineOrbit F e p) = Nat.card F + 1 := by
  rw [← Nat.card_congr (Equiv.Set.image (Subgroup.map f) (lineOrbit F e p)
    (Subgroup.map_injective hf))]
  exact card_lineOrbit F e p

end Natural

/-- Coordinates `(a,c)` for the plane `b=0`. -/
def vectorPlane₁ : Multiplicative (Fin 2 → F) ≃* V₁ F :=
  (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow F F).toAddEquiv).trans (plane₁Equiv F)
/-- Coordinates `(b,c)` for the plane `a=0`. -/
def vectorPlane₂ : Multiplicative (Fin 2 → F) ≃* V₂ F :=
  (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow F F).toAddEquiv).trans (plane₂Equiv F)

@[simp] theorem vectorPlane₁_apply (v : Multiplicative (Fin 2 → F)) :
    (vectorPlane₁ F v : U F) = ⟨v.toAdd 0, 0, v.toAdd 1⟩ := rfl
@[simp] theorem vectorPlane₂_apply (v : Multiplicative (Fin 2 → F)) :
    (vectorPlane₂ F v : U F) = ⟨0, v.toAdd 0, v.toAdd 1⟩ := rfl

/-- The highest-root line in natural plane coordinates. -/
def highestPoint : ℙ F (Fin 2 → F) :=
  Projectivization.mk F ![0,1] (by intro h; have := congrFun h 1; simp at this)

@[simp] theorem mem_highestPoint (v : Fin 2 → F) :
    v ∈ (highestPoint F).submodule ↔ v 0 = 0 := by
  rw [highestPoint, Projectivization.submodule_mk, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,rfl⟩; simp
  · intro h
    refine ⟨v 1, ?_⟩
    ext i
    fin_cases i <;> simp [h]

theorem highestPoint_plane₁ :
    (lineSubgroup F (vectorPlane₁ F) (highestPoint F)).map (V₁ F).subtype = Z F := by
  ext a
  constructor
  · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
    have hw : w.toAdd 0 = 0 := (mem_highestPoint F w.toAdd).mp hw
    simp [hw]
  · intro ha
    obtain ⟨hx,hy⟩ := (mem_Z F a).mp ha
    refine ⟨vectorPlane₁ F (Multiplicative.ofAdd ![0,a.c]), ?_, ?_⟩
    · apply Subgroup.mem_map.mpr
      exact ⟨_, (mem_highestPoint F _).mpr rfl, rfl⟩
    · exact U.ext hx.symm hy.symm rfl

theorem highestPoint_plane₂ :
    (lineSubgroup F (vectorPlane₂ F) (highestPoint F)).map (V₂ F).subtype = Z F := by
  ext a
  constructor
  · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
    have hw : w.toAdd 0 = 0 := (mem_highestPoint F w.toAdd).mp hw
    simp [hw]
  · intro ha
    obtain ⟨hx,hy⟩ := (mem_Z F a).mp ha
    refine ⟨vectorPlane₂ F (Multiplicative.ofAdd ![0,a.c]), ?_, ?_⟩
    · apply Subgroup.mem_map.mpr
      exact ⟨_, (mem_highestPoint F _).mpr rfl, rfl⟩
    · exact U.ext hx.symm hy.symm rfl

/-- The SL₂ orbit of Z in the first plane has q+1 distinct subgroups. -/
theorem card_highestRoot_orbit₁ [Finite F] :
    Nat.card (lineOrbit F (vectorPlane₁ F) (highestPoint F)) = Nat.card F + 1 :=
  card_lineOrbit F _ _
/-- The SL₂ orbit of Z in the second plane has q+1 distinct subgroups. -/
theorem card_highestRoot_orbit₂ [Finite F] :
    Nat.card (lineOrbit F (vectorPlane₂ F) (highestPoint F)) = Nat.card F + 1 :=
  card_lineOrbit F _ _

/-- Here the orbit members are subgroups of U itself. -/
theorem card_highestRoot_ambient_orbit₁ [Finite F] :
    Nat.card (Subgroup.map (V₁ F).subtype ''
      lineOrbit F (vectorPlane₁ F) (highestPoint F)) = Nat.card F + 1 :=
  card_mapped_lineOrbit F _ _ (V₁ F).subtype_injective _

theorem card_highestRoot_ambient_orbit₂ [Finite F] :
    Nat.card (Subgroup.map (V₂ F).subtype ''
      lineOrbit F (vectorPlane₂ F) (highestPoint F)) = Nat.card F + 1 :=
  card_mapped_lineOrbit F _ _ (V₂ F).subtype_injective _

end Matrix.PSL3Even.UnipotentGeometry
