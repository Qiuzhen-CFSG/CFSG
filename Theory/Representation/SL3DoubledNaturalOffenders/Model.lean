module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The marked doubled natural SL₃ module

The same special linear matrix acts on both copies of the natural module.
The commuting multiplicity algebra acts on the two copy indices. Their product
is the literal tensor action of SL₃ × SL₂, inside the binary general linear group.
No normalizer coverage or offender estimate is assumed in these definitions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

@[expose] public section

namespace Representation.SL3DoubledNaturalOffenders
open Matrix
variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

abbrev Natural := Fin 3 → F
abbrev Space := Fin 2 → Natural F
abbrev SL := SpecialLinearGroup (Fin 3) F
abbrev MultiplicitySL := SpecialLinearGroup (Fin 2) F
abbrev Ambient := (Module.End (ZMod 2) (Space F))ˣ

/-- The identical natural marking on the two copies. -/
def representation : Representation (ZMod 2) (SL F) (Space F) where
  toFun g :=
    { toFun := fun v i => g.val.mulVec (v i)
      map_add' v w := by funext i; exact Matrix.mulVec_add g.val (v i) (w i)
      map_smul' a v := by funext i; exact Matrix.mulVec_smul g.val a (v i) }
  map_one' := by apply LinearMap.ext; intro v; funext i; exact Matrix.one_mulVec (v i)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    exact (Matrix.mulVec_mulVec (v i) g.val h.val).symm

@[simp] theorem representation_apply (g : SL F) (v : Space F) (i : Fin 2) :
    representation F g v i = g.val.mulVec (v i) := rfl

/-- The actual SL₃ image in binary invertible operators. -/
def component : Subgroup (Ambient F) := (representation F).asGroupHom.range

/-- The full binary normalizer of the marked component. -/
def normalizer : Subgroup (Ambient F) := Subgroup.normalizer (component F)

/-- Evaluation by binary invertible operators. -/
def action : Representation (ZMod 2) (Ambient F) (Space F) := Units.coeHom _

@[simp] theorem action_component (g : SL F) :
    action F ((representation F).asGroupHom g) = representation F g := rfl

theorem action_injective : Function.Injective (action F) := fun _ _ h => Units.ext h

theorem representation_injective : Function.Injective (representation F) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact congrArg (fun f : Module.End (ZMod 2) (Space F) => f (fun _ => v) 0) he

/-- Two by two field matrices acting on the multiplicity indices. -/
def multiplicity (c : Matrix (Fin 2) (Fin 2) F) : Module.End (ZMod 2) (Space F) where
  toFun v i := c i 0 • v 0 + c i 1 • v 1
  map_add' v w := by ext i j; simp; ring
  map_smul' a v := by
    ext i j
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [smul_comm (c i 0) a, smul_comm (c i 1) a, smul_add]
    rfl

@[simp] theorem multiplicity_apply (c : Matrix (Fin 2) (Fin 2) F)
    (v : Space F) (i : Fin 2) :
    multiplicity F c v i = c i 0 • v 0 + c i 1 • v 1 := rfl

@[simp] theorem multiplicity_one : multiplicity F 1 = 1 := by
  apply LinearMap.ext
  intro v
  funext i j
  fin_cases i <;> simp [multiplicity, Matrix.one_apply]

@[simp] theorem multiplicity_mul (c d : Matrix (Fin 2) (Fin 2) F) :
    multiplicity F (c * d) = multiplicity F c * multiplicity F d := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [multiplicity, Module.End.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[simp] theorem multiplicity_zero : multiplicity F 0 = 0 := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [multiplicity]

@[simp] theorem multiplicity_add (c d : Matrix (Fin 2) (Fin 2) F) :
    multiplicity F (c + d) = multiplicity F c + multiplicity F d := by
  apply LinearMap.ext
  intro v
  funext i j
  simp [multiplicity, add_mul]
  ring

/-- The concrete matrix algebra in the binary commutant. -/
def multiplicityHom : Matrix (Fin 2) (Fin 2) F →+* Module.End (ZMod 2) (Space F) where
  toFun := multiplicity F
  map_one' := multiplicity_one F
  map_mul' := multiplicity_mul F
  map_zero' := multiplicity_zero F
  map_add' := multiplicity_add F

theorem multiplicity_injective : Function.Injective (multiplicity F) := by
  intro c d h
  ext i j
  have he := congrArg (fun f : Module.End (ZMod 2) (Space F) =>
    f (Pi.single j (Pi.single 0 1)) i 0) h
  fin_cases j <;> simpa [multiplicity] using he

/-- Multiplicity matrices commute with the identical natural action. -/
theorem multiplicity_commutes (c : Matrix (Fin 2) (Fin 2) F) (g : SL F) :
    multiplicity F c * representation F g = representation F g * multiplicity F c := by
  apply LinearMap.ext
  intro v
  funext i j
  change (c i 0 • g.val.mulVec (v 0) + c i 1 • g.val.mulVec (v 1)) j =
    g.val.mulVec (c i 0 • v 0 + c i 1 • v 1) j
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- Special linear changes of multiplicity coordinates. -/
def multiplicityRepresentation : Representation (ZMod 2) (MultiplicitySL F) (Space F) :=
  (multiplicityHom F).toMonoidHom.comp SpecialLinearGroup.coeMonoidHom

/-- The concrete tensor product action; both factors retain their markings. -/
def tensorRepresentation : Representation (ZMod 2) (SL F × MultiplicitySL F) (Space F) where
  toFun p := representation F p.1 * multiplicityRepresentation F p.2
  map_one' := by simp
  map_mul' p q := by
    change representation F (p.1 * q.1) * multiplicityRepresentation F (p.2 * q.2) = _
    rw [map_mul, map_mul]
    have hc := multiplicity_commutes F p.2.val q.1
    change multiplicityRepresentation F p.2 * representation F q.1 =
      representation F q.1 * multiplicityRepresentation F p.2 at hc
    simp only [mul_assoc]
    rw [← mul_assoc (multiplicityRepresentation F p.2), hc, mul_assoc]

/-- The actual tensor subgroup, not a predicate asserting normalizer coverage. -/
def tensorSubgroup : Subgroup (Ambient F) := (tensorRepresentation F).asGroupHom.range

/-- The tensor subgroup contains the marked component with exactly the original action. -/
theorem component_le_tensorSubgroup : component F ≤ tensorSubgroup F := by
  rintro b ⟨g, rfl⟩
  refine ⟨(g, 1), ?_⟩
  apply Units.ext
  change representation F g * multiplicityRepresentation F 1 = representation F g
  rw [map_one, mul_one]

/-- The multiplicity special linear group lies in the actual component centralizer. -/
theorem multiplicity_mem_centralizer (c : MultiplicitySL F) :
    (multiplicityRepresentation F).asGroupHom c ∈
      Subgroup.centralizer (component F : Set (Ambient F)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro b ⟨g, rfl⟩
  apply Units.ext
  exact (multiplicity_commutes F c.val g).symm

/-- Every tensor actor really normalizes the marked doubled component. -/
theorem tensorSubgroup_le_normalizer : tensorSubgroup F ≤ normalizer F := by
  rintro b ⟨⟨g, c⟩, rfl⟩
  have he : (tensorRepresentation F).asGroupHom (g, c) =
      (representation F).asGroupHom g * (multiplicityRepresentation F).asGroupHom c := by
    apply Units.ext
    rfl
  rw [he]
  apply (normalizer F).mul_mem
  · exact (component F).le_normalizer ⟨g, rfl⟩
  · exact Subgroup.centralizer_le_normalizer _ (multiplicity_mem_centralizer F c)

end Representation.SL3DoubledNaturalOffenders
