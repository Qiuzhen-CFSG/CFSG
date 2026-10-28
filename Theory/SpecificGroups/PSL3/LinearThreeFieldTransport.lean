module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Coefficient transport of the degree-three local factors

A field isomorphism sends the vector-fixing and covector-fixing matrix
subgroups to the corresponding subgroups over the target field. Restricting
entrywise matrix transport and then using the actual projective restrictions
gives local-factor isomorphisms. The final equations identify them with the
ambient projective field transport, retaining the scalar quotient.

The binary application in Chapter F transports any field of order two to
ZMod 2 before applying the faithful four-point actions. Source:
Aschbacher–Smith F.1.12(I)(1), printed pp.262–264. The imported ambient
transport is the attributed ATLAS construction in
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section

open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable {F K : Type*} [Field F] [Field K]

theorem mem_pointLocalSL_field_iff (e : F ≃+* K) (g : SL(3,F)) :
    Atlas.fieldEquivSL 3 e g ∈ pointLocalSL K ↔ g ∈ pointLocalSL F := by
  rw [mem_pointLocalSL_iff, mem_pointLocalSL_iff]
  change (e (g.val 0 0) = 1 ∧ e (g.val 1 0) = 0 ∧ e (g.val 2 0) = 0) ↔ _
  simp

theorem mem_lineLocalSL_field_iff (e : F ≃+* K) (g : SL(3,F)) :
    Atlas.fieldEquivSL 3 e g ∈ lineLocalSL K ↔ g ∈ lineLocalSL F := by
  rw [mem_lineLocalSL_iff, mem_lineLocalSL_iff]
  change (e (g.val 2 0) = 0 ∧ e (g.val 2 1) = 0 ∧ e (g.val 2 2) = 1) ↔ _
  simp

def pointLocalSLFieldEquiv (e : F ≃+* K) : pointLocalSL F ≃* pointLocalSL K where
  toFun g := ⟨Atlas.fieldEquivSL 3 e g, (mem_pointLocalSL_field_iff e g).mpr g.property⟩
  invFun g := ⟨Atlas.fieldEquivSL 3 e.symm g,
    (mem_pointLocalSL_field_iff e.symm g).mpr g.property⟩
  left_inv g := Subtype.ext ((Atlas.fieldEquivSL 3 e).left_inv g)
  right_inv g := Subtype.ext ((Atlas.fieldEquivSL 3 e).right_inv g)
  map_mul' g h := Subtype.ext ((Atlas.fieldEquivSL 3 e).map_mul g h)

def lineLocalSLFieldEquiv (e : F ≃+* K) : lineLocalSL F ≃* lineLocalSL K where
  toFun g := ⟨Atlas.fieldEquivSL 3 e g, (mem_lineLocalSL_field_iff e g).mpr g.property⟩
  invFun g := ⟨Atlas.fieldEquivSL 3 e.symm g,
    (mem_lineLocalSL_field_iff e.symm g).mpr g.property⟩
  left_inv g := Subtype.ext ((Atlas.fieldEquivSL 3 e).left_inv g)
  right_inv g := Subtype.ext ((Atlas.fieldEquivSL 3 e).right_inv g)
  map_mul' g h := Subtype.ext ((Atlas.fieldEquivSL 3 e).map_mul g h)

noncomputable def pointLocalFieldEquiv (e : F ≃+* K) : pointLocal F ≃* pointLocal K :=
  (pointLocalProjectEquiv F).symm.trans
    ((pointLocalSLFieldEquiv e).trans (pointLocalProjectEquiv K))

noncomputable def lineLocalFieldEquiv (e : F ≃+* K) : lineLocal F ≃* lineLocal K :=
  (lineLocalProjectEquiv F).symm.trans
    ((lineLocalSLFieldEquiv e).trans (lineLocalProjectEquiv K))

theorem pointLocalFieldEquiv_project (e : F ≃+* K) (g : pointLocalSL F) :
    pointLocalFieldEquiv e (pointLocalProjectEquiv F g) =
      pointLocalProjectEquiv K (pointLocalSLFieldEquiv e g) := by
  exact congrArg ((pointLocalProjectEquiv K) ∘ (pointLocalSLFieldEquiv e))
    ((pointLocalProjectEquiv F).symm_apply_apply g)

theorem lineLocalFieldEquiv_project (e : F ≃+* K) (g : lineLocalSL F) :
    lineLocalFieldEquiv e (lineLocalProjectEquiv F g) =
      lineLocalProjectEquiv K (lineLocalSLFieldEquiv e g) := by
  exact congrArg ((lineLocalProjectEquiv K) ∘ (lineLocalSLFieldEquiv e))
    ((lineLocalProjectEquiv F).symm_apply_apply g)

theorem pointLocalFieldEquiv_coe (e : F ≃+* K) (g : pointLocal F) :
    (pointLocalFieldEquiv e g : PSL(3,K)) = Atlas.fieldEquivPSL 3 e g := by
  obtain ⟨x, rfl⟩ := (pointLocalProjectEquiv F).surjective g
  rw [pointLocalFieldEquiv_project]
  exact (Atlas.fieldEquivPSL_mk 3 e x).symm

theorem lineLocalFieldEquiv_coe (e : F ≃+* K) (g : lineLocal F) :
    (lineLocalFieldEquiv e g : PSL(3,K)) = Atlas.fieldEquivPSL 3 e g := by
  obtain ⟨x, rfl⟩ := (lineLocalProjectEquiv F).surjective g
  rw [lineLocalFieldEquiv_project]
  exact (Atlas.fieldEquivPSL_mk 3 e x).symm

end Matrix.PSL3.LinearThree
