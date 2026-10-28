module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.ElementaryEight.CayleyFrame

/-!
# Cayley triples and the two reference frames

A normalized Cayley triple consists of imaginary vectors `a,b,c`, with `a,b`
of norm one and `c` of nonzero norm `r`. They are pairwise orthogonal, and
`c` is orthogonal to `ab`. The associated eight products have fixed
parentheses. These geometric conditions are the input to the Cayley-table
construction; their definition does not assert a table or an automorphism.

Both reference frames are in the actual split octonions. `false` selects the
old torus/Weyl eight, whose third generator has norm minus one; `true` selects
the all-norm-one eight. The old frame receives an explicit inverse coordinate
map, and both reference multiplication tables and diagonal actions are checked
by kernel reduction. The two existing embedded subgroups are preserved.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482. The recognition configuration
on printed p.417 is not a conjugacy theorem. Coordinates follow the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
open Atlas.SplitOctonion
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Purely geometric hypotheses for a normalized Cayley triple. -/
structure IsCayleyTriple (r : ZMod 3) (a b c : V) : Prop where
  trace_a : trace a = 0
  trace_b : trace b = 0
  trace_c : trace c = 0
  norm_a : norm a = 1
  norm_b : norm b = 1
  norm_c : norm c = r
  norm_c_ne : r ≠ 0
  polar_ab : normPolar a b = 0
  polar_ac : normPolar a c = 0
  polar_bc : normPolar b c = 0
  polar_abc : normPolar (mul a b) c = 0

/-- The parenthesized products used throughout the conjugacy construction. -/
@[expose] def frame (a b c : V) : Fin 8 → V :=
  ![unit, a, b, mul a b, c, mul a c, mul b c, mul (mul a b) c]

/-- Nontrivial homogeneous vectors are imaginary. -/
theorem trace_eq_zero_of_character_ne_one {E : Subgroup G} {χ : Character E}
    (hχ : χ ≠ 1) {x : V} (hx : x ∈ characterSpace E χ) : trace x = 0 := by
  have ht : normPolar x unit = trace x := by simp [normPolar, unit, trace]
  exact ht.symm.trans (orthogonal hχ hx (unit_mem E))

/-- Homogeneity of the generators gives homogeneity of every parenthesized product. -/
theorem frame_homogeneous {E : Subgroup G} {χ ψ ξ : Character E} {a b c : V}
    (ha : a ∈ characterSpace E χ) (hb : b ∈ characterSpace E ψ)
    (hc : c ∈ characterSpace E ξ) :
    ∀ i, ∃ η : Character E, frame a b c i ∈ characterSpace E η := by
  intro i
  fin_cases i
  · exact ⟨1, unit_mem E⟩
  · exact ⟨χ, ha⟩
  · exact ⟨ψ, hb⟩
  · exact ⟨χ * ψ, mul_mem ha hb⟩
  · exact ⟨ξ, hc⟩
  · exact ⟨χ * ξ, mul_mem ha hc⟩
  · exact ⟨ψ * ξ, mul_mem hb hc⟩
  · exact ⟨(χ * ψ) * ξ, mul_mem (mul_mem ha hb) hc⟩

/-- Changing the last norm changes precisely the products with two last-half factors. -/
@[expose] def coefficient (r : ZMod 3) (i j : Fin 8) : ZMod 3 :=
  CayleyEight.twist i j * (if 4 ≤ i.val ∧ 4 ≤ j.val then r else 1)

/-- Norm of the third reference generator: old frame first, norm-one frame second. -/
@[expose] def referenceNorm (k : Bool) : ZMod 3 := if k then 1 else -1

@[expose] def referenceThird (k : Bool) : V :=
  if k then CayleyEight.c else ![0,0,0,1,-1,0,0,0]

@[expose] def referenceFrame (k : Bool) : Fin 8 → V :=
  frame CayleyEight.a CayleyEight.b (referenceThird k)

theorem reference_triple (k : Bool) :
    IsCayleyTriple (referenceNorm k) CayleyEight.a CayleyEight.b (referenceThird k) := by
  cases k <;> constructor <;> decide +kernel

private def oldExpansion : V →ₗ[ZMod 3] V where
  toFun x := ![x 1-x 5, x 2+x 6, -x 3-x 7, x 0+x 4,
    x 0-x 4, -x 3+x 7, x 2-x 6, x 1+x 5]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

private def oldCoordinates : V →ₗ[ZMod 3] V where
  toFun x := ![-x 3-x 4, -x 0-x 7, -x 1-x 6, x 2+x 5,
    -x 3+x 4, x 0-x 7, -x 1+x 6, x 2-x 5]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

private def oldFrameEquiv : V ≃ₗ[ZMod 3] V where
  toLinearMap := oldExpansion
  invFun := oldCoordinates
  left_inv x := by
    have h : oldCoordinates.comp oldExpansion = LinearMap.id := by
      apply linearMap_ext
      exact (by decide +kernel : ∀ i, oldCoordinates (oldExpansion (basisVector i)) = basisVector i)
    exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) h
  right_inv x := by
    have h : oldExpansion.comp oldCoordinates = LinearMap.id := by
      apply linearMap_ext
      exact (by decide +kernel : ∀ i, oldExpansion (oldCoordinates (basisVector i)) = basisVector i)
    exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) h

/-- Bases of the two actual reference frames. -/
noncomputable def referenceBasis (k : Bool) : Module.Basis (Fin 8) (ZMod 3) V :=
  if k then CayleyEight.frameBasis else (Pi.basisFun (ZMod 3) (Fin 8)).map oldFrameEquiv

@[simp] theorem referenceBasis_apply (k : Bool) (i : Fin 8) :
    referenceBasis k i = referenceFrame k i := by
  cases k
  · change oldFrameEquiv ((Pi.basisFun (ZMod 3) (Fin 8)) i) = referenceFrame false i
    simpa only [Pi.basisFun_apply, basisVector] using
      (by decide +kernel : ∀ i, oldFrameEquiv (basisVector i) = referenceFrame false i) i
  · exact CayleyEight.frameBasis_apply i

/-- Both multiplication tables, including the old frame's minus-one third norm. -/
theorem reference_mul (k : Bool) (i j : Fin 8) :
    mul (referenceFrame k i) (referenceFrame k j) =
      coefficient (referenceNorm k) i j • referenceFrame k (CayleyEight.gradeSum i j) :=
  (by decide +kernel : ∀ k i j, mul (referenceFrame k i) (referenceFrame k j) =
    coefficient (referenceNorm k) i j • referenceFrame k (CayleyEight.gradeSum i j)) k i j

/-- The original parameter embeddings, with no replacement of either image. -/
@[expose] def referenceEmbedding (k : Bool) : Parameters →* G :=
  if k then CayleyEight.embedding else TernaryLocals.embedding

@[expose] def representative (k : Bool) : Subgroup G :=
  if k then CayleyEight.elementary else TernaryLocals.elementary

theorem representative_eq_range (k : Bool) : representative k = (referenceEmbedding k).range := by
  cases k <;> rfl

theorem card_representative (k : Bool) : Nat.card (representative k) = 8 := by
  cases k
  · exact TernaryLocals.card_elementary
  · exact CayleyEight.card_elementary

theorem centralizer_representative (k : Bool) :
    Subgroup.centralizer (representative k : Set G) = representative k := by
  cases k
  · exact ElementaryEight.centralizer_elementary
  · exact CayleyEight.centralizer_elementary

/-- Both parameter embeddings act by the same sign formula on their own frames. -/
theorem referenceEmbedding_frame (k : Bool) (p : Parameters) (i : Fin 8) :
    (referenceEmbedding k p).val (referenceFrame k i) = CayleyEight.sign p i • referenceFrame k i := by
  cases k
  · exact (by decide +kernel : ∀ p i,
      (referenceEmbedding false p).val (referenceFrame false i) =
        CayleyEight.sign p i • referenceFrame false i) p i
  · exact CayleyEight.embedding_frame p i

end Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy
