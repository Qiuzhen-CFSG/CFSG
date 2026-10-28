module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.Coordinates
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.FiniteCriterion
public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel


/-!
# Realizing the six binary word groups as UT₃(F₄)

We send the ordered word a^i b^j c^k d^l z^m u^n to its product in the
literal upper unitriangular group over `GaloisField 2 2`. The common images
are a=(1,1,0), b=(ω,ω+1,0), z=(0,0,1), and u=(0,0,ω). With
C=(ω+1,ω+1,0), D=(1,ω,0), and E=(ω,1,0), the six respective pairs (c,d)
are (C,D), (C,E), (D,C), (E,C), (D,E), and (E,D).

Two binary coordinates represent r+sω. The identity ω²=ω+1 proves that
this representation respects field multiplication, and ω∉{0,1} proves
injectivity. Each word image has two linear root coordinates and the
quadratic central correction obtained by multiplying the ordered generators.
Polynomial identities verify the six collection cocycles. A small kernel
calculation verifies injectivity of their four-bit linear coordinates;
central-coordinate injectivity then gives an injective homomorphism, hence
an isomorphism between the two groups of order 64.

The consumer applies this realization to explicit marked coordinates and
balanced nonidentity central square fibers. Existence of marked coordinates
remains with the independent intrinsic normal-form construction and the
source recognition assembly; it is not assumed to follow from a group label.
Source motivation: Aschbacher, *Sporadic Groups* (1994), proof of 46.14,
printed pp.257–258. This module supplies the multiplication recognition,
not the other normalizer, fusion, and subgroup clauses of that source lemma.
-/

public section

open Matrix.PSL3Four Matrix.PSL3Four.SylowModel
namespace Theory.GroupTheory.AnisotropicRecognition
noncomputable section

private def bitCast : Bit →+* F := ZMod.castHom (dvd_refl 2) F

private def fieldValue (p : Central) : F := bitCast p.1 + omega * bitCast p.2

private def fieldMul (p q : Central) : Central :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)

private theorem fieldValue_add (p q : Central) :
    fieldValue (p+q) = fieldValue p + fieldValue q := by
  simp only [fieldValue, Prod.fst_add, Prod.snd_add, map_add]
  ring

private theorem fieldValue_mul (p q : Central) :
    fieldValue (fieldMul p q) = fieldValue p * fieldValue q := by
  have hw : omega ^ 2 = omega + 1 := by
    rw [← fieldFrobenius_apply, omega_frobenius]
  dsimp [fieldValue, fieldMul]
  simp only [map_add, map_mul]
  calc
    _ = bitCast p.1 * bitCast q.1 + omega * (bitCast p.1 * bitCast q.2 +
      bitCast p.2 * bitCast q.1) + (omega + 1) * (bitCast p.2 * bitCast q.2) := by ring
    _ = _ := by rw [← hw]; ring

private theorem fieldValue_injective : Function.Injective fieldValue := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have bit_cases : ∀ x : Bit, x = 0 ∨ x = 1 := by decide +kernel
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;>
    rcases bit_cases d with rfl | rfl <;>
    simp_all [fieldValue, omega_ne_zero, omega_ne_one,
      Ne.symm omega_ne_zero, Ne.symm omega_ne_one, CharTwo.add_eq_zero]
  exact omega_ne_one (CharTwo.add_eq_zero.mp h.symm).symm

private def scale (t : Bit) (p : Central) : Central := (t * p.1, t * p.2)

private def rootX (c d : Central × Central) (v : Vector) : Central :=
  scale v.1.1 cz + scale v.1.2 cu + scale v.2.1 c.1 + scale v.2.2 d.1

private def rootY (c d : Central × Central) (v : Vector) : Central :=
  scale v.1.1 cz + scale v.1.2 czu + scale v.2.1 c.2 + scale v.2.2 d.2

private def correction (c d : Central × Central) (v : Vector) : Central :=
  scale (v.1.1 * v.1.2) (fieldMul cz czu) +
  scale (v.1.1 * v.2.1) (fieldMul cz c.2) +
  scale (v.1.1 * v.2.2) (fieldMul cz d.2) +
  scale (v.1.2 * v.2.1) (fieldMul cu c.2) +
  scale (v.1.2 * v.2.2) (fieldMul cu d.2) +
  scale (v.2.1 * v.2.2) (fieldMul c.1 d.2)

private def rootC : Central × Central := (czu, czu)
private def rootD : Central × Central := (cz, cu)
private def rootE : Central × Central := (cu, cz)

private theorem rootX_add (c d : Central × Central) (v w : Vector) :
    rootX c d (v + w) = rootX c d v + rootX c d w := by
  ext <;> dsimp [rootX,scale] <;> ring

private theorem rootY_add (c d : Central × Central) (v w : Vector) :
    rootY c d (v + w) = rootY c d v + rootY c d w := by
  ext <;> dsimp [rootY,scale] <;> ring

private def modelMatrix : Fin 6 → Cross
  | 0 => ⟨0, czu, czu, 0⟩
  | 1 => ⟨0, czu, czu, czu⟩
  | 2 => ⟨czu, 0, 0, czu⟩
  | 3 => ⟨czu, 0, czu, czu⟩
  | 4 => ⟨czu, czu, 0, czu⟩
  | 5 => ⟨czu, czu, czu, 0⟩

private def modelParameters : Fin 6 → (Central × Central) × (Central × Central)
  | 0 => (rootC, rootD)
  | 1 => (rootC, rootE)
  | 2 => (rootD, rootC)
  | 3 => (rootE, rootC)
  | 4 => (rootD, rootE)
  | 5 => (rootE, rootD)

private theorem model_collection (i : Fin 6) (v w : Vector) :
    cocycle (modelMatrix i) v w +
      correction (modelParameters i).1 (modelParameters i).2 (v + w) =
    correction (modelParameters i).1 (modelParameters i).2 v +
      correction (modelParameters i).1 (modelParameters i).2 w +
      fieldMul (rootX (modelParameters i).1 (modelParameters i).2 v)
        (rootY (modelParameters i).1 (modelParameters i).2 w) := by
  fin_cases i <;> ext <;>
    dsimp [modelMatrix, modelParameters, cocycle, correction, rootX, rootY,
      rootC, rootD, rootE, scale, fieldMul, cz, cu, czu] <;>
    ring_nf <;>
    simp [show (2 : Bit) = 0 by decide, show (3 : Bit) = 1 by decide]

private theorem model_vector_injective : ∀ (i : Fin 6) (v w : Vector),
    rootX (modelParameters i).1 (modelParameters i).2 v =
      rootX (modelParameters i).1 (modelParameters i).2 w →
    rootY (modelParameters i).1 (modelParameters i).2 v =
      rootY (modelParameters i).1 (modelParameters i).2 w → v = w := by
  decide +kernel

private def modelMap (i : Fin 6) (p : Word (modelMatrix i)) :
    RootNormalizerModel.Root :=
  ⟨fieldValue (rootX (modelParameters i).1 (modelParameters i).2 p.vector),
    fieldValue (rootY (modelParameters i).1 (modelParameters i).2 p.vector),
    fieldValue (p.central +
      correction (modelParameters i).1 (modelParameters i).2 p.vector)⟩

private def modelHom (i : Fin 6) : Word (modelMatrix i) →* RootNormalizerModel.Root where
  toFun := modelMap i
  map_one' := by
    apply U.ext <;>
      simp [modelMap, rootX, rootY, correction, scale, fieldValue]
  map_mul' p q := by
    apply U.ext
    · change fieldValue (rootX _ _ (p.vector + q.vector)) = _
      rw [rootX_add, fieldValue_add]
      rfl
    · change fieldValue (rootY _ _ (p.vector + q.vector)) = _
      rw [rootY_add, fieldValue_add]
      rfl
    · change fieldValue ((p.central + q.central + cocycle (modelMatrix i) p.vector q.vector) +
        correction (modelParameters i).1 (modelParameters i).2 (p.vector + q.vector)) = _
      rw [add_assoc (p.central + q.central), model_collection]
      simp only [fieldValue_add, fieldValue_mul, mul_c, modelMap]
      abel

private theorem modelHom_injective (i : Fin 6) : Function.Injective (modelHom i) := by
  intro p q h
  have hx := fieldValue_injective (congrArg U.x h)
  have hy := fieldValue_injective (congrArg U.y h)
  have hv := model_vector_injective i p.vector q.vector hx hy
  apply Word.ext hv
  have hc := fieldValue_injective (congrArg U.c h)
  change p.central + correction _ _ p.vector = q.central + correction _ _ q.vector at hc
  rw [hv] at hc
  exact add_right_cancel hc

private def modelEquiv (i : Fin 6) : Word (modelMatrix i) ≃* RootNormalizerModel.Root :=
  MulEquiv.ofBijective (modelHom i)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨modelHom_injective i, (card_Word _).trans card_U.symm⟩)

/-- Each of the six balanced multiplication laws is the literal UT₃(F₄) group. -/
theorem rootEquiv_of_sixCases (M : Cross) (hM : SixCases M) :
    Nonempty (Word M ≃* RootNormalizerModel.Root) := by
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨modelEquiv 0⟩
  · exact ⟨modelEquiv 1⟩
  · exact ⟨modelEquiv 2⟩
  · exact ⟨modelEquiv 3⟩
  · exact ⟨modelEquiv 4⟩
  · exact ⟨modelEquiv 5⟩

/-- Marked normal forms and balanced nonidentity central square fibers identify
an anisotropic factor group with UT₃(F₄). The existence of the marked normal
forms is an independent premise, discharged by the intrinsic recognition owner. -/
theorem rootEquiv_of_coordinates {K : Type*} [Group K]
    (F : AnisotropicFactors K) (C : MarkedCoordinates F)
    (h : ∀ c d : Subgroup.center K, c ≠ 1 → d ≠ 1 →
      Nat.card {x : K // x ^ 2 = (c : K)} = Nat.card {x : K // x ^ 2 = (d : K)}) :
    Nonempty (K ≃* RootNormalizerModel.Root) := by
  obtain ⟨e⟩ := rootEquiv_of_sixCases C.matrix
    (sixCases_of_balanced C.matrix (firstNondegenerate_of_coordinates F C)
      (balanced_of_coordinates F C h))
  exact ⟨C.equiv.trans e⟩

end
end Theory.GroupTheory.AnisotropicRecognition
