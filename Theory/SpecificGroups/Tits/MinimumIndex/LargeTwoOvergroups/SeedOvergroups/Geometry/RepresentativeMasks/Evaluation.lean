module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks.PointCertificates
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks.Rotations

/-!
# Reusing certified point actions in the representative tests

Replace the forward actions of the conjugators, both normal-form halves,
and the two marked central generators by their checked tables. The inverse
conjugator table is checked as a right inverse; injectivity supplies the
other inverse law. Every resulting permutation is proved equal to the
original one, so the tests retain exactly Evaluation.placeTest's semantics.
Source: Parrott (1972), p.683, and Geometry/Evaluation.lean.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks

def withForward (g : Equiv.Perm (Fin 1600)) (f : Fin 1600 → Fin 1600)
    (h : ∀ p, f p = g p) : Equiv.Perm (Fin 1600) where
  toFun := f
  invFun := g.symm
  left_inv p := by rw [h]; exact g.left_inv p
  right_inv p := by rw [h]; exact g.right_inv p

private theorem withForward_eq (g : Equiv.Perm (Fin 1600))
    (f : Fin 1600 → Fin 1600) (h : ∀ p, f p = g p) : withForward g f h = g :=
  Equiv.ext h

/-- The literal conjugating permutation, with both point actions tabulated. -/
def conjugator (j : Fin 38) : Equiv.Perm (Fin 1600) where
  toFun := tableMap (conjData j.val)
  invFun := tableMap (invConjData j.val)
  left_inv p := by
    apply (fastConjugator j).injective
    rw [← conj_correct j, inv_correct, conj_correct]
  right_inv p := inv_correct j p

theorem conjugator_eq (j : Fin 38) : conjugator j = fastConjugator j :=
  Equiv.ext (conj_correct j)

def low (n : Fin 32) : Equiv.Perm (Fin 1600) :=
  withForward (fastNormalForm ⟨n.val, by omega⟩) (tableMap (lowData n.val))
    (low_correct n)

def high (n : Fin 64) : Equiv.Perm (Fin 1600) :=
  withForward (fastNormalForm ⟨32 * n.val, by omega⟩) (tableMap (highData n.val))
    (high_correct n)

private theorem low_eq (n : Fin 32) : low n = fastNormalForm ⟨n.val, by omega⟩ :=
  withForward_eq _ _ _

private theorem high_eq (n : Fin 64) : high n = fastNormalForm ⟨32 * n.val, by omega⟩ :=
  withForward_eq _ _ _

private theorem normal_split (n : Fin 2048) :
    fastNormalForm n =
      fastNormalForm ⟨n.val % 32, by omega⟩ *
      fastNormalForm ⟨32 * (n.val / 32), by omega⟩ := by
  simp only [fastNormalForm]
  have h₁ : n.val % 32 % 2 = n.val % 2 := by omega
  have h₂ : n.val % 32 / 2 % 2 = n.val / 2 % 2 := by omega
  have h₃ : n.val % 32 / 4 % 4 = n.val / 4 % 4 := by omega
  have h₄ : n.val % 32 / 16 % 2 = n.val / 16 % 2 := by omega
  have h₅ : n.val % 32 / 32 % 4 = 0 := by omega
  have h₆ : n.val % 32 / 128 % 2 = 0 := by omega
  have h₇ : n.val % 32 / 256 % 4 = 0 := by omega
  have h₈ : n.val % 32 / 1024 % 2 = 0 := by omega
  have k₁ : 32 * (n.val / 32) % 2 = 0 := by omega
  have k₂ : 32 * (n.val / 32) / 2 % 2 = 0 := by omega
  have k₃ : 32 * (n.val / 32) / 4 % 4 = 0 := by omega
  have k₄ : 32 * (n.val / 32) / 16 % 2 = 0 := by omega
  have k₅ : 32 * (n.val / 32) / 32 % 4 = n.val / 32 % 4 := by omega
  have k₆ : 32 * (n.val / 32) / 128 % 2 = n.val / 128 % 2 := by omega
  have k₇ : 32 * (n.val / 32) / 256 % 4 = n.val / 256 % 4 := by omega
  have k₈ : 32 * (n.val / 32) / 1024 % 2 = n.val / 1024 % 2 := by omega
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈,
    pow_zero, mul_one, one_mul, mul_assoc]

/-- Evaluate a Sylow normal form using its two ordered halves. -/
def normal (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  low ⟨n.val % 32, Nat.mod_lt _ (by decide)⟩ * high ⟨n.val / 32, by omega⟩

theorem normal_eq (n : Fin 2048) : normal n = fastNormalForm n := by
  rw [normal, low_eq, high_eq]
  exact (normal_split n).symm

def rotation (j : Fin 38) (e : Nat) : Equiv.Perm (Fin 1600) :=
  if j.val < 17 then
    if he : e < 5 then
      withForward ((fastAssignment .s1 * fastAssignment .r1) ^ e)
        (tableMap (firstRotationData ⟨e, he⟩)) (firstRotation_correct ⟨e, he⟩)
    else (fastAssignment .s1 * fastAssignment .r1) ^ e
  else
    if he : e < 3 then
      withForward ((fastAssignment .s8 * fastAssignment .r8) ^ e)
        (tableMap (secondRotationData ⟨e, he⟩)) (secondRotation_correct ⟨e, he⟩)
    else (fastAssignment .s8 * fastAssignment .r8) ^ e

private theorem rotation_eq (j : Fin 38) (e : Nat) :
    rotation j e = (if j.val < 17 then fastAssignment .s1 * fastAssignment .r1
      else fastAssignment .s8 * fastAssignment .r8) ^ e := by
  simp only [rotation, withForward_eq]
  split_ifs <;> rfl

/-- The literal representative, evaluated through certified point tables. -/
def representative (r : Row) : Equiv.Perm (Fin 1600) :=
  let j : Fin 38 := ⟨r.1 % 38, Nat.mod_lt _ (by decide)⟩
  let n : Fin 2048 := ⟨r.1 / 38 % 2048, Nat.mod_lt _ (by decide)⟩
  let w := conjugator j
  w * (normal n * rotation j (r.1 / (38 * 2048))) * w⁻¹

theorem representative_eq (r : Row) : representative r = rowPerm r := by
  simp only [representative, conjugator_eq, normal_eq, rotation_eq, rowPerm]

def central : Equiv.Perm (Fin 1600) :=
  withForward centralPerm (tableMap (centerData 0)) central_correct

def mate : Equiv.Perm (Fin 1600) :=
  withForward matePerm (tableMap (centerData 1)) mate_correct

private theorem central_eq : central = centralPerm := withForward_eq _ _ _
private theorem mate_eq : mate = matePerm := withForward_eq _ _ _

def centerImage (g z : Equiv.Perm (Fin 1600)) : Bool :=
  sameBase (g * z) g || sameBase (g * z) (central * g) ||
    sameBase (g * z) (mate * g) || sameBase (g * z) (central * mate * g)

/-- The original place test with the shared actions tabulated. -/
def test (g : Equiv.Perm (Fin 1600)) (j : Fin 38) : Bool :=
  let w := conjugator j
  let a := w⁻¹ * g * w
  if j.val < 17 then sameBase (a * central) (central * a)
  else centerImage a central && centerImage a mate

theorem test_eq (g : Equiv.Perm (Fin 1600)) (j : Fin 38) : test g j = placeTest g j := by
  simp only [test, conjugator_eq, central_eq, mate_eq, centerImage, centerImageTest,
    placeTest]

/-- Check all global support bits that the pattern actually uses. -/
def check (t : Fin 18) (r : Row) : Bool :=
  (placePattern t).all (fun j => test (representative r) j == rowMember r j)

/-- Transport the bounded computations to the original computational contract. -/
theorem of_checks (t : Fin 18) (h : (rows t).all (check t) = true) :
    ∀ r ∈ rows t, ∀ j ∈ placePattern t, placeTest (rowPerm r) j = rowMember r j := by
  intro r hr j hj
  have hrow := List.all_eq_true.mp h r hr
  have hbit := List.all_eq_true.mp hrow j hj
  simpa only [beq_iff_eq, test_eq, representative_eq] using hbit

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks
