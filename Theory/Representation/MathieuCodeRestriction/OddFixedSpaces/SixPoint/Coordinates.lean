module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.CoreGeometry

/-!
# Native fixed-point coordinates for the Mathieu cocode

The normalizer acts on the literal common fixed-point subset and on the
actual cocode fixed space. Extension by zero sends its even core into the
24-point core, and then into the cocode fixed space. On a pair this map is
exactly the published two-subset class, including pairs through point zero.
No bijectivity or normalizer quotient is assumed or asserted here.

These are the coordinate maps used in Aschbacher–Smith H.15.7, printed
pp.401–402 (1 March 2004 manuscript). Their construction works for every
subgroup; six fixed points give a source core of dimension five.
-/

@[expose] public section

open Sporadic.Mathieu
open Representation.BinaryOffender
open scoped BigOperators
namespace MathieuCode.SixPoint
noncomputable section
open scoped Classical

/-- Native points fixed by every element of the supplied subgroup. -/
abbrev FixedPoint (D : Subgroup M24) := MulAction.fixedPoints D (Fin 24)

instance (D : Subgroup M24) : Fintype (FixedPoint D) := Fintype.ofFinite _

theorem normalizer_preserves_fixedPoints (D : Subgroup M24) (n : (Subgroup.normalizer (D : Set M24)))
    (i : FixedPoint D) : n.val • i.val ∈ MulAction.fixedPoints D (Fin 24) := by
  intro d
  have hc : n.val⁻¹ * d.val * n.val ∈ D := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (D : Set M24)).inv_mem n.property) d.val).mp d.property
  calc
    d.val • (n.val • i.val) = n.val • ((n.val⁻¹ * d.val * n.val) • i.val) := by
      simp [mul_smul]
    _ = n.val • i.val := congrArg (n.val • ·) (i.property ⟨_, hc⟩)

/-- Restriction of the genuine native permutation to the subgroup's fixed points. -/
def normalizerPerm (D : Subgroup M24) : (Subgroup.normalizer (D : Set M24)) →* Equiv.Perm (FixedPoint D) where
  toFun n :=
    { toFun := fun i => ⟨n.val • i.val, normalizer_preserves_fixedPoints D n i⟩
      invFun := fun i => ⟨n.val⁻¹ • i.val, normalizer_preserves_fixedPoints D n⁻¹ i⟩
      left_inv := fun i => Subtype.ext (inv_smul_smul n.val i.val)
      right_inv := fun i => Subtype.ext (smul_inv_smul n.val i.val) }
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

def fixedPointCoreRepresentation (D : Subgroup M24) :
    Representation (ZMod 2) (Subgroup.normalizer (D : Set M24)) (BinaryPermutation.core (FixedPoint D)) :=
  (BinaryPermutation.coreRepresentation (FixedPoint D)).comp (normalizerPerm D)

theorem normalizer_preserves_fixedCocode (D : Subgroup M24) (n : (Subgroup.normalizer (D : Set M24)))
    (v : fixedSpace cocodeRepresentation D) :
    cocodeRepresentation n.val v.val ∈ fixedSpace cocodeRepresentation D := by
  intro d
  have hc : n.val⁻¹ * d.val * n.val ∈ D := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (D : Set M24)).inv_mem n.property) d.val).mp d.property
  have he := v.property ⟨_, hc⟩
  change cocodeRepresentation (n.val⁻¹ * d.val * n.val) v.val = v.val at he
  change cocodeRepresentation d.val (cocodeRepresentation n.val v.val) = _
  calc
    _ = cocodeRepresentation (d.val * n.val) v.val := by rw [map_mul, Module.End.mul_apply]
    _ = cocodeRepresentation n.val (cocodeRepresentation (n.val⁻¹ * d.val * n.val) v.val) := by
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    _ = _ := congrArg (cocodeRepresentation n.val) he

def normalizerFixedSubrepresentation (D : Subgroup M24) :
    Subrepresentation (cocodeRepresentation.comp (Subgroup.normalizer (D : Set M24)).subtype) where
  toSubmodule := fixedSpace cocodeRepresentation D
  apply_mem_toSubmodule n v hv := normalizer_preserves_fixedCocode D n ⟨v, hv⟩

def fixedCocodeRepresentation (D : Subgroup M24) :
    Representation (ZMod 2) (Subgroup.normalizer (D : Set M24)) (fixedSpace cocodeRepresentation D) :=
  (normalizerFixedSubrepresentation D).toRepresentation

/-- Extension by zero from the literal fixed-point subset. -/
def extendWord (D : Subgroup M24) : (FixedPoint D → ZMod 2) →ₗ[ZMod 2] Full where
  toFun v i := if h : i ∈ MulAction.fixedPoints D (Fin 24) then v ⟨i, h⟩ else 0
  map_add' v w := by
    ext i
    dsimp
    split <;> simp
  map_smul' c v := by
    ext i
    dsimp
    split <;> simp


@[simp] theorem extendWord_apply (D : Subgroup M24) (v : FixedPoint D → ZMod 2)
    (i : FixedPoint D) : extendWord D v i.val = v i := by
  classical
  change (if h : i.val ∈ MulAction.fixedPoints D (Fin 24) then v ⟨i.val, h⟩ else 0) = _
  rw [dif_pos i.property]

theorem extendWord_sum (D : Subgroup M24) (v : FixedPoint D → ZMod 2) :
    ∑ i, extendWord D v i = ∑ i, v i := by
  classical
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective v (extendWord D v)
  · intro i hi
    change (if h : i ∈ MulAction.fixedPoints D (Fin 24) then v ⟨i, h⟩ else 0) = 0
    rw [dif_neg (fun h => hi ⟨⟨i, h⟩, rfl⟩)]
  · intro i
    exact (extendWord_apply D v i).symm

def extendCore (D : Subgroup M24) : BinaryPermutation.core (FixedPoint D) →ₗ[ZMod 2] Core :=
  ((extendWord D).comp (BinaryPermutation.core (FixedPoint D)).subtype).codRestrict Core
    (fun v => by
      change (∑ i, extendWord D v.val i) = 0
      rw [extendWord_sum]
      exact v.property)

theorem extendCore_fixed (D : Subgroup M24) (v : BinaryPermutation.core (FixedPoint D))
    (d : D) : coreRepresentation d.val (extendCore D v) = extendCore D v := by
  classical
  apply Subtype.ext
  ext i
  change extendWord D v.val (d.val.val.symm i) = extendWord D v.val i
  by_cases hi : i ∈ MulAction.fixedPoints D (Fin 24)
  · have he : d.val.val.symm i = i := hi d⁻¹
    rw [he]
  · have hn : d.val.val.symm i ∉ MulAction.fixedPoints D (Fin 24) := by
      intro h
      have he : d.val.val (d.val.val.symm i) = d.val.val.symm i := h d
      have hsame : i = d.val.val.symm i := by simpa using he
      exact hi (hsame ▸ h)
    change (if h : d.val.val.symm i ∈ MulAction.fixedPoints D (Fin 24) then _ else 0) =
      (if h : i ∈ MulAction.fixedPoints D (Fin 24) then _ else 0)
    rw [dif_neg hi, dif_neg hn]

/-- The literal cocode image of an even word supported on the fixed points. -/
def toCocode (D : Subgroup M24) : BinaryPermutation.core (FixedPoint D) →ₗ[ZMod 2] Cocode :=
  codeInCore.mkQ.comp (extendCore D)

theorem toCocode_mem_fixedSpace (D : Subgroup M24)
    (v : BinaryPermutation.core (FixedPoint D)) :
    toCocode D v ∈ fixedSpace cocodeRepresentation D := by
  intro d
  change codeInCore.mkQ (coreRepresentation d.val (extendCore D v)) = _
  rw [extendCore_fixed]
  rfl

/-- The canonical map to the actual fixed subspace; bijectivity is a separate theorem. -/
def toFixedCocode (D : Subgroup M24) : BinaryPermutation.core (FixedPoint D) →ₗ[ZMod 2]
    fixedSpace cocodeRepresentation D :=
  (toCocode D).codRestrict _ (toCocode_mem_fixedSpace D)

theorem extendCore_pair (D : Subgroup M24) (i j : FixedPoint D) :
    extendCore D (pair i j) = pair i.val j.val := by
  apply Subtype.ext
  ext k
  by_cases hk : k ∈ MulAction.fixedPoints D (Fin 24)
  · change (if h : k ∈ MulAction.fixedPoints D (Fin 24) then
      (Pi.single i 1 + Pi.single j 1 : FixedPoint D → ZMod 2) ⟨k, h⟩ else 0) = _
    rw [dif_pos hk]
    simp only [pair, Pi.add_apply, Pi.single_apply, Subtype.ext_iff]
  · have hki : k ≠ i.val := by intro he; exact hk (he ▸ i.property)
    have hkj : k ≠ j.val := by intro he; exact hk (he ▸ j.property)
    change (if h : k ∈ MulAction.fixedPoints D (Fin 24) then _ else 0) = _
    rw [dif_neg hk]
    simp [pair, hki, hkj]

theorem toCocode_pair (D : Subgroup M24) (i j : FixedPoint D) (hij : i ≠ j) :
    toCocode D (pair i j) = twoSubsetClass {i.val, j.val}
      (by simp [show i.val ≠ j.val from fun h => hij (Subtype.ext h)]) := by
  change codeInCore.mkQ (extendCore D (pair i j)) = _
  rw [extendCore_pair]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  ext k
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  change (Pi.single i.val 1 + Pi.single j.val 1 : Full) k = wordOfSet {i.val, j.val} k
  by_cases hki : k = i.val
  · subst k
    simp [wordOfSet, hval]
  · by_cases hkj : k = j.val
    · subst k
      simp [wordOfSet, hval]
    · simp [wordOfSet, hki, hkj]

theorem toCocode_pair_mem (D : Subgroup M24) (i j : FixedPoint D) (hij : i ≠ j) :
    toCocode D (pair i j) ∈ cocodeO2 := by
  exact ⟨{i.val, j.val}, _, toCocode_pair D i j hij⟩

theorem toCocode_pointPair_mem (D : Subgroup M24) (i j : FixedPoint D)
    (hi : i.val = 0) (hij : i ≠ j) :
    toCocode D (pair i j) ∈ m23CocodeO2 := by
  refine ⟨{i.val, j.val}, _, ?_, toCocode_pair D i j hij⟩
  simp [hi]

theorem finrank_fixedPoint_core (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6) :
    Module.finrank (ZMod 2) (BinaryPermutation.core (FixedPoint D)) = 5 := by
  have hc : Fintype.card (FixedPoint D) = 6 := by simpa only [Nat.card_eq_fintype_card] using hD
  have : Nonempty (FixedPoint D) := Fintype.card_pos_iff.mp (by omega)
  rw [BinaryPermutation.finrank_core, hc]


@[simp] theorem normalizerPerm_apply (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24)) (i : FixedPoint D) :
    (normalizerPerm D n i).val = n.val • i.val := rfl

@[simp] theorem fixedCocodeRepresentation_apply (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24)) (v : fixedSpace cocodeRepresentation D) :
    (fixedCocodeRepresentation D n v).val = cocodeRepresentation n.val v.val := rfl

@[simp] theorem toFixedCocode_apply (D : Subgroup M24)
    (v : BinaryPermutation.core (FixedPoint D)) :
    (toFixedCocode D v).val = toCocode D v := rfl

end
end MathieuCode.SixPoint
