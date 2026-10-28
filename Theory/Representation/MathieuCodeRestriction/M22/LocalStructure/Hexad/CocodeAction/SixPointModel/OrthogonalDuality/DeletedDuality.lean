module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.LinearIdentification
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# The dual of the even six-coordinate module

The dot product pairs the full permutation module with its even core. Its
left radical consists exactly of the constants (test against pairs). Thus
the deleted module is the dual of the core, equivariantly for all coordinate
permutations. In particular this applies to the actual hexad stabilizer.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399.
-/

@[expose] public section
open scoped BigOperators
namespace MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
noncomputable section

section General
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- Dot product against even coordinate words. -/
def fullCorePairing : BinaryPermutation.Full Ω →ₗ[ZMod 2]
    Module.Dual (ZMod 2) (BinaryPermutation.core Ω) :=
  (dotProductEquiv (ZMod 2) Ω).toLinearMap.compl₂ (BinaryPermutation.core Ω).subtype

omit [Nonempty Ω] in
lemma fullCorePairing_apply (v : BinaryPermutation.Full Ω) (w : BinaryPermutation.core Ω) :
    fullCorePairing Ω v w = ∑ i, v i * w.val i := rfl

lemma ker_fullCorePairing : (fullCorePairing Ω).ker = BinaryPermutation.constants Ω := by
  ext v
  constructor
  · intro hv
    let a : Ω := Classical.choice inferInstance
    have hconst (i : Ω) : v i = v a := by
      let w : BinaryPermutation.core Ω := ⟨Pi.single i 1 + Pi.single a 1, by
        simp [BinaryPermutation.mem_core, Finset.sum_add_distrib]⟩
      have h := LinearMap.congr_fun hv w
      change dotProduct v (Pi.single i 1 + Pi.single a 1) = 0 at h
      simp only [dotProduct_add, dotProduct_single, mul_one] at h
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
    exact Submodule.mem_span_singleton.mpr ⟨v a, funext fun i => by
      simpa [BinaryPermutation.allOne] using (hconst i).symm⟩
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    apply LinearMap.ext
    intro w
    change (∑ i, (c • BinaryPermutation.allOne Ω) i * w.val i) = 0
    simp only [Pi.smul_apply, BinaryPermutation.allOne, smul_eq_mul, mul_one,
      ← Finset.mul_sum]
    rw [show ∑ i, w.val i = 0 from w.property, mul_zero]

/-- The perfect pairing of the deleted module with the even core. -/
def deletedCorePairing : BinaryPermutation.Deleted Ω →ₗ[ZMod 2]
    Module.Dual (ZMod 2) (BinaryPermutation.core Ω) :=
  (BinaryPermutation.constants Ω).liftQ (fullCorePairing Ω)
    (le_of_eq (ker_fullCorePairing Ω).symm)

lemma deletedCorePairing_mk (v : BinaryPermutation.Full Ω) (w : BinaryPermutation.core Ω) :
    deletedCorePairing Ω ((BinaryPermutation.constants Ω).mkQ v) w =
      ∑ i, v i * w.val i := rfl

lemma deletedCorePairing_injective : Function.Injective (deletedCorePairing Ω) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨u, rfl⟩ := (BinaryPermutation.constants Ω).mkQ_surjective v
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← ker_fullCorePairing Ω]
  exact hv

/-- The cocode deleted module is the dual of the even module. -/
def deletedCoreDualEquiv : BinaryPermutation.Deleted Ω ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (BinaryPermutation.core Ω) :=
  LinearEquiv.ofBijective (deletedCorePairing Ω) ⟨deletedCorePairing_injective Ω,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      simp [BinaryPermutation.finrank_deleted, BinaryPermutation.finrank_core])).mp
        (deletedCorePairing_injective Ω)⟩

lemma deletedCoreDualEquiv_mk (v : BinaryPermutation.Full Ω) (w : BinaryPermutation.core Ω) :
    deletedCoreDualEquiv Ω ((BinaryPermutation.constants Ω).mkQ v) w =
      ∑ i, v i * w.val i := rfl

/-- Contragredient equivariance, including the inverse on the test vector. -/
lemma deletedCoreDualEquiv_equivariant (g : Equiv.Perm Ω) (v : BinaryPermutation.Deleted Ω) :
    deletedCoreDualEquiv Ω (BinaryPermutation.deletedRepresentation Ω g v) =
      (BinaryPermutation.coreRepresentation Ω).dual g (deletedCoreDualEquiv Ω v) := by
  obtain ⟨u, rfl⟩ := (BinaryPermutation.constants Ω).mkQ_surjective v
  apply LinearMap.ext
  intro w
  change (∑ i, u (g.symm i) * w.val i) = ∑ i, u i * w.val (g i)
  simpa using Equiv.sum_comp g.symm (fun i => u i * w.val (g i))
end General

/-- The actual supported M22 cocode image paired with the six-coordinate core. -/
def imageCoreDualEquiv : imageSpace ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (BinaryPermutation.core H) :=
  imageEquiv.trans (deletedCoreDualEquiv H)

lemma imageCoreDualEquiv_apply (v : BinaryPermutation.core O.val)
    (w : BinaryPermutation.core H) :
    imageCoreDualEquiv ⟨toM22 v, LinearMap.mem_range_self _ _⟩ w =
      ∑ i, v.val (inOctad i) * w.val i := by
  change deletedCoreDualEquiv H (imageEquiv _) w = _
  rw [imageEquiv_apply]
  rfl

lemma imageCoreDualEquiv_equivariant {G : Type*} [Group G]
    (f : G →* m22PairStabilizer)
    (g : Stabilizer f) (v : imageSpace) :
    imageCoreDualEquiv (imageRepresentation f g v) =
      (BinaryPermutation.coreRepresentation H).dual (coordinateAction f g)
        (imageCoreDualEquiv v) := by
  change deletedCoreDualEquiv H (imageEquiv _) = _
  rw [imageEquiv_equivariant, deletedCoreDualEquiv_equivariant]
  rfl

end
end MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
