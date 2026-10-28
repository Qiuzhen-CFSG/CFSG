module

public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Geometry
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Block
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.BlockOrbits
public import Theory.Representation.SU3.CubicDegree.InnerActors.Reduction

/-!
# Generation of binary SU₃ by three conjugate Sylow centers

The two opposite centers contain the fixed-field SL₂ block. A word in the
first and third centers connects its two isotropic-line orbits.
The explicit block-orbit decomposition therefore gives transitivity, and the
normal-closure argument in `ThreeRoots.Geometry` gives generation of SU₃.
Sylow conjugacy and a genuine Hermitian basis change retain arbitrary forms,
all exponents at least two, and the full scalar kernel.

The coordinate proof in `ThreeRoots.BlockOrbits` discharges the block-orbit
premise in `generation`. Characteristic two follows from the field order.
The final theorem applies generation to the literal inner-actor estimate,
retaining only the independent `RootControl` premise. The conditional
block-orbit reductions remain available with their original interfaces.

Source: Huppert II.10.12 for Hermitian coordinates; Aschbacher--Smith K.3.3,
printed p.456, and the fixed-space bound used in K.1, printed pp.451--453.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.BorelTorus.EvenCenterAction
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem triple_transitive_of_block_orbits (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (b : F) (hb : b + J.conj b = 1) (ho : BlockOrbitDecomposition J hJ b) :
    IsotropicLineTransitive J (triple J hJ b hb) := by
  intro v hv hi
  have hblock : (block J hJ).range ≤ triple J hJ b hb :=
    (block_range_le_pair J hJ).trans le_sup_left
  rcases ho v hv hi with ⟨A, a, ha, hAv⟩ | ⟨A, a, ha, hAv⟩
  · exact ⟨block J hJ A, hblock ⟨A, rfl⟩, a, ha, hAv⟩
  · obtain ⟨g, hg, he⟩ := exists_connector J hJ b hb
    refine ⟨block J hJ A * g, (triple J hJ b hb).mul_mem (hblock ⟨A, rfl⟩) hg,
      a, ha, ?_⟩
    intro i
    change ((block J hJ A).val.val * g.val.val) i 0 = _
    simpa only [Matrix.mul_apply, he, Matrix.mulVec, dotProduct] using hAv i

theorem standard_generation_of_block_orbits (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s)
    (b : F) (hb : b + J.conj b = 1) (ho : BlockOrbitDecomposition J hJ b) :
    ThreeRootGeneration J.specialSubgroup := by
  apply generation_of_triple J hJ hs hcard hfixed b hb
  exact eq_top_of_isotropicLineTransitive J hJ hs hcard hfixed _
    (le_sup_left.trans le_sup_left) (triple_transitive_of_block_orbits J hJ b hb ho)

theorem generation_of_block_orbits (J : HermitianForm 3 F)
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ho : ∀ b : F, b + J.conj b = 1 → BlockOrbitDecomposition (standardForm J) rfl b) :
    ThreeRootGeneration J.specialSubgroup := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  obtain ⟨C, hC⟩ := exists_standard_basis J (2 ^ s) hcard hf
  apply of_equiv (specialEquiv J C hC)
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J (2 ^ s) hcard hf 1 (by simp)
  exact standard_generation_of_block_orbits (standardForm J) rfl hs hcard hf b hb (ho b hb)

/-- The literal inner actor estimate, with only the explicit block-orbit
calculation and the independent root-control premise remaining. -/
theorem finrank_le_of_inner_actor_of_block_orbits
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ho : ∀ b : F, b + J.conj b = 1 → BlockOrbitDecomposition (standardForm J) rfl b)
    (hr : RootControl J.specialSubgroup s)
    (σ : Representation (ZMod 2) J.specialSubgroup V) (hi : σ.IsIrreducible)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (A : Subgroup (BinaryOffender.linearNormalizer σ)) (hA : BinaryOffender.IsElementaryTwo A)
    (hc : BinaryOffender.fixedCodim (BinaryOffender.normalizerRepresentation σ) A ≤
      2 * BinaryOffender.rank A)
    (hinner : A ≤ (BinaryOffender.actionImage σ).subgroupOf (BinaryOffender.linearNormalizer σ)) :
    Module.finrank (ZMod 2) V ≤ 6 * s :=
  finrank_le_of_inner_actor_of_root_geometry J hs hcard hconj hr
    (generation_of_block_orbits J hs hcard hconj ho) σ hi hk A hA hc hinner

omit [CharP F 2] in
/-- Every Sylow two-center of the full SU₃ has three conjugates generating
SU₃, for every Hermitian form and every exponent `s ≥ 2`. In particular,
the possible scalar center for odd `s` is retained. -/
theorem generation (J : HermitianForm 3 F)
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) :
    ThreeRootGeneration J.specialSubgroup := by
  let : CharP F 2 := charTwo_of_card hcard
  exact generation_of_block_orbits J hs hcard hconj
    (fun b hb => blockOrbitDecomposition (standardForm J) rfl b hb)

omit [CharP F 2] in
/-- The literal inner-actor estimate with three-center generation proved.
Only root control remains as an independent group-geometric premise. -/
theorem finrank_le_of_inner_actor_of_root_control
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hr : RootControl J.specialSubgroup s)
    (σ : Representation (ZMod 2) J.specialSubgroup V) (hi : σ.IsIrreducible)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (A : Subgroup (BinaryOffender.linearNormalizer σ)) (hA : BinaryOffender.IsElementaryTwo A)
    (hc : BinaryOffender.fixedCodim (BinaryOffender.normalizerRepresentation σ) A ≤
      2 * BinaryOffender.rank A)
    (hinner : A ≤ (BinaryOffender.actionImage σ).subgroupOf (BinaryOffender.linearNormalizer σ)) :
    Module.finrank (ZMod 2) V ≤ 6 * s :=
  finrank_le_of_inner_actor_of_root_geometry J hs hcard hconj hr
    (generation J hs hcard hconj) σ hi hk A hA hc hinner

end Representation.SU3.CubicDegree.InnerActors.ThreeRoots
