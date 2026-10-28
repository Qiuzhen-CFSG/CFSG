module

public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore
import all Theory.Mathieu.M24.LocalGeometry.LinearFourCore
public import Theory.Quasithin.EvenCharacteristic

/-!
# Self-centralizing two-cores of native M₂₄ octad stabilizers

The existing pointwise kernel has order sixteen and is elementary abelian;
the octad action has image A₈. The centralizer of this normal kernel has
normal image in A₈. A full image would make the kernel central, contradicting
the already constructed fixed-point-free action of a native heptad three-cycle.
Simplicity of A₈ forces the image to be trivial. The kernel is therefore
self-centralizing and equals the intrinsic two-core. Octad transitivity
transports the result to every native octad stabilizer.

This is an internal proof extension of `LinearFourCore`. The private `import all`
is used only for the two map equations below, leaving that module's existing
definition bodies and public boundary unchanged.

Source: GLS3, Table 5.3e, E₁₆.A₈; Aschbacher–Smith, Theorem 0.1.2(5)
and condition E, printed pp.3–4. Exhaustive local coverage is a separate step.
-/

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.LinearFourCore

/-- The lifted pointwise kernel uses the same native heptad inclusion. -/
public theorem kernelLift_coe (u : heptadKernel) :
    (kernelLift u).val = heptadLift u.val := by
  rfl

/-- The alternating quotient retains the actual octad permutation. -/
public theorem alternatingAction_coe (g : octadStabilizer seedOctad) :
    (alternatingAction g).val = action seedOctad g := by
  rfl

private theorem seed_kernel_not_central :
    centralizer ((action seedOctad).ker : Set (octadStabilizer seedOctad)) ≠ ⊤ := by
  intro htop
  have hall (u : heptadKernel) : u = 1 := by
    have hc : heptadLift (AlternatingSection.s AlternatingSection.c) ∈
        centralizer ((action seedOctad).ker : Set (octadStabilizer seedOctad)) := by
      rw [htop]
      trivial
    have hcomm := hc (kernelLift u).val (kernelLift u).property
    have hcomm' : (u : heptadStabilizer) * AlternatingSection.s AlternatingSection.c =
        AlternatingSection.s AlternatingSection.c * u := by
      apply heptadLift_injective
      simpa only [map_mul, kernelLift_coe] using hcomm
    apply (heptadConjugation_cycle_fixed_iff u).mp
    apply Subtype.ext
    rw [heptadConjugation_coe]
    exact (mul_inv_eq_iff_eq_mul).mpr hcomm'.symm
  have hsub : Subsingleton heptadKernel := ⟨fun u v => (hall u).trans (hall v).symm⟩
  have hc := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  rw [heptadKernel_card] at hc
  omega

/-- The pointwise octad kernel is self-centralizing in the octad stabilizer. -/
public theorem seed_kernel_selfCentralizing :
    centralizer ((action seedOctad).ker : Set (octadStabilizer seedOctad)) ≤
      (action seedOctad).ker := by
  let K := (action seedOctad).ker
  let C := centralizer (K : Set (octadStabilizer seedOctad))
  let : IsMulCommutative K := ⟨⟨kernel_mul_comm⟩⟩
  have hKC : K ≤ C := K.le_centralizer
  have hker : alternatingAction.ker = K := by
    ext g
    change (alternatingAction g = 1) ↔ action seedOctad g = 1
    simp only [Subtype.ext_iff, alternatingAction_coe, Subgroup.coe_one]
  let D := C.map alternatingAction
  have : D.Normal := Subgroup.Normal.map inferInstance alternatingAction
    alternatingAction_surjective
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
      (by rw [seed_card]; decide) (N := D) with hd | hd
  · intro g hg
    have hm : alternatingAction g ∈ D := ⟨g, hg, rfl⟩
    rw [hd] at hm
    change g ∈ K
    rw [← hker]
    exact hm
  · have hm : C.map alternatingAction = alternatingAction.range := by
      change D = alternatingAction.range
      rw [hd, MonoidHom.range_eq_top.mpr alternatingAction_surjective]
    have he := Subgroup.map_eq_range_iff.mp hm
    rw [codisjoint_iff, hker, sup_eq_left.mpr hKC] at he
    exact (seed_kernel_not_central he).elim

/-- The pointwise kernel is exactly the intrinsic two-core of the chosen octad stabilizer. -/
public theorem seed_core_eq_kernel :
    pCore 2 (octadStabilizer seedOctad) = (action seedOctad).ker := by
  apply le_antisymm core_le_kernel
  exact le_sSup ⟨inferInstance, IsPGroup.of_card (p := 2) (n := 4) (by
    simpa using kernel_card)⟩

/-- The intrinsic two-core of the chosen octad stabilizer is self-centralizing. -/
public theorem seed_core_selfCentralizing :
    centralizer (pCore 2 (octadStabilizer seedOctad) : Set (octadStabilizer seedOctad)) ≤
      pCore 2 (octadStabilizer seedOctad) := by
  rw [seed_core_eq_kernel]
  exact seed_kernel_selfCentralizing

/-- Every native octad stabilizer has a self-centralizing intrinsic two-core. -/
public theorem octad_core_selfCentralizing (O : Octad) :
    centralizer (pCore 2 (octadStabilizer O) : Set (octadStabilizer O)) ≤
      pCore 2 (octadStabilizer O) := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq seedOctad O
  have hs : octadStabilizer O =
      (octadStabilizer seedOctad).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 O.val =
      (MulAction.stabilizer M24 seedOctad.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [hs]
  exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g)
    (octadStabilizer seedOctad)).mpr seed_core_selfCentralizing

end Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
