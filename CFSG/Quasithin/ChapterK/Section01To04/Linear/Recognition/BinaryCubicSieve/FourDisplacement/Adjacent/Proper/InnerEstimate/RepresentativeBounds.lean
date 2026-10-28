module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate.RepresentativeBounds.TensorWitnesses
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.Comparison
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Proper-support involution bounds from the shared tensor comparison

An irreducible binary module embeds in the natural–exterior tensor whenever
there is a nonzero intertwiner into that tensor. Its nonzero {0,1} highest
vector maps to the unique tensor seed. The explicit nine independent
involution images of seed translates therefore lift to independent images on
the original module. Rank–nullity gives the two literal fixed-codimension
bounds required by `ProperInvolutionBounds`.

The proved mixed-tensor comparison discharges the nonzero-intertwiner premise
in `proper_involution_bounds`. No module catalogue, absolute irreducibility,
or degree cutoff is used. The result supplies the precise input of
`proper_inner_estimate_of_involution_bounds`, which passes these cyclic bounds
to the common fixed space of each remaining elementary actor.

Source application: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript
Proposition 4.7, pp.25–26. The exact involutions are I+E₀₁ and
(I+E₀₁)(I+E₂₃), acting on the original representation.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace RepresentativeBounds
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem map_highest {σ : Representation (ZMod 2) Group V}
    (f : IntertwiningMap σ SupportSeparation.mixedTensor) {v : V}
    (h : LocalHighestVector σ {0, 1} v) :
    LocalHighestVector SupportSeparation.mixedTensor {0, 1} (f v) := by
  constructor
  · intro i j hij
    rw [← f.isIntertwining, h.upper_fixed i j hij]
  · intro i hi
    rw [← f.isIntertwining, h.inactive_fixed i hi]
  · intro i hi
    simpa only [map_add, f.isIntertwining, map_zero] using congrArg f (h.active_relation i hi)

/-- The explicit independent tensor images lift to displacement images on the
original module under any intertwiner taking its marked vector to the seed. -/
theorem nine_le_fixedCodim_of_seed_image [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V)
    (f : IntertwiningMap σ SupportSeparation.mixedTensor)
    (v : V) (hv : f v = seed) (r : Fin 2) :
    9 ≤ fixedCodim σ (Subgroup.zpowers (representative r)) := by
  let D : V →ₗ[ZMod 2] V := σ (representative r) - LinearMap.id
  let w : Fin 9 → V := fun i => σ (translate r i) v
  have hind : LinearIndependent (ZMod 2) (fun i => D (w i)) := by
    apply LinearIndependent.of_comp f.toLinearMap
    simpa only [D, w, LinearMap.sub_apply, LinearMap.id_apply,
      Function.comp_def, IntertwiningMap.toLinearMap_apply, map_sub,
      f.isIntertwining, hv] using independent_displacements r
  let lifts : Fin 9 → LinearMap.range D := fun i => ⟨D (w i), ⟨w i, rfl⟩⟩
  have hlifts : LinearIndependent (ZMod 2) lifts :=
    LinearIndependent.of_comp (LinearMap.range D).subtype hind
  have hdim : 9 ≤ Module.finrank (ZMod 2) (LinearMap.range D) := by
    simpa using hlifts.fintype_card_le_finrank
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hdim

/-- A nonzero mixed-tensor comparison yields both required bounds. Its
injectivity follows from irreducibility, so the highest vector has nonzero image. -/
theorem bounds_of_nonzero_intertwiner [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    (f : IntertwiningMap σ SupportSeparation.mixedTensor) (hf : f ≠ 0)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v) :
    9 ≤ fixedCodim σ (Subgroup.zpowers (simpleUpper 0)) ∧
      9 ≤ fixedCodim σ (Subgroup.zpowers (simpleUpper 0 * simpleUpper 2)) := by
  have : IsIrreducible σ := hi
  have hf_inj := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hf_v : f v ≠ 0 := by
    intro he
    exact hv (hf_inj (he.trans (map_zero f).symm))
  have hseed := highest_eq_seed (f v) hf_v (map_highest f h)
  exact ⟨nine_le_fixedCodim_of_seed_image σ f v hseed 0,
    nine_le_fixedCodim_of_seed_image σ f v hseed 1⟩
end RepresentativeBounds

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The shared mixed-tensor comparison producer suffices for the literal
proper-support involution contract on the original representation. -/
theorem proper_involution_bounds_of_mixedTensor_comparison
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    (hcomparison : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 1} v →
      ∃ f : IntertwiningMap σ SupportSeparation.mixedTensor, f ≠ 0) :
    ProperInvolutionBounds σ := by
  intro v hv h
  obtain ⟨f, hf⟩ := hcomparison v hv h
  exact RepresentativeBounds.bounds_of_nonzero_intertwiner σ hi f hf hv h

/-- Faithful irreducible binary SL₄ modules with proper adjacent highest
support satisfy both literal involution bounds on the original module. -/
theorem proper_involution_bounds [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (_hfaithful : Function.Injective σ)
    (hi : IsIrreducible σ) : ProperInvolutionBounds σ :=
  proper_involution_bounds_of_mixedTensor_comparison σ hi
    (fun _ hv h => SupportSeparation.mixedTensor_comparison σ hi hv h)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
