module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.Linear

/-!
# Native octad placement of involution centralizers

The elementary octad kernel is transitive on the complementary sixteen points.
An element fixing one such point therefore fixes them all; its nonidentity
members have precisely the octad as their fixed-point set. Their centralizers
stabilize that octad, normalize its kernel, and contain it in their intrinsic
two-core. Self-centrality of the octad two-core also places the center of every
compatible Sylow subgroup in the kernel.

Source: the compatible marking preceding Aschbacher--Smith H.14.1 and the
local setup of H.16.2, printed pp.396,402--403. These are placement results;
they do not assert the second elementary supplement or its code centralizer.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative


namespace MathieuCode

/-- The whole setwise octad stabilizer fixes the literal octad vector. -/
theorem octadVector_fixed_stabilizer (O : Octad) :
    octadVector O ∈ fixedSpace codeRepresentation (octadStabilizer O) := by
  intro g
  have he : g.val • O.val = O.val := g.property
  change codeRepresentation g.val (octadVector O) = octadVector O
  unfold octadVector
  rw [codeRepresentation_mk]
  congr 1
  apply Subtype.ext
  change BinaryPermutation.representation (Fin 24) g.val.val (wordOfSet O.val) = _
  rw [permute_wordOfSet]
  exact congrArg wordOfSet he

/-- The octad fixed line is pointwise fixed by the full octad stabilizer. -/
theorem octad_fixedSpace_le_stabilizer_fixedSpace (O : Octad) :
    fixedSpace codeRepresentation (octadPointwiseKernel O) ≤
      fixedSpace codeRepresentation (octadStabilizer O) := by
  rw [octad_fixedSpace_eq_span]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (octadVector_fixed_stabilizer O))

theorem octad_pointwiseKernel_elementary (O : Octad) : IsElementaryAbelian 2 (octadPointwiseKernel O) := by
  rw [← octad_core_map_eq_pointwise]
  let := (octad_core_structure O).2
  exact IsElementaryAbelian.map _

theorem octad_kernel_fixed_point_iff (O : Octad) (z : M24) (hz : z ∈ octadPointwiseKernel O)
    (hne : z ≠ 1) (i : Fin 24) : z • i = i ↔ i ∈ O.val := by
  constructor
  · intro hi
    by_contra hio
    apply hne
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro j
    by_cases hj : j ∈ O.val
    · exact (mem_octadPointwiseKernel O z).mp hz j hj
    obtain ⟨a, ha⟩ := octad_kernel_transitive O i j hio hj
    let := octad_pointwiseKernel_elementary O
    have hc : z * a.val = a.val * z := congrArg Subtype.val (mul_comm (⟨z, hz⟩ : octadPointwiseKernel O) a)
    change z • j = j
    rw [← ha, ← mul_smul, hc, mul_smul, hi]
  · exact (mem_octadPointwiseKernel O z).mp hz i

theorem octad_kernel_centralizer_le_stabilizer (O : Octad) (z : M24) (hz : z ∈ octadPointwiseKernel O)
    (hne : z ≠ 1) : Subgroup.centralizer ({z} : Set M24) ≤ octadStabilizer O := by
  intro g hg
  change g • O.val = O.val
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_smul_finset.mp hj
    apply (octad_kernel_fixed_point_iff O z hz hne _).mp
    rw [← mul_smul, ← hc, mul_smul, (octad_kernel_fixed_point_iff O z hz hne i).mpr hi]
  · simp

theorem sylow_center_mem_octad_pointwiseKernel (O : Octad) (T : Sylow 2 M24)
    (hT : (T : Subgroup M24) ≤ octadStabilizer O) (z : M24)
    (hz : z ∈ (Subgroup.center T).map (T : Subgroup M24).subtype) : z ∈ octadPointwiseKernel O := by
  obtain ⟨a, ha, rfl⟩ := hz
  rw [← octad_core_map_eq_pointwise]
  have hm : (⟨a.val, hT a.property⟩ : octadStabilizer O) ∈ pCore 2 (octadStabilizer O) := by
    apply octad_core_selfCentralizing O
    intro u hu
    have hut : u.val ∈ (T : Subgroup M24) :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hT) hu
    have he : u.val * a.val = a.val * u.val :=
      congrArg (fun b : T => (b : M24)) ((Subgroup.mem_center_iff.mp ha) ⟨u.val, hut⟩)
    exact Subtype.ext he
  exact Subgroup.mem_map_of_mem _ hm

theorem octad_stabilizer_le_normalizer_pointwiseKernel (O : Octad) :
    octadStabilizer O ≤ Subgroup.normalizer (octadPointwiseKernel O) := by
  rw [← octad_core_map_eq_pointwise]
  have h := (pCore 2 (octadStabilizer O)).le_normalizer_map (octadStabilizer O).subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using h

theorem octad_kernel_le_involution_core (O : Octad) (z : M24) (hz : z ∈ octadPointwiseKernel O)
    (hne : z ≠ 1) : octadPointwiseKernel O ≤
      (pCore 2 (Subgroup.centralizer ({z} : Set M24))).map
        (Subgroup.centralizer ({z} : Set M24)).subtype := by
  let C := Subgroup.centralizer ({z} : Set M24)
  let K := octadPointwiseKernel O
  let _ := octad_pointwiseKernel_elementary O
  have hKC : K ≤ C := by
    intro a ha
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : K) ⟨z, hz⟩)
  have hnormal : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr
      ((octad_kernel_centralizer_le_stabilizer O z hz hne).trans (octad_stabilizer_le_normalizer_pointwiseKernel O))
  have hp : IsPGroup 2 (K.subgroupOf C) :=
    (IsElementaryAbelian.isPGroup 2 K).comap_of_injective C.subtype C.subtype_injective
  have hle : K.subgroupOf C ≤ pCore 2 C := le_sSup ⟨hnormal, hp⟩
  simpa only [Subgroup.map_subgroupOf_eq_of_le hKC] using Subgroup.map_mono (f := C.subtype) hle

/-- The purely group-theoretic supplement used in Asc94, 39.1.
The carrier is independent of the code centralizer D. Constructing this record
and then identifying its carrier with D are separate mathematical obligations.
Normality is relative to the actual involution centralizer. -/
structure OctadInvolutionSupplement (O : Octad) (z : M24) where
  carrier : Subgroup M24
  le_centralizer : carrier ≤ Subgroup.centralizer ({z} : Set M24)
  normal : (carrier.subgroupOf (Subgroup.centralizer ({z} : Set M24))).Normal
  elementary : IsElementaryAbelian 2 carrier
  card : Nat.card carrier = 16
  intersection : octadPointwiseKernel O ⊓ carrier = Subgroup.zpowers z
  product : (octadPointwiseKernel O : Set M24) * (carrier : Set M24) =
    ((pCore 2 (Subgroup.centralizer ({z} : Set M24))).map
      (Subgroup.centralizer ({z} : Set M24)).subtype : Set M24)

end MathieuCode


