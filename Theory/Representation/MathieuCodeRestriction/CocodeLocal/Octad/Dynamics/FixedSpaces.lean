module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Transport
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces
public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.RestrictionComparison
/-!
# Octad-kernel fixed spaces and their span

The native moment coordinates distinguish the fixed exterior pair directions.
Cyclic code/cocode duality and the checked code fixed-dimension calculation
show that each nonidentity cyclic fixed space is the six-dimensional octad
pair space plus its one direction. Two distinct directions give the common
fixed space for every noncyclic subgroup. All directions together span the
geometric parity hyperplane. No cyclic-rank hypothesis remains.

Source: Aschbacher--Smith, H.15.2(2,4--5), printed pp.398--399.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.CocodeOctad.Dynamics
open SmallKernelFixed
noncomputable section

lemma pairSpace_le_fixed (O : Octad) :
    supportedPairSpace O.val ≤ fixedSpace cocodeRepresentation (octadPointwiseKernel O) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P, hP, rfl⟩ g
  apply (pairVector_fixed_iff g.val P).mpr
  rw [Finset.smul_finset_def]
  calc
    _ = P.val.image id := Finset.image_congr fun i hi =>
      (mem_octadPointwiseKernel O g.val).mp g.property i (hP hi)
    _ = P.val := Finset.image_id

lemma cyclic_finrank (O : Octad) (g : M24) (hg : g ∈ octadPointwiseKernel O) (hne : g ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation (Subgroup.zpowers g)) = 7 := by
  rw [← code_cocode_fixed_finrank_cyclic]
  exact octad_kernel_involution_fixed_finrank O g hg hne

lemma cyclic_fixedCodim (O : Octad) (g : M24) (hg : g ∈ octadPointwiseKernel O) (hne : g ≠ 1) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers g) = 4 := by
  have h := fixedCodim_add_finrank cocodeRepresentation (Subgroup.zpowers g)
  rw [cyclic_finrank O g hg hne, finrank_cocode] at h
  omega

namespace CoordinateModel
variable {O : Octad} (C : CoordinateModel O)
include C

lemma actor_ne_one_iff (n : Fin 16) : (C.actor n).val ≠ 1 ↔ n ≠ 0 := by
  constructor
  · intro h hn
    exact h (hn ▸ C.actor_zero)
  · intro hn he
    apply hn
    apply C.actor.injective
    exact Subtype.ext (he.trans C.actor_zero.symm)

lemma vector_not_mem (n : Fin 16) (hn : n ≠ 0) : C.vector n ∉ supportedPairSpace O.val := by
  intro hv
  rw [← C.ker] at hv
  have h : decode n = 0 := congrArg Prod.snd ((C.vector_map n).symm.trans hv)
  exact hn (decode_bijective.1 (h.trans decode_zero.symm))

lemma cyclic_fixed (n : Fin 16) (hn : n ≠ 0) :
    fixedSpace cocodeRepresentation (Subgroup.zpowers (C.actor n).val) =
      supportedPairSpace O.val ⊔ Submodule.span (ZMod 2) {C.vector n} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · exact (pairSpace_le_fixed O).trans
        (fixedSpace_antitone cocodeRepresentation (Subgroup.zpowers_le.mpr (C.actor n).property))
    · exact Submodule.span_le.mpr
        (by rintro v (rfl : v = C.vector n); exact
        ((mem_fixedSpace_zpowers_iff _ _ _).mpr (C.vector_fixed n)))
  · rw [Submodule.finrank_sup_span_singleton (C.vector_not_mem n hn),
      finrank_supportedPairSpace, cyclic_finrank O _ (C.actor n).property
        ((C.actor_ne_one_iff n).mpr hn)]

lemma fixed_map (n : Fin 16) (hn : n ≠ 0) {v : Cocode}
    (hv : v ∈ fixedSpace cocodeRepresentation (Subgroup.zpowers (C.actor n).val)) :
    ∃ c : ZMod 2, C.map v = c • (0, decode n) := by
  rw [C.cyclic_fixed n hn] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  refine ⟨c, ?_⟩
  have hu0 : C.map u = 0 := by rw [← LinearMap.mem_ker, C.ker]; exact hu
  rw [map_add, map_smul, hu0, C.vector_map, zero_add]

lemma fixed_map_ne_zero (n : Fin 16) (hn : n ≠ 0) {v : Cocode}
    (hv : v ∈ fixedSpace cocodeRepresentation (Subgroup.zpowers (C.actor n).val))
    (hvu : v ∉ supportedPairSpace O.val) : C.map v = (0, decode n) := by
  obtain ⟨c, hc⟩ := C.fixed_map n hn hv
  have hb : c = 0 ∨ c = 1 := (by decide +kernel : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  rcases hb with rfl | rfl
  · exfalso
    apply hvu
    rw [← C.ker, LinearMap.mem_ker, hc, zero_smul]
  · simpa only [one_smul] using hc

lemma fixed_inter_le (n m : Fin 16) (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    fixedSpace cocodeRepresentation (Subgroup.zpowers (C.actor n).val) ⊓
      fixedSpace cocodeRepresentation (Subgroup.zpowers (C.actor m).val) ≤
        supportedPairSpace O.val := by
  intro v hv
  by_contra h
  have he := (C.fixed_map_ne_zero n hn hv.1 h).symm.trans (C.fixed_map_ne_zero m hm hv.2 h)
  exact hnm (decode_bijective.1 (congrArg Prod.snd he))

lemma kernel_fixed : fixedSpace cocodeRepresentation (octadPointwiseKernel O) =
    supportedPairSpace O.val := by
  apply le_antisymm _ (pairSpace_le_fixed O)
  apply le_trans _ (C.fixed_inter_le 1 2 (by decide) (by decide) (by decide))
  exact le_inf
    (fixedSpace_antitone _ (Subgroup.zpowers_le.mpr (C.actor 1).property))
    (fixedSpace_antitone _ (Subgroup.zpowers_le.mpr (C.actor 2).property))

lemma noncyclic_fixed (A : Subgroup M24) (hA : A ≤ octadPointwiseKernel O)
    (hnc : ¬ IsCyclic A) : fixedSpace cocodeRepresentation A = supportedPairSpace O.val := by
  apply le_antisymm _ ((pairSpace_le_fixed O).trans (fixedSpace_antitone _ hA))
  let : Nontrivial A := Nontrivial.of_not_isCyclic hnc
  obtain ⟨g, hg⟩ := exists_ne (1 : A)
  have hg1 : g.val ≠ 1 := fun h => hg (Subtype.ext h)
  have hnot : ¬ A ≤ Subgroup.zpowers g.val := fun h => hnc (Subgroup.isCyclic_of_le h)
  obtain ⟨a, ha, hag⟩ := SetLike.not_le_iff_exists.mp hnot
  have ha1 : a ≠ 1 := fun h => hag (h ▸ (Subgroup.zpowers g.val).one_mem)
  have hag' : a ≠ g.val := fun h => hag (h ▸ Subgroup.mem_zpowers g.val)
  obtain ⟨n, hn⟩ := C.actor.surjective ⟨g.val, hA g.property⟩
  obtain ⟨m, hm⟩ := C.actor.surjective ⟨a, hA ha⟩
  have hnv : (C.actor n).val = g.val := congrArg Subtype.val hn
  have hmv : (C.actor m).val = a := congrArg Subtype.val hm
  have hn0 : n ≠ 0 := (C.actor_ne_one_iff n).mp (hnv ▸ hg1)
  have hm0 : m ≠ 0 := (C.actor_ne_one_iff m).mp (hmv ▸ ha1)
  have hnm : n ≠ m := fun h => hag' (hmv.symm.trans ((congrArg (fun j => (C.actor j).val) h).symm.trans hnv))
  apply le_trans _ (C.fixed_inter_le n m hn0 hm0 hnm)
  rw [hnv, hmv]
  exact le_inf (fixedSpace_antitone _ (Subgroup.zpowers_le.mpr g.property))
    (fixedSpace_antitone _ (Subgroup.zpowers_le.mpr ha))

lemma span_eq : fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O) = octadHyperplane O := by
  have hU : supportedPairSpace O.val ≤ fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O) :=
    ((pairSpace_le_fixed O).trans (fixedSpace_antitone _ (Subgroup.zpowers_le.mpr (C.actor 1).property))).trans
      (fixedSpace_le_fixedSpaceSpan _ (C.actor 1).property ((C.actor_ne_one_iff 1).mpr (by decide)))
  apply le_antisymm
  · apply fixedSpaceSpan_le
    intro a ha hne v hv
    obtain ⟨n, hn⟩ := C.actor.surjective ⟨a, ha⟩
    have hnval : (C.actor n).val = a := congrArg Subtype.val hn
    have hn0 : n ≠ 0 := (C.actor_ne_one_iff n).mp (hnval ▸ hne)
    rw [← hnval] at hv
    obtain ⟨c, hc⟩ := C.fixed_map n hn0 hv
    change octadParity O v = 0
    rw [← C.parity, hc]
    change c * 0 = 0
    exact mul_zero _
  · intro v hv
    obtain ⟨n, hn⟩ := decode_bijective.2 (C.map v).2
    have hvm : C.map v = (0, decode n) := by
      apply Prod.ext
      · exact (C.parity v).trans hv
      · exact hn.symm
    have hd : v - C.vector n ∈ supportedPairSpace O.val := by
      rw [← C.ker, LinearMap.mem_ker, map_sub, hvm, C.vector_map, sub_self]
    by_cases hn0 : n = 0
    · apply hU
      rw [← C.ker, LinearMap.mem_ker, hvm, hn0, decode_zero]
      rfl
    · have hnfix : C.vector n ∈ fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O) :=
        fixedSpace_le_fixedSpaceSpan _ (C.actor n).property ((C.actor_ne_one_iff n).mpr hn0)
          ((mem_fixedSpace_zpowers_iff _ _ _).mpr (C.vector_fixed n))
      simpa only [sub_add_cancel] using Submodule.add_mem _ (hU hd) hnfix

end CoordinateModel

lemma octad_fixedSpace (O : Octad) :
    fixedSpace cocodeRepresentation (octadPointwiseKernel O) = supportedPairSpace O.val :=
  (model O).kernel_fixed

lemma octad_noncyclic_fixedSpace (O : Octad) (A : Subgroup M24)
    (hA : A ≤ octadPointwiseKernel O) (hnc : ¬ IsCyclic A) :
    fixedSpace cocodeRepresentation A = supportedPairSpace O.val :=
  (model O).noncyclic_fixed A hA hnc

lemma octad_fixedSpaceSpan (O : Octad) :
    fixedSpaceSpan cocodeRepresentation (octadPointwiseKernel O) = octadHyperplane O :=
  (model O).span_eq

end
end MathieuCode.CocodeOctad.Dynamics
