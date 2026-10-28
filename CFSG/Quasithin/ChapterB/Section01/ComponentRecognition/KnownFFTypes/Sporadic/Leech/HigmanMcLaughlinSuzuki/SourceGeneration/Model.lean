module

public import Theory.GroupTheory.InvolutionAutomorphismGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceGeneration.Certificates
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.Enumeration
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.PermutationFusion

/-!
# Five-conjugate generation for every involutory automorphism of HS

The checked generator-recovery words handle the two inner and two outer
permutation representatives. Existing exhaustive fusion in the exact carrier
and its normalizer transports these witnesses to every normalizer involution.
Conjugation by a normalizing permutation sends carrier-valued conjugators to
carrier-valued conjugators. The actual normalizer-to-automorphism equivalence
then gives the uniform abstract automorphism bound.

The two original ATLAS generators are recovered, so no group-family label,
order assertion, or unproved simplicity statement substitutes for generation.
Source: GM02 (2.5)--(2.6), Proposition 5.1, the HS paragraph; the fusion
marking is the one used for Aschbacher--Smith 16.1.5(10), printed p.1172.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceGeneration
open Subgroup Theory.GroupTheory
open _root_.Sporadic.LeechRelated.HS
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HSOuter

private def PermutationGenerates (p : Equiv.Perm (Fin 100)) : Prop :=
  ∃ c : Fin 5 → Carrier, generated ≤
    closure (Set.range fun i => inclusion (c i) * p * (inclusion (c i))⁻¹)

private theorem permutation_generates_conj {p : Equiv.Perm (Fin 100)}
    (hp : PermutationGenerates p) (g : PermutationNormalizer) :
    PermutationGenerates (g.val * p * g.val⁻¹) := by
  obtain ⟨c, hc⟩ := hp
  let d : Fin 5 → Carrier := fun i => generated.normalizerMonoidHom g (c i)
  refine ⟨d, ?_⟩
  have hm := Subgroup.map_mono (f := (MulAut.conj g.val : Equiv.Perm (Fin 100) →* Equiv.Perm (Fin 100))) hc
  rw [mem_normalizer_iff_map_conj_eq.mp g.property, MonoidHom.map_closure,
    ← Set.range_comp] at hm
  convert hm using 1
  congr 1
  apply congrArg Set.range
  funext i
  change (g.val * inclusion (c i) * g.val⁻¹) * (g.val * p * g.val⁻¹) *
    (g.val * inclusion (c i) * g.val⁻¹)⁻¹ =
    g.val * (inclusion (c i) * p * (inclusion (c i))⁻¹) * g.val⁻¹
  group

private theorem normalizer_generation_of_representatives
    (hrep : ∀ r : Fin 4, PermutationGenerates (Certificates.representative r))
    (n : PermutationNormalizer) (hn : n ≠ 1) (hn2 : n ^ 2 = 1) :
    PermutationGenerates n.val := by
  by_cases hi : n.val ∈ generated
  · let s : Carrier := ⟨n.val, hi⟩
    have hs2 : s ^ 2 = 1 := Subtype.ext (congrArg (fun x : PermutationNormalizer => x.val) hn2)
    have hs : s ≠ 1 := by
      intro h
      exact hn (Subtype.ext (congrArg (fun x : Carrier => x.val) h))
    rcases HSInner.ClassCoverage.involution_classes s
      (orderOf_eq_prime_iff.mpr ⟨hs2, hs⟩) with h | h
    · obtain ⟨g, hg⟩ := isConj_iff.mp h
      have he : inclusion g * Certificates.representative 0 * (inclusion g)⁻¹ = n.val :=
        congrArg _root_.Sporadic.LeechRelated.HS.inclusion hg
      rw [← he]
      exact permutation_generates_conj (hrep 0) (Subgroup.inclusion generated.le_normalizer g)
    · obtain ⟨g, hg⟩ := isConj_iff.mp h
      have he : inclusion g * Certificates.representative 1 * (inclusion g)⁻¹ = n.val :=
        congrArg _root_.Sporadic.LeechRelated.HS.inclusion hg
      rw [← he]
      exact permutation_generates_conj (hrep 1) (Subgroup.inclusion generated.le_normalizer g)
  · rcases outer_involution_permutation_fusion n
      (orderOf_eq_prime_iff.mpr ⟨hn2, hn⟩) hi with ⟨g, hg⟩ | ⟨g, hg⟩
    · rw [hg]
      exact permutation_generates_conj (hrep 2) g
    · rw [hg]
      exact permutation_generates_conj (hrep 3) g

private theorem automorphism_generation_of_permutation (n : PermutationNormalizer)
    (hp : PermutationGenerates n.val) :
    ∃ c : Fin 5 → Carrier, (MulAut.conj : Carrier →* MulAut Carrier).range ≤
      closure (Set.range fun i => MulAut.conj (c i) *
        generated.normalizerMonoidHom n * (MulAut.conj (c i))⁻¹) := by
  obtain ⟨c, hc⟩ := hp
  let inc : Carrier →* PermutationNormalizer := Subgroup.inclusion generated.le_normalizer
  let d (i : Fin 5) := inc (c i) * n * (inc (c i))⁻¹
  let H := closure (Set.range d)
  have hmap : H.map PermutationNormalizer.subtype =
      closure (Set.range fun i => inclusion (c i) * n.val * (inclusion (c i))⁻¹) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hi (s : Carrier) : inc s ∈ H := by
    obtain ⟨y, hy, he⟩ := hmap.symm ▸ hc s.property
    exact (Subtype.ext he : y = inc s) ▸ hy
  refine ⟨c, ?_⟩
  have hinner (s : Carrier) : generated.normalizerMonoidHom (inc s) = MulAut.conj s := rfl
  have himage : H.map generated.normalizerMonoidHom =
      closure (Set.range fun i => MulAut.conj (c i) *
        generated.normalizerMonoidHom n * (MulAut.conj (c i))⁻¹) := by
    change (Subgroup.closure _).map _ = _
    rw [MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  rw [← himage]
  rintro _ ⟨s, rfl⟩
  exact ⟨inc s, hi s, hinner s⟩

/-- Finite generation of the four concrete representatives suffices for
all abstract automorphisms, with conjugators in the original carrier. -/
theorem model_bound_of_representatives
    (hrep : ∀ r : Fin 4, ∃ c : Fin 5 → Carrier, generated ≤
      closure (Set.range fun i => inclusion (c i) * Certificates.representative r *
        (inclusion (c i))⁻¹)) :
    InvolutionInnerConjugateGenerationBound Carrier 5 := by
  intro t ht ht2
  obtain ⟨n, he⟩ := (normalizer_surjective_of_pointStabilizer_map pointStabilizer_map) t
  have hn : n ≠ 1 := by
    intro h
    exact ht (he.symm.trans (h ▸ map_one generated.normalizerMonoidHom))
  have hn2 : n ^ 2 = 1 := by
    apply normalizer_action_injective
    rw [map_pow, he, ht2, map_one]
  have h := automorphism_generation_of_permutation n
    (normalizer_generation_of_representatives hrep n hn hn2)
  rwa [he] at h

/-- Every nonidentity involutory automorphism has five HS-conjugates
whose generated subgroup contains the whole inner automorphism group. -/
theorem five_conjugates_on_automorphisms :
    InvolutionInnerConjugateGenerationBound Carrier 5 :=
  model_bound_of_representatives Certificates.representative_generates

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.SourceGeneration
