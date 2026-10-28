module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.DegreeTen.Coordinates
public import Theory.SpecificGroups.AlternatingSix.M10.Action.SylowTransport

/-!
# The ten concrete Sylow subgroups and their conjugation action

Embed each order-nine range from `Coordinates` into the literal M₁₀ extension.
The subgroup images distinguish the ten Sylow subgroups. The four marked
automorphisms belong to that extension, and their action on the two generators
of each nine-group gives their action on the Sylow subgroup. In particular the
last automorphism is exactly `rotation * transposition`; its action is obtained
from its actual pentad formula, not from an abstract model comparison.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), the degree-ten action used in 4.10, pp.41–42.
-/

@[expose] public section

open Subgroup
namespace AlternatingSix.M10.Action.DegreeTen
open ShadowLocal
open Atlas.Comparisons.Exceptional.TriplePartitions

noncomputable def label (i : Fin 10) : Sylow 3 extension :=
  markedSylow (nineGroup i) (card_nineGroup i)

theorem label_map (i : Fin 10) :
    (label i).toSubgroup.map extension.subtype = nine (nineGroup i) :=
  map_subgroupOf_eq_of_le (nine_le_extension _ (card_nineGroup i))

theorem label_injective : Function.Injective label := by
  intro i j hij
  have hD : nineGroup i = nineGroup j := by
    apply Subgroup.map_injective permutationAction_injective
    have h := congrArg (fun P : Sylow 3 extension => P.toSubgroup.map extension.subtype) hij
    simpa only [label_map, nine] using h
  have hm : embedding i first ∈ nineGroup j := hD ▸ (show embedding i first ∈ nineGroup i from ⟨first, rfl⟩)
  obtain ⟨x, hx⟩ := hm
  exact embedding_separates i j x hx

def naturalGenerator (a : A6) : extension :=
  ⟨permutationAction a, (permutationAction_mem_extension_iff _).mpr a.property⟩

noncomputable def generator : Fin 4 → extension := ![
  naturalGenerator firstCycle, naturalGenerator secondCycle, naturalGenerator doubleSwap,
  ⟨Identification.rotation * Identification.transposition,
    show Identification.rotation * Identification.transposition ∈
      ShadowLocal.inner ⊔ zpowers (Identification.rotation * Identification.transposition) from
      Subgroup.mem_sup_right (mem_zpowers _)⟩]

theorem generator_apply (k : Fin 4) (a : A6) :
    ((generator k : AutA6) a).val = generatorHom k a.val := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · change GLS3.Chapter5.outerHom
        (Identification.twist * (Identification.transpositionPerm * a.val *
          Identification.transpositionPerm⁻¹) * Identification.twist⁻¹) =
      GLS3.Chapter5.outerHom ((Identification.twist * Identification.transpositionPerm) *
        a.val * (Identification.twist * Identification.transpositionPerm)⁻¹)
    apply congrArg GLS3.Chapter5.outerHom
    group

theorem generator_conjugates (k : Fin 4) (a : A6) :
    (generator k : AutA6) * permutationAction a.val * (generator k : AutA6)⁻¹ =
      permutationAction (generatorHom k a.val) := by
  rw [← generator_apply, permutationAction_coe, permutationAction_coe]
  ext b
  simp

theorem embedding_decompose (i : Fin 10) (x : E) :
    embedding i x = (embedding i first) ^ x.1.toAdd.val *
      (embedding i second) ^ x.2.toAdd.val := by
  have hf : baseEmbedding first = firstCyclePerm := by decide +kernel
  have hs : baseEmbedding second = secondCyclePerm := by decide +kernel
  change (MulAut.conj (relabel i)) (firstCyclePerm ^ x.1.toAdd.val *
    secondCyclePerm ^ x.2.toAdd.val) =
    ((MulAut.conj (relabel i)) (baseEmbedding first)) ^ x.1.toAdd.val *
    ((MulAut.conj (relabel i)) (baseEmbedding second)) ^ x.2.toAdd.val
  rw [hf, hs, map_mul, map_pow, map_pow]

theorem generator_mem (k : Fin 4) (i : Fin 10) (x : E) :
    generatorHom k (embedding i x) ∈ nineGroup (permutation k i) := by
  rw [embedding_decompose, map_mul, map_pow, map_pow]
  have hf : generatorHom k (embedding i first) ∈ nineGroup (permutation k i) :=
    ⟨imageCoordinates k i 0, (generator_images k i 0).symm⟩
  have hs : generatorHom k (embedding i second) ∈ nineGroup (permutation k i) :=
    ⟨imageCoordinates k i 1, (generator_images k i 1).symm⟩
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hf _) (Subgroup.pow_mem _ hs _)

theorem generator_smul (k : Fin 4) (i : Fin 10) :
    generator k • label i = label (permutation k i) := by
  apply Sylow.ext
  apply Eq.symm
  apply (generator k • label i).is_maximal' (label (permutation k i)).isPGroup'
  change (label i).toSubgroup.map (MulAut.conj (generator k)).toMonoidHom ≤ _
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x.val ∈ nine (nineGroup i) := hx
  obtain ⟨p, hp, hpx⟩ := hx'
  obtain ⟨z, rfl⟩ := hp
  change (generator k : AutA6) * x.val * (generator k : AutA6)⁻¹ ∈ nine (nineGroup (permutation k i))
  rw [← hpx, generator_conjugates k ⟨embedding i z, embedding_even i z⟩]
  exact ⟨_, generator_mem k i z, rfl⟩
end AlternatingSix.M10.Action.DegreeTen
