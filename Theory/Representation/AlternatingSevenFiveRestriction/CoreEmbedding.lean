module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor
/-!
# The actual five-point core inside a Sylow-normalized A₅ in A₇

The full Sylow normalizer forces two fixed letters. Restriction to their
complement supplies the actual A₅ coordinates. Extension by zero embeds its
binary augmentation core equivariantly in the seven-point augmentation core.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup
namespace BinaryPermutation
private def embeddingLinear (l : Fin 5 ↪ Fin 7) : Full (Fin 5) →ₗ[ZMod 2] Full (Fin 7) :=
  ∑ k : Fin 5, (LinearMap.single (ZMod 2) (fun _ : Fin 7 => ZMod 2) (l k)).comp (LinearMap.proj k)
private theorem embeddingLinear_apply (l : Fin 5 ↪ Fin 7) (v : Full (Fin 5)) :
    embeddingLinear l v = ∑ k : Fin 5, Pi.single (l k) (v k) := by
  simp [embeddingLinear, LinearMap.sum_apply]
private theorem embeddingLinear_at (l : Fin 5 ↪ Fin 7) (v : Full (Fin 5)) (k : Fin 5) :
    embeddingLinear l v (l k) = v k := by
  rw [embeddingLinear_apply, Finset.sum_apply]
  simp only [Pi.single_apply, l.injective.eq_iff]
  simp
private theorem embeddingLinear_sum (l : Fin 5 ↪ Fin 7) (v : Full (Fin 5)) :
    ∑ i, embeddingLinear l v i = ∑ k, v k := by
  simp only [embeddingLinear_apply, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp
private def embeddingCore (l : Fin 5 ↪ Fin 7) : core (Fin 5) →ₗ[ZMod 2] core (Fin 7) :=
  ((embeddingLinear l).comp (core (Fin 5)).subtype).codRestrict _ (fun v => by
    change ∑ i, embeddingLinear l v i = 0
    rw [embeddingLinear_sum]
    exact v.property)
private theorem embeddingCore_injective (l : Fin 5 ↪ Fin 7) :
    Function.Injective (embeddingCore l) := by
  intro v w h
  apply Subtype.ext
  funext k
  have hh := congrArg (fun v : core (Fin 7) => v.val (l k)) h
  exact (embeddingLinear_at l v k).symm.trans (hh.trans (embeddingLinear_at l w k))
private theorem embeddingCore_equivariant (l : Fin 5 ↪ Fin 7)
    (a : Equiv.Perm (Fin 5)) (b : Equiv.Perm (Fin 7))
    (hab : ∀ k, b (l k) = l (a k)) (v : core (Fin 5)) :
    embeddingCore l (coreRepresentation (Fin 5) a v) =
      coreRepresentation (Fin 7) b (embeddingCore l v) := by
  apply Subtype.ext
  change embeddingLinear l (representation (Fin 5) a v) =
    representation (Fin 7) b (embeddingLinear l v)
  rw [embeddingLinear_apply, embeddingLinear_apply, map_sum]
  have hs (k : Fin 5) : representation (Fin 7) b (Pi.single (l k) (v.val k)) =
      Pi.single (l (a k)) (v.val k) := by
    funext i
    simp only [representation_apply, Pi.single_apply]
    have he : b.symm i = l k ↔ i = l (a k) := by
      rw [Equiv.symm_apply_eq, hab]
    simp only [he]
  simp_rw [hs]
  simpa only [representation_apply, Equiv.symm_apply_apply] using
    (Equiv.sum_comp a (fun k : Fin 5 => (Pi.single (l k) (v.val (a.symm k)) : Full (Fin 7)))).symm
theorem exists_five_core_embedding
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7)))) :
    ∃ eB : B ≃* alternatingGroup (Fin 5),
    ∃ j : core (Fin 5) →ₗ[ZMod 2] core (Fin 7), Function.Injective j ∧
      ∀ (b : B) v, j (coreRepresentation (Fin 5) (eB b).val v) =
        coreRepresentation (Fin 7) b.val.val (j v) := by
  classical
  obtain ⟨i,k,hik,hB⟩ := Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e S hSN
  let s : Finset (Fin 7) := {i,k}
  have hBs : B = fixingSubgroup (alternatingGroup (Fin 7)) (s : Set (Fin 7)) := by
    simpa only [s, Finset.coe_insert, Finset.coe_singleton] using hB
  have hc : Fintype.card (↑sᶜ) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl]
    simp [s,hik]
  let d : (↑sᶜ) ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let e0 := (MulEquiv.subgroupCongr hBs).trans
    (Atlas.Families.Alternating.stabilizerComplementEquiv s)
  let eB := e0.trans (Atlas.Families.Alternating.relabel d)
  let l : Fin 5 ↪ Fin 7 := d.symm.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨eB,embeddingCore l,embeddingCore_injective l,?_⟩
  intro b v
  apply embeddingCore_equivariant l (eB b).val b.val.val _ v
  intro a
  have he := Atlas.Families.Alternating.stabilizerComplementEquiv_apply s
    ((MulEquiv.subgroupCongr hBs) b) (d.symm a)
  change b.val.val (d.symm a).val = (d.symm ((Atlas.Families.Alternating.relabel d (e0 b)).val a)).val
  rw [Atlas.Families.Alternating.relabel_apply, d.symm_apply_apply]
  exact he.symm
end BinaryPermutation
