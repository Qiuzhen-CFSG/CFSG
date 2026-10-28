module
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Lifting section centralizers through solvable kernels

A perfect subgroup normalized by a solvable kernel is the solvable residual
of its full image preimage. Thus every lift of an image normalizer preserves
the original subgroup. A prime-group kernel on the restricted map then
reflects the local prime core and the section-centralizer commutator bound.
Finally, surjectivity on Sylow subgroups lifts a prime-power element with its
exact image while retaining prime-power order. An exact prime-order lift is
not required.

Source application: Aschbacher–Smith, 10.2.9, printed p.751, on the
constrained component's action quotient.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The characteristic perfect residual recovers the original normalizer. -/
theorem normalizer_comap_map_le_of_solvable_kernel
    (f : G →* H) (L : Subgroup G) [Group.IsPerfect L] [Group.IsSolvable f.ker]
    (hn : f.ker ≤ normalizer (L : Set G)) :
    (normalizer (L.map f : Set H)).comap f ≤ normalizer (L : Set G) := by
  have hres := map_solvableResidual_sup_eq_of_perfect_normalized L f.ker hn
  have hN : (normalizer (L.map f : Set H)).comap f ≤
      normalizer (↑(L ⊔ f.ker : Subgroup G) : Set G) := by
    simpa only [comap_map_eq] using (L.map f).le_normalizer_comap f
  simpa only [hres] using hN.trans (normalizer_le_normalizer_characteristic_image (L ⊔ f.ker)
    (solvableResidual (L ⊔ f.ker : Subgroup G)))

/-- Only the kernel restricted to the original subgroup must be a p-group. -/
theorem mem_pCoreIn_of_map_mem [Finite G] [Finite H] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (L : Subgroup G) (hk : IsPGroup p (f.subgroupMap L).ker)
    {x : G} (hx : x ∈ L) (hf : f x ∈ (L.map f).pCoreIn p) : x ∈ L.pCoreIn p := by
  have hcore := (f.subgroupMap L).comap_pCore_of_ker_isPGroup
    (f.subgroupMap_surjective L) hk
  apply mem_map_of_mem L.subtype (x := ⟨x,hx⟩)
  rw [←hcore]
  change f.subgroupMap L ⟨x,hx⟩ ∈ pCore p (L.map f)
  obtain ⟨z,hz,he⟩ := hf
  exact (Subtype.ext he : z = f.subgroupMap L ⟨x,hx⟩) ▸ hz

/-- Normalization and trivial action modulo the image two-core lift together. -/
theorem core_sectionCentralizer_comap_le [Finite G] [Finite H]
    (f : G →* H) (L : Subgroup G) [Group.IsPerfect L] [Group.IsSolvable f.ker]
    (hn : f.ker ≤ normalizer (L : Set G))
    (hk : IsPGroup 2 (f.subgroupMap L).ker) :
    (commutatorPreimage (normalizer (L.map f : Set H)) (L.map f)
      ((L.map f).pCoreIn 2)).comap f ≤
      commutatorPreimage (normalizer (L : Set G)) L (L.pCoreIn 2) := by
  let C := commutatorPreimage (normalizer (L.map f : Set H)) (L.map f)
    ((L.map f).pCoreIn 2)
  have hN : C.comap f ≤ normalizer (L : Set G) :=
    (comap_mono (commutatorPreimage_le _ _ _)).trans
      (normalizer_comap_map_le_of_solvable_kernel f L hn)
  apply le_commutatorPreimage hN
  apply commutator_le.mpr
  intro x hx l hl
  apply mem_pCoreIn_of_map_mem f L hk
  · exact le_normalizer_iff_commutator_le_right.mp hN
      (commutator_mem_commutator hx hl)
  · rw [map_commutatorElement]
    exact commutator_le.mp (commutator_commutatorPreimage_le _ _ _
      (normalizer_le_normalizer_characteristic_image (L.map f) (pCore 2 (L.map f))))
      (f x) hx (f l) (mem_map_of_mem f hl)

end Subgroup

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- A prime-power element has a prime-power preimage with the exact given image. -/
theorem exists_primePower_lift {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    {x : H} {n : ℕ} (hx : orderOf x = p ^ n) :
    ∃ y : G, f y = x ∧ ∃ k : ℕ, y ^ (p ^ k) = 1 := by
  have hp : IsPGroup p (zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers,hx])
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨S,hS⟩ := Sylow.mapSurjective_surjective hf p P
  have hxS : x ∈ (S : Subgroup G).map f := by
    change x ∈ (S.mapSurjective hf : Subgroup H)
    rw [hS]
    exact hP (mem_zpowers x)
  obtain ⟨y,hy,he⟩ := hxS
  obtain ⟨k,hk⟩ := S.isPGroup' ⟨y,hy⟩
  exact ⟨y,he,k,congrArg Subtype.val hk⟩

end MonoidHom
