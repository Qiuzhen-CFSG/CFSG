module
public import CFSG.Quasithin.Chapter2.Section04.BlockResidual
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Mathlib.GroupTheory.Complement
/-!
# The torus-normalizer complement

For a coprime torus B normalizing R, N_R(B) equals C_R(B), because its
commutators with B lie in both R and B. Thus C_R(B) = 1 makes the torus
normalizer disjoint from R. The actual Frattini factorization then gives a
complement inside T. An element of this complement outside R whose square
lies in R is an involution. Finally, Sylow maximality identifies L ∩ S
with R, so a complement to R in S lifts to a complement to L in H.

These are the splitting steps in 2.4.8(5) and the opening paragraph of
2.4.14. The torus and Frattini factorization still require construction.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.530, 532–533.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G]

private theorem normalizer_intersection_eq_centralizer (R B : Subgroup G)
    (hBR : B ≤ normalizer (R : Set G)) (hdis : Disjoint R B) :
    R ⊓ normalizer (B : Set G) = R ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · intro r hr
    refine ⟨hr.1, mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hcR : ⁅r, b⁆ ∈ R :=
      le_normalizer_iff_commutator_le_left.mp hBR (commutator_mem_commutator hr.1 hb)
    have hcB : ⁅r, b⁆ ∈ B :=
      B.mul_mem ((mem_normalizer_iff.mp hr.2 b).mp hb) (B.inv_mem hb)
    have he : ⁅r, b⁆ = 1 := disjoint_def.mp hdis hcR hcB
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  · exact inf_le_inf_left _ (centralizer_le_normalizer _)

/-- The fixed-free coprime torus gives a genuine disjoint complement candidate. -/
theorem disjoint_torusNormalizer_of_fixedFree (R B : Subgroup G)
    (hBR : B ≤ normalizer (R : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card R))
    (hfixed : R ⊓ centralizer (B : Set G) = ⊥) :
    Disjoint R (normalizer (B : Set G)) := by
  rw [disjoint_iff, normalizer_intersection_eq_centralizer R B hBR
    (disjoint_of_coprime_natCard hcop.symm), hfixed]

/-- The representative chosen in N_T(B) in 2.4.14 is an involution. -/
theorem order_two_of_torusNormalizer_square_mem (R B : Subgroup G)
    (hBR : B ≤ normalizer (R : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card R))
    (hfixed : R ⊓ centralizer (B : Set G) = ⊥)
    {t : G} (htB : t ∈ normalizer (B : Set G))
    (ht2 : t ^ 2 ∈ R) (ht : t ∉ R) : orderOf t = 2 := by
  apply orderOf_eq_prime
  · exact disjoint_def.mp (disjoint_torusNormalizer_of_fixedFree R B hBR hcop hfixed)
      ht2 ((normalizer (B : Set G)).pow_mem htB 2)
  · exact fun he => ht (he ▸ R.one_mem)

/-- The source Frattini factorization gives an actual complement inside T. -/
theorem torusNormalizer_complement (T R B : Subgroup G)
    (hRT : R ≤ T) (hTR : T ≤ normalizer (R : Set G))
    (hBR : B ≤ normalizer (R : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card R))
    (hfixed : R ⊓ centralizer (B : Set G) = ⊥)
    (hgen : R ⊔ (T ⊓ normalizer (B : Set G)) = T) :
    IsComplement' (R.subgroupOf T) ((normalizer (B : Set G)).subgroupOf T) := by
  have hdis := disjoint_torusNormalizer_of_fixedFree R B hBR hcop hfixed
  let _ : (R.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hRT).mpr hTR
  have hdisT : Disjoint (R.subgroupOf T) ((normalizer (B : Set G)).subgroupOf T) := by
    rw [disjoint_def]
    intro x hxR hxB
    exact Subtype.ext (disjoint_def.mp hdis hxR hxB)
  have hsup : R.subgroupOf T ⊔ (normalizer (B : Set G)).subgroupOf T = ⊤ := by
    apply Subgroup.map_injective T.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRT, subgroupOf_map_subtype,
      ← MonoidHom.range_eq_map, range_subtype, inf_comm, hgen]
  refine ⟨mul_injective_of_disjoint hdisT, ?_⟩
  intro t
  obtain ⟨r, hr, b, hb, he⟩ := mem_sup_of_normal_left.mp
    (show t ∈ R.subgroupOf T ⊔ (normalizer (B : Set G)).subgroupOf T by rw [hsup]; trivial)
  exact ⟨(⟨r, hr⟩, ⟨b, hb⟩), he⟩
/-- A Sylow of L lying in the two-subgroup S is the literal intersection L ∩ S. -/
theorem block_sylow_intersection [Finite G] {L S : Subgroup G}
    (P : Sylow 2 L) (hS : IsPGroup 2 S)
    (hPS : (P : Subgroup L).map L.subtype ≤ S) :
    S ⊓ L = (P : Subgroup L).map L.subtype := by
  have hsmall : IsPGroup 2 (S.subgroupOf L) :=
    hS.comap_of_injective L.subtype L.subtype_injective
  have hle : (P : Subgroup L) ≤ S.subgroupOf L :=
    map_le_iff_le_comap.mp hPS
  have he := P.is_maximal' hsmall hle
  have hm := congrArg (Subgroup.map L.subtype) he
  rwa [subgroupOf_map_subtype] at hm

/-- The group-splitting step of 2.4.12(1): a complement in S lifts to
a complement of the actual single block in H. Cyclicity and the field action
remain the separate model-theoretic conclusions. -/
theorem block_complement_of_sylow_complement [Finite G] {M : Subgroup G}
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (P : Sylow 2 d.block) (F : Subgroup d.H)
    (hPS : (P : Subgroup d.block).map d.block.subtype ≤ (d.S : Subgroup d.H))
    (hFS : F ≤ (d.S : Subgroup d.H))
    (hgen : (P : Subgroup d.block).map d.block.subtype ⊔ F = (d.S : Subgroup d.H))
    (hdis : Disjoint ((P : Subgroup d.block).map d.block.subtype) F) :
    IsComplement' d.block F := by
  have hnormal : d.block.Normal := hsingle ▸ d.L0_normal
  let := hnormal
  have hinter := block_sylow_intersection P d.S.isPGroup' hPS
  have hLF : Disjoint d.block F := by
    rw [disjoint_def]
    intro x hxL hxF
    have hxR : x ∈ (P : Subgroup d.block).map d.block.subtype :=
      hinter ▸ (show x ∈ (d.S : Subgroup d.H) ⊓ d.block from ⟨hFS hxF, hxL⟩)
    exact disjoint_def.mp hdis hxR hxF
  have hfull : d.block ⊔ F = ⊤ := by
    rw [← d.generated, ← hgen, ← sup_assoc,
      sup_eq_left.mpr (map_subtype_le (P : Subgroup d.block))]
  refine ⟨mul_injective_of_disjoint hLF, ?_⟩
  intro h
  obtain ⟨l, hl, f, hf, he⟩ := mem_sup_of_normal_left.mp
    (show h ∈ d.block ⊔ F by rw [hfull]; trivial)
  exact ⟨(⟨l, hl⟩, ⟨f, hf⟩), he⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
