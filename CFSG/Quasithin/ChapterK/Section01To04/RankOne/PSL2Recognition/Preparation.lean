module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Covers
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.PResidual.PrimeTo
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The actual PSL₂ actor in K.3.1

The existing covering theorem first identifies the whole layer with SL₂ over
its actual binary field. Self-centralization of F* then gives C_G(L)=1.
Consequently the original actor embeds in Aut(L), has elementary two-rank at
most the field degree r, and its literal quotient G/L has order dividing r.

For odd r every two-subgroup lies in L. Restriction and transport along the
matrix-group identification therefore preserve the source cubic-ratio bound.
In particular this removes outer actors from the exceptional SL₂(8) branch.
The general small-degree selection remains a separate representation argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Chapter K,
printed pp.451,453–454, and the binary PSL₂ automorphisms used in G.9.3.
-/

@[expose] public section

open scoped MatrixGroups
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The actual even central quotient gives a literal SL₂ field and group. -/
theorem exists_binary_sl2_equiv (h : SourceHypotheses ρ L)
    {r : ℕ} (hr : 2 ≤ r) (hq : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2 ^ r)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ r ∧ Nonempty (L ≃* SL(2,K)) := by
  have hp : KnownSimple.LinearParameters 2 (2 ^ r) :=
    ⟨(isPrimePow_nat_iff _).mpr ⟨2, r, Nat.prime_two, by omega, rfl⟩,
      le_rfl, fun _ => by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hr⟩
  have he : Even (2 ^ r) := (Nat.even_pow' (by omega : r ≠ 0)).mpr even_two
  obtain ⟨K, hK, hfin, hc, ⟨e⟩⟩ := h.isPSL_of_even_quotient hp he hq
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (by simpa [Nat.card_eq_fintype_card] using hc)
  exact ⟨K, hK, hfin, inferInstance, hc, ⟨e.trans (Theory.PSL2.sl2QuotientEquiv K).symm⟩⟩

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

omit [FiniteDimensional (ZMod 2) V] [Finite K] in
include h e in
/-- The centralizer of the layer in the actual source actor is trivial. -/
theorem psl2_centralizer_eq_bot : centralizer (L : Set G) = ⊥ := by
  have hCL : centralizer (L : Set G) ≤ L := by
    rw [← h.fitting]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  apply bot_unique
  intro g hg
  have hgZ : (⟨g, hCL hg⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (hg x x.property)
  have heZ := ((centerCongr e) ⟨_, hgZ⟩).property
  change e ⟨g, hCL hg⟩ ∈ center SL(2,K) at heZ
  rw [Theory.PSL2.sl2_center_eq_bot K] at heZ
  have he1 : e ⟨g, hCL hg⟩ = e 1 := (mem_bot.mp heZ).trans e.map_one.symm
  exact congrArg Subtype.val (e.injective he1)

omit [FiniteDimensional (ZMod 2) V] in
include h e in
/-- The sharp automorphism bound applies to the original ambient group. -/
theorem psl2_primeRank_le {r : ℕ} (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) :
    primeRank 2 G ≤ r := by
  let : L.Normal := h.layer_normal
  have hi := MulAut.conjNormal_injective_of_centralizer_eq_bot L (h.psl2_centralizer_eq_bot e)
  have hb := primeRank_le_of_injective 2 (MulAut.conjNormal : G →* MulAut L) hi
  rw [primeRank_equiv 2 (MulAut.congr e)] at hb
  exact hb.trans (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hr hc)

private theorem binary_outer_card_dvd {r : ℕ} (hc : Nat.card K = 2 ^ r) :
    Nat.card (MulAut.Outer (Theory.PSL2.Group K)) ∣ r := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Theory.PSL2.Group K))
  let f := q.comp (Theory.PSL2.fieldAutHom (K := K))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨g, σ, rfl⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage a
    refine ⟨σ, ?_⟩
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change q (Theory.PSL2.fieldAut σ) = q (MulAut.conj g * Theory.PSL2.fieldAut σ)
    rw [map_mul, hg, one_mul]
  exact (card_dvd_of_surjective f hf).trans
    (by rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hc])

omit [FiniteDimensional (ZMod 2) V] in
include h e in
/-- The order of the literal quotient G/L divides the defining field degree. -/
theorem psl2_index_dvd_degree {r : ℕ} (hc : Nat.card K = 2 ^ r) : L.index ∣ r := by
  let : L.Normal := h.layer_normal
  have hd := card_dvd_of_injective (MulAut.outerAction L)
    (MulAut.outerAction_injective L (h.psl2_centralizer_eq_bot e))
  have ho : Nat.card (MulAut.Outer L) ∣ r := by
    rw [Nat.card_congr (MulAut.outerCongr (e.trans (Theory.PSL2.sl2QuotientEquiv K))).toEquiv]
    exact binary_outer_card_dvd hc
  exact hd.trans ho

omit [FiniteDimensional (ZMod 2) V] in
include h e in
/-- Odd defining degree forces every actual two-subgroup into the layer. -/
theorem psl2_twoSubgroup_le_of_odd {r : ℕ} (hc : Nat.card K = 2 ^ r)
    (hr : Odd r) {A : Subgroup G} (hA : IsPGroup 2 A) : A ≤ L := by
  let : L.Normal := h.layer_normal
  have hi : Nat.Coprime 2 L.index := (hr.of_dvd_nat (h.psl2_index_dvd_degree e hc)).coprime_two_left
  intro a ha
  obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
  exact primeToResidual_le L hi (mem_primeToResidual_of_pow (congrArg Subtype.val hn))

omit [FiniteDimensional (ZMod 2) V] in
include h e in
/-- Cubic ratio two supplies a small actor in the actual ambient group. -/
theorem psl2_cubic_actor {r : ℕ} (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      fixedCodim ρ A ≤ 2 * rank A ∧ rank A ≤ r := by
  obtain ⟨A, hA, hC, hD⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  exact ⟨A, hA, hC, hD, hA.rank_le_of_primeRank_le (h.psl2_primeRank_le e hr hc)⟩

omit [FiniteDimensional (ZMod 2) V] in
include h e in
/-- At odd degree the source bound is inherited by the literal layer action. -/
theorem psl2_restricted_cubicRatio_le_two_of_odd {r : ℕ}
    (hc : Nat.card K = 2 ^ r) (hr : Odd r) : cubicRatio (ρ.comp L.subtype) ≤ 2 := by
  obtain ⟨A, hA, hC, hD⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.smallCubic
  let : IsElementaryAbelian 2 A := hA.2
  have hAL := h.psl2_twoSubgroup_le_of_odd e hc hr (IsElementaryAbelian.isPGroup 2 A)
  apply (cubicRatio_le_nat_iff _ 2).mpr
  refine ⟨A.subgroupOf L, ⟨?_, IsElementaryAbelian.subgroupOf hAL⟩, ?_, ?_⟩
  · intro hz
    apply hA.1
    rw [← map_subgroupOf_eq_of_le hAL, hz, Subgroup.map_bot]
  · intro a ha b hb c hc' v
    exact hC a ha b hb c hc' v
  · rwa [fixedCodim_subgroupOf ρ hAL, rank_subgroupOf hAL]

omit [FiniteDimensional (ZMod 2) V] in
include h e in
/-- At odd degree the same bound reaches the literal matrix representation. -/
theorem psl2_matrix_cubicRatio_le_two_of_odd {r : ℕ}
    (hc : Nat.card K = 2 ^ r) (hr : Odd r) :
    cubicRatio ((ρ.comp L.subtype).comp e.symm.toMonoidHom) ≤ 2 := by
  obtain ⟨A, hA, hC, hD⟩ := (cubicRatio_le_nat_iff _ 2).mp
    (h.psl2_restricted_cubicRatio_le_two_of_odd e hc hr)
  let B := A.map e.toMonoidHom
  have he : B.map e.symm.toMonoidHom = A := by
    rw [map_map]
    simp
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hz
    exact hA.1 (by rw [← he, hz, Subgroup.map_bot])
  have hR : rank B = rank A := by
    rw [← rank_map_injective e.symm.toMonoidHom e.symm.injective, he]
  apply (cubicRatio_le_nat_iff _ 2).mpr
  refine ⟨B, hB, ?_, ?_⟩
  · intro a ha b hb c hc' v
    exact hC (e.symm a) (he ▸ mem_map_of_mem _ ha)
      (e.symm b) (he ▸ mem_map_of_mem _ hb)
      (e.symm c) (he ▸ mem_map_of_mem _ hc') v
  · have hF : fixedCodim ((ρ.comp L.subtype).comp e.symm.toMonoidHom) B =
        fixedCodim (ρ.comp L.subtype) A := by
      unfold fixedCodim
      rw [fixedSpace_comp_map, he]
    rwa [hF, hR]

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
