module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Partition

/-!
# The original involution and order-four census in Lemma 15.6

The source normalizer hypotheses imply the exact census before |U| is
known. Bijectivity of the torus family gives exactly one A-coset of
nonsquare elements in each nonidentity AU-coset. Multiplying a chosen
nonsquare x by any nonidentity element of U must therefore square to one.
The existing inversion argument now proves |U|=2, and the actual local
embedding identifies J with U. The square-one census also retains actual
M-conjugators for the subsequent Lemma 15.7.

The sole independent premises are the earlier two-core structure and
normalizer-growth data; no desired centralizer or normal-closure order is
assumed. Source: GLS4, Chapter 2, Lemma 15.6, lines 2718–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
open Census
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "A" => closure (Z ∩ (M : Set G))
local notation "U" => twoCore M z t
local notation "R" => sourceNormalizer Z M z t
local notation "K" => residualCommutator M t

/-- The source coset witness, obtained before the order of U is known. -/
public theorem source_coset_witness (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    ∃ x ∈ R, x ^ 2 ≠ 1 ∧ ∀ u ∈ U, u ≠ 1 → (u * x) ^ 2 = 1 := by
  obtain ⟨x,hx,hx2⟩ := exists_nonsquare d hs hg
  refine ⟨x,hx,hx2,?_⟩
  intro u hu hu1
  by_contra hux
  have huR : u ∈ R := (sup_le_sourceNormalizer d hs) ((show U ≤ A ⊔ U from le_sup_right) hu)
  have huxR : u * x ∈ R := (R).mul_mem huR hx
  obtain ⟨⟨k,a⟩, he⟩ := (nonsquareMap_bijective d hs hg hx hx2).surjective
    ⟨⟨u * x,huxR⟩,fun hh => hux (congrArg Subtype.val hh)⟩
  have he' : MulAut.conj (k : G) x * a = u * x :=
    congrArg (fun y : {y : R // y ^ 2 ≠ 1} => (y.val : G)) he
  have hk1 : (k : G) = 1 := by
    by_contra hk1
    apply hg.torus_free k k.property hk1 x hx (fun hh => hx2 (sup_square d hs hh))
    have hdisp : MulAut.conj (k : G) x * x⁻¹ = u * (a : G)⁻¹ := by
      have hh := congrArg (fun y : G => y * (a : G)⁻¹) he'
      simp only [mul_inv_cancel_right] at hh
      rw [hh]
      calc
        _ = u * (x * (a : G)⁻¹) * x⁻¹ := by group
        _ = u * ((a : G)⁻¹ * x) * x⁻¹ := by
          rw [(distinguished_commutes d hx a.property).inv_left.eq]
        _ = u * (a : G)⁻¹ := by group
    rw [hdisp]
    exact (A ⊔ U).mul_mem ((show U ≤ A ⊔ U from le_sup_right) hu)
      ((show A ≤ A ⊔ U from le_sup_left) ((A).inv_mem a.property))
  simp only [hk1, MulAut.conj_apply, one_mul, inv_one, mul_one] at he'
  have hua : u = (a : G) := by
    rw [← (distinguished_commutes d hx a.property).eq] at he'
    exact (mul_right_cancel he').symm
  exact hu1 (disjoint_def.mp (distinguished_disjoint_twoCore d) (hua.symm ▸ a.property) hu)

/-- Count all square-one elements of the original R₁, including identity. -/
public theorem source_square_one_card (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    Nat.card {x : R // x ^ 2 = 1} = (2 ^ n) ^ 2 * (Nat.card U - 1) + 2 ^ n :=
  (square_and_nonsquare_card d hs hg).1

/-- Every element of R₁ has fourth power one, so the nonsquares have order four. -/
public theorem source_order_four_iff (hg : NormalizerData d) (x : R) :
    orderOf x = 4 ↔ x ^ 2 ≠ 1 := by
  constructor
  · intro ho hs
    have hd := orderOf_dvd_of_pow_eq_one hs
    rw [ho] at hd
    norm_num at hd
  · intro hx
    have h4 : x ^ (2 ^ (1 + 1)) = 1 := by
      apply Subtype.ext
      change (x : G) ^ 4 = 1
      have hh := distinguished_square d (hg.square_mem x x.property)
      simpa only [← pow_mul] using hh
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa only [pow_one] using hx) h4

/-- The q(q−1) elements of order four in the literal source normalizer. -/
public theorem source_order_four_card (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    Nat.card {x : R // orderOf x = 4} = 2 ^ n * (2 ^ n - 1) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (source_order_four_iff d hg))]
  exact (square_and_nonsquare_card d hs hg).2

/-- Every square-one element outside A is a literal M-conjugate of an element of U#. -/
public theorem source_square_one_fusion (hs : CentralizerLocalTwoData d) (hg : NormalizerData d)
    {x : G} (hx : x ∈ R) (hx2 : x ^ 2 = 1) (hxA : x ∉ A) :
    ∃ m ∈ M, ∃ u ∈ U, u ≠ 1 ∧ MulAut.conj m u = x := by
  obtain ⟨a | p, he⟩ := (squareMap_bijective d hs hg).surjective
    ⟨⟨x,hx⟩,Subtype.ext hx2⟩
  · have hh : (a : G) = x := congrArg (fun y : {y : R // y ^ 2 = 1} => (y.val : G)) he
    exact (hxA (hh ▸ a.property)).elim
  · have hh : (p.2.val : G) = x := congrArg (fun y : {y : R // y ^ 2 = 1} => (y.val : G)) he
    obtain ⟨m, hm⟩ := p.1.property
    dsimp only at hm
    have hv : x ∈ (U).conjBy (m : G) := by
      rw [hm, ← hh]
      exact p.2.val.property
    obtain ⟨u, hu, hue⟩ := hv
    refine ⟨m,m.property,u,hu,?_,hue⟩
    intro hu1
    apply p.2.property
    apply Subtype.ext
    change (p.2.val : G) = 1
    exact hh.trans (by simpa only [hu1,map_one] using hue.symm)

/-- Apply the census to the source inversion theorem and the proved actual embedding. -/
public theorem source_centralizer_counts (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    Nat.card (centralizer (residualGenerated M z t : Set G)) = 2 ∧
      Nat.card (normalClosure (((centralizer (residualGenerated M z t : Set G)).subgroupOf M) : Set M)) =
        2 * (2 ^ n) ^ 2 := by
  obtain ⟨hm⟩ := d.centralizerLocalModelData
  exact counts_of_normalizer_and_census d hm hs hg (source_coset_witness d hs hg)

end BenderSuzuki.ZD.LinearExclusion.SourceCount
