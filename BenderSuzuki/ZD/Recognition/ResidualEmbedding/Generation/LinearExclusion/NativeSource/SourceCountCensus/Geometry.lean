module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceCount.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Geometry for the original Section 15 involution census

The literal subgroup AU has order q|U| and exponent two. The supplied
normalizer order q²|U| therefore gives an element outside AU. Its trivial
centralizer in the nontrivial U supplies an element with nontrivial square.
All conjugation and normality remain relative to the original M.

Source: GLS4, Chapter 2, Lemma 15.6, lines 2718–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
open Subgroup Theory.GroupTheory
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "A" => closure (Z ∩ (M : Set G))
local notation "U" => twoCore M z t
local notation "R" => sourceNormalizer Z M z t
local notation "K" => residualCommutator M t
include d

public theorem distinguished_square {a : G} (ha : a ∈ A) : a ^ 2 = 1 := by
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  exact elemPow_eq_one_of_isElementaryAbelian a ha

public theorem twoCore_square (hs : CentralizerLocalTwoData d)
    {a : G} (ha : a ∈ U) : a ^ 2 = 1 := by
  let : IsElementaryAbelian 2 U := hs.twoCore_elementary
  exact elemPow_eq_one_of_isElementaryAbelian a ha

public theorem twoCore_le_pair : U ≤ residualPairStabilizer M t :=
  (map_subtype_le _).trans
    (centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M)

public theorem distinguished_disjoint_twoCore : Disjoint A U := by
  apply disjoint_def.mpr
  intro a ha hu
  by_contra hne
  have hz := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp ⟨hne, distinguished_square d ha⟩
  exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected
    d.t_not_mem_M (twoCore_le_pair d hu) hz

public theorem distinguished_conj_mem {m a : G} (hm : m ∈ M) (ha : a ∈ A) :
    MulAut.conj m a ∈ A := by
  have hn : m ∈ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
    exact hm
  exact (mem_normalizer_iff.mp hn a).mp ha

public theorem source_conj_mem (hg : NormalizerData d)
    {m x : G} (hm : m ∈ M) (hx : x ∈ R) : MulAut.conj m x ∈ R := by
  exact hg.relative_normal.conj_mem ⟨x, sourceNormalizer_le_point hx⟩ hx ⟨m, hm⟩

public theorem torus_le_point : K ≤ M := by
  rw [d.torus_structure.1]
  exact inf_le_left.trans inf_le_left

public theorem distinguished_commutes {x a : G} (hx : x ∈ R) (ha : a ∈ A) :
    Commute a x := mem_centralizer_iff.mp (sourceNormalizer_centralizes_distinguished d hx) a ha

public theorem sup_square (hs : CentralizerLocalTwoData d)
    {x : G} (hx : x ∈ A ⊔ U) : x ^ 2 = 1 := by
  have hn : U ≤ normalizer (A : Set G) :=
    (show U ≤ R from le_sup_right.trans (sup_le_sourceNormalizer d hs)).trans
      ((sourceNormalizer_centralizes_distinguished d).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨a, ha, u, hu, rfl⟩ :=
    (Set.ext_iff.mp (coe_mul_of_right_le_normalizer_left A U hn) x).mp hx
  rw [(distinguished_commutes d ((sup_le_sourceNormalizer d hs) ((show U ≤ A ⊔ U from le_sup_right) hu)) ha).mul_pow,
    distinguished_square d ha, twoCore_square d hs hu, one_mul]

public theorem sup_card (hs : CentralizerLocalTwoData d) :
    Nat.card (A ⊔ U : Subgroup G) = 2 ^ n * Nat.card U := by
  have hn : U ≤ normalizer (A : Set G) :=
    (show U ≤ R from le_sup_right.trans (sup_le_sourceNormalizer d hs)).trans
      ((sourceNormalizer_centralizes_distinguished d).trans (Subgroup.centralizer_le_normalizer _))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A U hn
    (distinguished_disjoint_twoCore d), d.distinguished_elementary_card.2]

public theorem exists_nonsquare (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    ∃ x ∈ R, x ^ 2 ≠ 1 := by
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by have := d.parameter; omega) (by decide)
  have hlt : Nat.card (A ⊔ U : Subgroup G) < Nat.card R := by
    rw [sup_card d hs, hg.card]
    exact Nat.mul_lt_mul_of_pos_right (by nlinarith) Nat.card_pos
  have hnle : ¬ R ≤ A ⊔ U := fun hle => (not_lt_of_ge (card_le_of_le hle)) hlt
  obtain ⟨x, hx, hxAU⟩ := Set.not_subset.mp hnle
  obtain ⟨u, hu⟩ := ne_bot_iff_exists_ne_one.mp (twoCore_ne_bot d hs)
  have hu1 : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  by_cases hx2 : x ^ 2 = 1
  · refine ⟨u * x, (R).mul_mem ((sup_le_sourceNormalizer d hs) ((show U ≤ A ⊔ U from le_sup_right) u.property)) hx, ?_⟩
    intro hux
    have hui : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using twoCore_square d hs u.property)
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
    have huxi : ((u : G) * x)⁻¹ = (u : G) * x :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hux)
    have hc : Commute (u : G) x := by
      rw [mul_inv_rev, hui, hxi] at huxi
      exact huxi.symm
    have hb : (u : G) ∈ (⊥ : Subgroup G) :=
      twoCore_centralizer_outside_sup d hs hx hxAU ▸
        (show (u : G) ∈ U ⊓ centralizer ({x} : Set G) from
          ⟨u.property, mem_centralizer_singleton_iff.mpr hc.eq⟩)
    exact hu1 hb
  · exact ⟨x, hx, hx2⟩

end BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
