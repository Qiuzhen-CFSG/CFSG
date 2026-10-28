module
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Injective
public import Mathlib.Data.Finite.Perm
public import Theory.GroupTheory.PrimeRankHom

/-!
# Two-rank for two permuted supports

For a faithful action on two spanning supports whose individual stabilizer
images have two-rank at most one, every elementary binary subgroup has
order at most four. A subgroup fixing both supports embeds into the two
rank-one images. If it exchanges them, its index-two kernel acts faithfully
on one support because its elements commute with the exchange.

Source application: Aschbacher–Smith 15.1.7(6) and15.1.13, p.1091.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation
variable {G V I : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite I]

omit [Finite I] in
private theorem perm_pair_fixed_iff_one (i j : I) (hij : i ≠ j)
    (hall : ∀ k, k = i ∨ k = j) (p : Equiv.Perm I) : p i = i ↔ p = 1 := by
  refine ⟨?_,fun h => h ▸ rfl⟩
  intro hi
  have hj : p j = j := by
    rcases hall (p j) with h | h
    · exact False.elim (hij (p.injective (hi.trans h.symm)))
    · exact h
  ext k
  rcases hall k with rfl | rfl
  · exact hi
  · exact hj

private theorem elementary_card_le_two_of_injective
    {E H : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    [Group H] [Finite H] (f : E →* H) (hf : Function.Injective f)
    (hH : primeRank 2 H ≤ 1) : Nat.card E ≤ 2 := by
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hh := (primeRank_le_iff_elementary_card_le H).mp hH f.range inferInstance
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hh
  exact hh

/-- Two permuted complementary supports, each with image two-rank at most one,
give ambient two-rank at most two. An elementary subgroup exchanging the
supports has a kernel that acts faithfully on either one. -/
theorem twoRank_le_two_of_permuted_pair
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (W : I → Submodule (ZMod 2) V) (i j : I) (hij : i ≠ j)
    (hall : ∀ k, k = i ∨ k = j) (hfull : W i ⊔ W j = ⊤)
    (π : G →* Equiv.Perm I)
    (hp : ∀ g k, (W k).map (ρ g) = W (π g k))
    (hr : ∀ k, primeRank 2 (subspaceActionImage ρ (W k)) ≤ 1) :
    primeRank 2 G ≤ 2 := by
  classical
  have hI : Nat.card I = 2 := by
    refine Nat.card_eq_two_iff.mpr ⟨i,j,hij,?_⟩
    exact Set.eq_univ_iff_forall.mpr (fun k => by simpa using hall k)
  have hstable (g : G) (hg : π g = 1) (k : I) : g ∈ subspaceStabilizer ρ (W k) := by
    apply (subspace_map_eq_iff ρ _ g).mp
    rw [hp,hg]
    rfl
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro A hA
  let := hA
  let f : A →* Equiv.Perm I := π.comp A.subtype
  by_cases htriv : ∀ a : A, f a = 1
  · let q (k : I) : A →* subspaceActionImage ρ (W k) :=
      (subspaceActionHom ρ (W k)).comp
        (A.subtype.codRestrict _ (fun a => hstable a (htriv a) k))
    let q' : A →* ((q i).range × (q j).range) :=
      (q i).rangeRestrict.prod (q j).rangeRestrict
    have hq : Function.Injective q' := by
      intro a b hab
      apply Subtype.ext
      apply hf
      have he (k : I) (hk : q k a = q k b) :
          W k ≤ LinearMap.eqLocus (ρ a) (ρ b) := by
        intro v hv
        exact congrArg (fun g => (subspaceImageRepresentation ρ (W k) g ⟨v,hv⟩ : V)) hk
      have ht : (⊤ : Submodule (ZMod 2) V) ≤ LinearMap.eqLocus (ρ a) (ρ b) := by
        rw [←hfull]
        exact sup_le (he i (congrArg (fun z => (z.1 : subspaceActionImage ρ (W i))) hab))
          (he j (congrArg (fun z => (z.2 : subspaceActionImage ρ (W j))) hab))
      ext v
      exact ht Submodule.mem_top
    have hb (k : I) : Nat.card (q k).range ≤ 2 := by
      let : IsElementaryAbelian 2 (q k).range :=
        IsElementaryAbelian.of_surjective (q k).rangeRestrict (q k).rangeRestrict_surjective
      exact (primeRank_le_iff_elementary_card_le _).mp (hr k) _ inferInstance
    have hh := Nat.card_le_card_of_injective q' hq
    rw [Nat.card_prod] at hh
    exact hh.trans (Nat.mul_le_mul (hb i) (hb j))
  · push Not at htriv
    obtain ⟨a,ha⟩ := htriv
    have hai : π (a : G) i = j := by
      rcases hall (π (a : G) i) with h | h
      · exact False.elim (ha ((perm_pair_fixed_iff_one i j hij hall _).mp h))
      · exact h
    let N := f.ker
    let : IsElementaryAbelian 2 N := IsElementaryAbelian.of_injective N.subtype N.subtype_injective
    let g : N →* G := A.subtype.comp N.subtype
    let q : N →* subspaceActionImage ρ (W i) :=
      (subspaceActionHom ρ (W i)).comp
        (g.codRestrict _ (fun n => hstable (g n) n.property i))
    have hq : Function.Injective q := by
      intro b c hbc
      have he : W i ≤ LinearMap.eqLocus (ρ (g b)) (ρ (g c)) := by
        intro v hv
        exact congrArg (fun z => (subspaceImageRepresentation ρ (W i) z ⟨v,hv⟩ : V)) hbc
      have hcomm (n : N) (v : V) :
          ρ (g n) (ρ (a : G) v) = ρ (a : G) (ρ (g n) v) := by
        rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
        exact congrArg (fun x => ρ x v) (congrArg A.subtype (mul_comm (n : A) a))
      have hj : W j ≤ LinearMap.eqLocus (ρ (g b)) (ρ (g c)) := by
        intro w hw
        rw [←hai,←hp] at hw
        obtain ⟨v,hv,rfl⟩ := hw
        change ρ (g b) (ρ (a : G) v) = ρ (g c) (ρ (a : G) v)
        rw [hcomm,hcomm,show ρ (g b) v = ρ (g c) v from he hv]
      have ht : (⊤ : Submodule (ZMod 2) V) ≤ LinearMap.eqLocus (ρ (g b)) (ρ (g c)) := by
        rw [←hfull]
        exact sup_le he hj
      apply Subtype.ext
      apply Subtype.ext
      apply hf
      ext v
      exact ht Submodule.mem_top
    have hN : Nat.card N ≤ 2 := elementary_card_le_two_of_injective q hq (hr i)
    have hqcard : Nat.card f.range ≤ 2 := by
      have hh := f.range.card_le_card_group
      rw [Nat.card_perm,hI] at hh
      exact hh
    have hcount := f.ker.card_mul_index
    rw [index_ker] at hcount
    change Nat.card N * Nat.card f.range = Nat.card A at hcount
    rw [←hcount]
    exact Nat.mul_le_mul hN hqcard
end Representation
