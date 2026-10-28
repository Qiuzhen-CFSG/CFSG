module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum

/-!
# The centralizer of an A₅ join of cubic subgroups

Suppose A and B have order three, generate A₅, and their simultaneous
normalizer has order twenty. Its Sylow five-subgroup E is unique, so the
whole pair normalizer normalizes E. Since a group of order five acts trivially
on a group of order three, E centralizes the join A ⊔ B.

If every five-normalizer is D₁₀ × A₅ or D₁₀ × D₁₀, the latter alternative
is excluded by the cubic subgroup. In the former, the A₅ join has trivial
projection to D₁₀ and fills the A₅ factor. Its whole ambient centralizer lies
in the pair normalizer, hence in N(E), and is exactly the D₁₀ factor.

This supplies an actual multiplicative equivalence, without recognition from
order alone. Source application: Aschbacher, *Sporadic Groups* (1994), 47.2
and the final paragraph of 47.6, printed pp.261 and 264. The five-normalizer
alternatives are explicit earlier-source inputs, not proved here.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.Alternating.CubicPairCentralizer
local notation "A5" => alternatingGroup (Fin 5)
local notation "D10" => DihedralGroup 5
private theorem to_dihedral_trivial (f : A5 →* D10) (x : A5) : f x = 1 := by
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
  · have h := Nat.card_le_card_of_injective f (f.ker_eq_bot_iff.mp hk)
    rw [nat_card_alternatingGroup, DihedralGroup.nat_card] at h
    norm_num [Nat.factorial] at h
  · exact show x ∈ f.ker from hk ▸ (mem_top x)

/-- An actual A₅ subgroup of D₁₀ × A₅ is the second factor. If the product
overgroup contains its whole ambient centralizer, that centralizer is D₁₀. -/
theorem centralizer_equiv_in_dihedral_product {G : Type*} [Group G]
    (A M : Subgroup G) (hAM : A ≤ M) (hCM : centralizer (A : Set G) ≤ M)
    (eA : A ≃* A5) (eM : M ≃* D10 × A5) :
    Nonempty (centralizer (A : Set G) ≃* D10) := by
  let a : A5 →* D10 × A5 :=
    eM.toMonoidHom.comp ((inclusion hAM).comp eA.symm.toMonoidHom)
  have ha : Function.Injective a :=
    eM.injective.comp ((inclusion_injective hAM).comp eA.symm.injective)
  let a₂ := (MonoidHom.snd D10 A5).comp a
  have ha₁ (x : A5) : (a x).1 = 1 :=
    to_dihedral_trivial ((MonoidHom.fst D10 A5).comp a) x
  have ha₂ : Function.Injective a₂ := by
    intro x y h
    exact ha (Prod.ext ((ha₁ x).trans (ha₁ y).symm) h)
  have hs : Function.Surjective a₂ := Finite.surjective_of_injective ha₂
  have hA₁ (z : A) : (eM (inclusion hAM z)).1 = 1 := by
    simpa only [a, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using ha₁ (eA z)
  have hf₂ (k : centralizer (A : Set G)) : (eM (inclusion hCM k)).2 = 1 := by
    have hz : (eM (inclusion hCM k)).2 ∈ center A5 := by
      apply mem_center_iff.mpr
      intro d
      obtain ⟨x, hx⟩ := hs d
      have hc : inclusion hAM (eA.symm x) * inclusion hCM k =
          inclusion hCM k * inclusion hAM (eA.symm x) := by
        apply Subtype.ext
        exact mem_centralizer_iff.mp k.property (eA.symm x) (eA.symm x).property
      have hh := congrArg (fun z : M => (eM z).2) hc
      simpa only [map_mul, Prod.snd_mul, show (eM (inclusion hAM (eA.symm x))).2 = d from hx]
        using hh
    rwa [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  let f : centralizer (A : Set G) →* D10 :=
    (MonoidHom.fst D10 A5).comp (eM.toMonoidHom.comp (inclusion hCM))
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro k l h
    apply inclusion_injective hCM
    apply eM.injective
    exact Prod.ext h ((hf₂ k).trans (hf₂ l).symm)
  · intro d
    let g : M := eM.symm (d, 1)
    have hg : (g : G) ∈ centralizer (A : Set G) := by
      apply mem_centralizer_iff.mpr
      intro z hz
      have hh : inclusion hAM ⟨z, hz⟩ * g = g * inclusion hAM ⟨z, hz⟩ := by
        apply eM.injective
        rw [map_mul, map_mul, show eM g = (d, 1) from eM.apply_symm_apply _]
        apply Prod.ext
        · simp only [Prod.fst_mul, hA₁, one_mul, mul_one]
        · simp only [Prod.snd_mul, one_mul, mul_one]
      exact congrArg Subtype.val hh
    refine ⟨⟨g, hg⟩, ?_⟩
    change (eM g).1 = d
    rw [show eM g = (d, 1) from eM.apply_symm_apply _]
private theorem five_centralizes_three {G : Type*} [Group G] [Finite G]
    (E A : Subgroup G) (hE : Nat.card E = 5) (hA : Nat.card A = 3)
    (hn : E ≤ normalizer (A : Set G)) : E ≤ centralizer (A : Set G) := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  let f : E →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  have hc : Nat.card (MulAut A) = 2 := by
    rw [IsCyclic.card_mulAut, hA]
    decide
  have h₅ : Nat.card f.range ∣ 5 := hE ▸ card_range_dvd f
  have h₂ : Nat.card f.range ∣ 2 := hc ▸ f.range.card_subgroup_dvd_card
  have hh : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes (by decide) h₅ h₂
  have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp (card_eq_one.mp hh)
  intro g hg
  have hk : inclusion hn ⟨g, hg⟩ ∈ A.normalizerMonoidHom.ker := by
    change f ⟨g, hg⟩ = 1
    rw [hf]
    rfl
  rwa [normalizerMonoidHom_ker] at hk

private theorem normal_five_of_card_twenty {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (hN : Nat.card N = 20) :
    ∃ E : Subgroup G, Nat.card E = 5 ∧ E ≤ N ∧ N ≤ normalizer (E : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 N := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hN]
    decide +kernel
  have hi : (P : Subgroup N).index = 4 := by
    have hh := (P : Subgroup N).card_mul_index
    rw [hP, hN] at hh
    omega
  have hcount : Nat.card (Sylow 5 N) = 1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hm := card_sylow_modEq_one 5 N
    change Nat.card (Sylow 5 N) % 5 = 1 % 5 at hm
    omega
  let : Subsingleton (Sylow 5 N) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (P : Subgroup N).Normal := P.normal_of_subsingleton
  refine ⟨(P : Subgroup N).map N.subtype, ?_, map_subtype_le _, ?_⟩
  · rw [card_map_of_injective N.subtype_injective, hP]
  · have hh := (P : Subgroup N).le_normalizer_map N.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh

/-- The normal five-subgroup of the order-twenty pair stabilizer identifies
the whole centralizer of an A₅ join through the actual five-local products. -/
theorem pair_centralizer_equiv {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hN : Nat.card (normalizer (A : Set G) ⊓ normalizer (B : Set G) : Subgroup G) = 20)
    (e : (A ⊔ B : Subgroup G) ≃* alternatingGroup (Fin 5))
    (h₅ : ∀ E : Subgroup G, Nat.card E = 5 →
      Nonempty (normalizer (E : Set G) ≃* DihedralGroup 5 × alternatingGroup (Fin 5)) ∨
      Nonempty (normalizer (E : Set G) ≃* DihedralGroup 5 × DihedralGroup 5)) :
    Nonempty (centralizer ((A ⊔ B : Subgroup G) : Set G) ≃* DihedralGroup 5) := by
  let N := normalizer (A : Set G) ⊓ normalizer (B : Set G)
  obtain ⟨E, hE, hEN, hNE⟩ := normal_five_of_card_twenty N hN
  have hEA : E ≤ centralizer (A : Set G) :=
    five_centralizes_three E A hE hA (hEN.trans inf_le_left)
  have hEB : E ≤ centralizer (B : Set G) :=
    five_centralizes_three E B hE hB (hEN.trans inf_le_right)
  have hJN : A ⊔ B ≤ normalizer (E : Set G) :=
    (sup_le (le_centralizer_iff.mp hEA) (le_centralizer_iff.mp hEB)).trans
      (centralizer_le_normalizer _)
  have hCN : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ N :=
    le_inf ((centralizer_le (show A ≤ A ⊔ B from le_sup_left)).trans
      (centralizer_le_normalizer _))
      ((centralizer_le (show B ≤ A ⊔ B from le_sup_right)).trans
        (centralizer_le_normalizer _))
  rcases h₅ E hE with h | h
  · exact centralizer_equiv_in_dihedral_product (A ⊔ B) (normalizer (E : Set G)) hJN
      (hCN.trans hNE) e h.some
  · have hd := card_dvd_of_le ((show A ≤ A ⊔ B from le_sup_left).trans hJN)
    rw [hA, Nat.card_congr h.some.toEquiv, Nat.card_prod, DihedralGroup.nat_card] at hd
    norm_num at hd
end Theory.SpecificGroups.Alternating.CubicPairCentralizer
