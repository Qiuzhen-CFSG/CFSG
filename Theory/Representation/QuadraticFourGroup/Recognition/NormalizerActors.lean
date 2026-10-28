module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSpectrum
public import Theory.GroupAction.InvolutoryOddDisplacement
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Faithful elementary normalizer actors on binary PSL₂ covers

The actual conjugation action of N_C(L) has trivial kernel when C_C(L)=1.
The proved automorphism bound for a perfect cover of PSL₂(2ⁿ) gives
|N_C(L)|≤2ⁿ. If the C-orbit of L is contained in {L,Lᵃ}, the actual
normalizer index divides two, giving |C|≤2ⁿ⁺¹ and the corresponding ranks.

A nonidentity normalizing involution induces a nonidentity automorphism on
the marked central quotient. The involution-or-odd spectrum supplies an
odd nonidentity displacement. Lifting it through the literal quotient map
produces a commutator in L; the final theorem places it in the first factor
of the supplied TwoFactorModel with the original ambient commutator identity.

These discharge the group inputs to GLS2, Chapter G, Theorem 26.24, Step 5
and its final module argument (following the recognition in Theorem 25.14).
-/

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup.NormalizerActors
variable {G : Type*} [Group G] (C L : Subgroup G)

@[expose] public def action : (normalizer (L : Set G)).subgroupOf C →* MulAut L :=
  L.normalizerMonoidHom.comp {
    toFun c := ⟨((c : C) : G), c.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

public theorem action_injective (hc : C ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective (action C L) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply eq_bot_iff.mpr
  intro c he
  change c = 1
  have hz : ((c : C) : G) ∈ centralizer (L : Set G) := by
    have hm : (⟨((c : C) : G), c.property⟩ : normalizer (L : Set G)) ∈
        L.normalizerMonoidHom.ker := he
    rwa [L.normalizerMonoidHom_ker] at hm
  have heq : ((c : C) : G) = 1 := by
    exact mem_bot.mp (hc ▸ (show ((c : C) : G) ∈ C ⊓ centralizer (L : Set G) from
      ⟨(c : C).property, hz⟩))
  exact Subtype.ext (Subtype.ext heq)

public theorem normalizer_card_le [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card ((normalizer (L : Set G)).subgroupOf C) ≤ 2 ^ n := by
  let N := (normalizer (L : Set G)).subgroupOf C
  let : IsElementaryAbelian 2 N := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 C) (x:C)) }
  exact Theory.PSL2.elementary_action_card_le hn e (action C L) (action_injective C L hc)

private theorem map_conj_mul (a b : G) :
    L.map (MulAut.conj (a*b)).toMonoidHom =
      (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

public theorem normalizer_index_dvd_two (a : C)
    (horbit : ∀ c : C, L.map (MulAut.conj (c:G)).toMonoidHom = L ∨
      L.map (MulAut.conj (c:G)).toMonoidHom = L.map (MulAut.conj (a:G)).toMonoidHom) :
    ((normalizer (L : Set G)).subgroupOf C).index ∣ 2 := by
  apply index_dvd_two_iff'.mpr
  refine ⟨a⁻¹, fun c => ?_⟩
  rcases horbit c with h | h
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr h)
  · apply Or.inl
    apply mem_normalizer_iff_map_conj_eq.mpr
    change L.map (MulAut.conj ((a:G)⁻¹ * (c:G))).toMonoidHom = L
    rw [map_conj_mul, h, ← map_conj_mul, inv_mul_cancel, map_one]
    exact L.map_id

public theorem card_le_of_pair_orbit [Finite G] [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) (a : C)
    (horbit : ∀ c : C, L.map (MulAut.conj (c:G)).toMonoidHom = L ∨
      L.map (MulAut.conj (c:G)).toMonoidHom = L.map (MulAut.conj (a:G)).toMonoidHom) :
    Nat.card C ≤ 2 ^ (n+1) := by
  let N := (normalizer (L : Set G)).subgroupOf C
  have hi : N.index ≤ 2 := Nat.le_of_dvd (by decide) (normalizer_index_dvd_two C L a horbit)
  have hb := normalizer_card_le C L hn e hc
  calc
    Nat.card C = Nat.card N * N.index := N.card_mul_index.symm
    _ ≤ 2 ^ n * 2 := Nat.mul_le_mul hb hi
    _ = 2 ^ (n+1) := (pow_succ 2 n).symm

public theorem rank_le_of_pair_orbit [Finite G] [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) (a : C)
    (horbit : ∀ c : C, L.map (MulAut.conj (c:G)).toMonoidHom = L ∨
      L.map (MulAut.conj (c:G)).toMonoidHom = L.map (MulAut.conj (a:G)).toMonoidHom) :
    Group.rank C ≤ n+1 :=
  IsElementaryAbelian.rank_le_of_card_le C (card_le_of_pair_orbit C L hn e hc a horbit)


public theorem primeRank_le_of_pair_orbit [Finite G] [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) (a : C)
    (horbit : ∀ c : C, L.map (MulAut.conj (c:G)).toMonoidHom = L ∨
      L.map (MulAut.conj (c:G)).toMonoidHom = L.map (MulAut.conj (a:G)).toMonoidHom) :
    primeRank 2 C ≤ n+1 :=
  IsElementaryAbelian.primeRank_le_of_card_le C (card_le_of_pair_orbit C L hn e hc a horbit)

public theorem card_le_of_normalizes [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) (hN : C ≤ normalizer (L : Set G)) :
    Nat.card C ≤ 2 ^ n := by
  have hb := normalizer_card_le C L hn e hc
  have he : (normalizer (L : Set G)).subgroupOf C = ⊤ := by
    ext x
    simp only [mem_subgroupOf, mem_top, iff_true]
    exact hN x.property
  rw [he, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).toEquiv] at hb
  exact hb

public theorem rank_le_of_normalizes [Finite G] [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) (hN : C ≤ normalizer (L : Set G)) :
    Group.rank C ≤ n :=
  IsElementaryAbelian.rank_le_of_card_le C (card_le_of_normalizes C L hn e hc hN)

public theorem primeRank_le_of_normalizes [Finite G] [Group.IsPerfect L] [IsElementaryAbelian 2 C]
    {n : ℕ} (hn : 2 ≤ n) (e : L ⧸ center L ≃* Factor n)
    (hc : C ⊓ centralizer (L : Set G) = ⊥) (hN : C ≤ normalizer (L : Set G)) :
    primeRank 2 C ≤ n :=
  IsElementaryAbelian.primeRank_le_of_card_le C (card_le_of_normalizes C L hn e hc hN)

public theorem odd_commutator [IsQuasisimple L] [IsElementaryAbelian 2 C]
    {n : ℕ} (f : L →* Factor n) (hf : Function.Surjective f)
    (hk : f.ker = center L) (hc : C ⊓ centralizer (L : Set G) = ⊥)
    (c : G) (hcC : c ∈ C) (hcN : c ∈ normalizer (L : Set G)) (hne : c ≠ 1) :
    ∃ l d : L, (d:G) = c * (l:G) * c⁻¹ * (l:G)⁻¹ ∧
      Odd (orderOf (f d)) ∧ f d ≠ 1 := by
  let e : L ⧸ center L ≃* Factor n :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (l : L) : e (QuotientGroup.mk' (center L) l) = f l := rfl
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (Factor n) := e.symm.isSimpleGroup
  let : Group.IsPerfect (Factor n) := Group.IsPerfect.ofSurjective hf
  let cN : (normalizer (L : Set G)).subgroupOf C := ⟨⟨c,hcC⟩,hcN⟩
  let α := action C L cN
  have hα : α ^ 2 = 1 := by
    change action C L cN ^ 2 = 1
    rw [← map_pow]
    have hc2 : cN ^ 2 = 1 := Subtype.ext (Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian c hcC))
    rw [hc2, map_one]
  have hαne : α ≠ 1 := by
    intro hh
    have hh' : cN = 1 := action_injective C L hc (hh.trans (map_one _).symm)
    exact hne (congrArg (fun x : (normalizer (L : Set G)).subgroupOf C => ((x:C):G)) hh')
  let β := MulAut.centralQuotientAction e α
  have hβ : β ^ 2 = 1 := by
    change MulAut.centralQuotientAction e α ^ 2 = 1
    rw [← map_pow,hα,map_one]
  have hβne : β ≠ 1 := fun hh => hαne
    (MulAut.centralQuotientAction_injective e (hh.trans (map_one _).symm))
  obtain ⟨y,hy,hyne⟩ := exists_odd_displacement_of_involutory_automorphism
    (factor_involutionOddSpectrum n) β hβ hβne
  obtain ⟨l,rfl⟩ := hf y
  have hβf : β (f l) = f (α l) := by
    simpa only [he] using MulAut.centralQuotientAction_apply e α l
  refine ⟨l, α l * l⁻¹, rfl, ?_, ?_⟩
  · simpa only [map_mul,map_inv,← hβf] using hy
  · simpa only [map_mul,map_inv,← hβf] using hyne

public theorem twoFactor_odd_commutator [IsQuasisimple L] [IsElementaryAbelian 2 C]
    {E : Subgroup G} (hLE : L ≤ E) (M : TwoFactorModel E)
    (f : L →* Factor M.n) (hf : Function.Surjective f)
    (hk : f.ker = center L)
    (hmark : ∀ l : L, M.projection (Subgroup.inclusion hLE l) = (f l,1))
    (hc : C ⊓ centralizer (L : Set G) = ⊥)
    (c : G) (hcC : c ∈ C) (hcN : c ∈ normalizer (L : Set G)) (hne : c ≠ 1) :
    ∃ (l : L) (x : E) (g : Factor M.n), M.projection x = (g,1) ∧
      Odd (orderOf g) ∧ g ≠ 1 ∧ (x:G) = c * (l:G) * c⁻¹ * (l:G)⁻¹ := by
  obtain ⟨l,d,hd,ho,hn⟩ := odd_commutator C L f hf hk hc c hcC hcN hne
  exact ⟨l, Subgroup.inclusion hLE d, f d, hmark d, ho, hn, hd⟩

end Representation.QuadraticFourGroup.NormalizerActors
