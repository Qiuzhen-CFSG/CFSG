module
public import Theory.Representation.RankOne.QuadraticRecognition.TwoRankOne
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiAllActors
public import Theory.GroupTheory.SylowSmallIndexModels

/-!
# Quadratic square bounds for the small solvable rank-one actors

In D₁₀, the two-rank is one and a third reflection lies outside the
three-involution configuration. The transvection bound therefore gives
|A|² ≤ |V/C_V(A)|. The corresponding bound for the concrete Sz(2) is
already proved. Groups of orders ten and twenty with trivial two-core
are identified with those actual models. Divisor arithmetic extends the
result to every core-free subgroup of a group of order twenty.

Source: DGS, Groups and Graphs (1985), 6.4--6.5, pp.120--122, using
the quadratic bounds of 5.12, pp.113--115. D₁₀ is treated separately;
no new row is added to the Chapter 5 catalogue.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance finiteSmallSolvableQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

/-- The retained D10 model has the same quadratic square obstruction as Sz(2). -/
theorem dihedral_five_quadratic_square_bound
    (ρ : Representation (ZMod 2) (DihedralGroup 5) V) (hf : Function.Injective ρ)
    (A : Subgroup (DihedralGroup 5)) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  have hr : primeRank 2 (DihedralGroup 5) ≤ 1 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E hE
    let := hE
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := E)).exists_card_eq
    have hd : Nat.card E ∣ 2*5 := by simpa only [DihedralGroup.nat_card] using card_subgroup_dvd_card E
    have hc : (Nat.card E).Coprime 5 := by
      rw [hk]
      exact (by decide : Nat.Coprime 2 5).pow_left k
    have htwo : Nat.card E ∣ 2 := hc.dvd_mul_right.mp hd
    simpa using Nat.le_of_dvd (by decide : 0 < 2) htwo
  exact square_bound_of_two_rank_one hr (DihedralGroup.sr 0) (DihedralGroup.sr 1)
    (DihedralGroup.sr 3) (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) ρ hf A hq

omit [Finite V] in
private theorem fixedSpace_transport
    {G H : Type*} [Group G] [Group H]
    (ρ : Representation (ZMod 2) G V) (e : G ≃* H) (A : Subgroup G) :
    fixedSpace (ρ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) = fixedSpace ρ A := by
  rw [fixedSpace_comp_map,Subgroup.map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext a; simp
  rw [he,Subgroup.map_id]

omit [Finite V] in
private theorem quadratic_transport
    {G H : Type*} [Group G] [Group H]
    (ρ : Representation (ZMod 2) G V) (e : G ≃* H) (A : Subgroup G)
    (hq : IsQuadratic ρ A) : IsQuadratic (ρ.comp e.symm.toMonoidHom) (A.map e.toMonoidHom) := by
  rintro a ⟨b,hb,rfl⟩ c ⟨d,hd,rfl⟩ v
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hq b hb d hd v

/-- Faithful quadratic actors in either core-free group of order ten or twenty obey the square bound. -/
theorem ten_or_twenty_quadratic_square_bound {D : Type*} [Group D] [Finite D]
    (hcard : Nat.card D = 10 ∨ Nat.card D = 20) (hcore : pCore 2 D = ⊥)
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (A : Subgroup D) (hp : IsPGroup 2 A) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  rcases hcard with hc | hc
  · obtain ⟨e⟩ := Theory.GroupTheory.equiv_dihedral_of_card_ten hc hcore
    have hb := dihedral_five_quadratic_square_bound (ρ.comp e.symm.toMonoidHom)
      (hf.comp e.symm.injective) (A.map e.toMonoidHom) (quadratic_transport ρ e A hq)
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective,fixedSpace_transport ρ e A] using hb
  · obtain ⟨e⟩ := Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty hc hcore
    obtain ⟨S,hS⟩ := (hp.map e.toMonoidHom).exists_le_sylow
    have hb := suzukiZero_square_bound (ρ.comp e.symm.toMonoidHom)
      (hf.comp e.symm.injective) S (A.map e.toMonoidHom) hS (quadratic_transport ρ e A hq)
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective,fixedSpace_transport ρ e A] using hb
/-- The small solvable square bound applies to any actual core-free subgroup of order dividing twenty. -/
theorem card_dvd_twenty_quadratic_square_bound {D : Type*} [Group D] [Finite D]
    (hcard : Nat.card D ∣ 20) (hcore : pCore 2 D = ⊥)
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (A : Subgroup D) (hp : IsPGroup 2 A) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  have hcases : Nat.card D = 1 ∨ Nat.card D = 2 ∨ Nat.card D = 4 ∨
      Nat.card D = 5 ∨ Nat.card D = 10 ∨ Nat.card D = 20 := by
    have hh : Nat.card D ∈ Nat.divisors 20 := (Nat.mem_divisors).mpr ⟨hcard,by decide⟩
    have hd : Nat.divisors 20 = {1,2,4,5,10,20} := by decide +kernel
    rw [hd] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have trivial_of_pGroup (hD : IsPGroup 2 D) : Nat.card D = 1 := by
    have ht : (⊤ : Subgroup D) ≤ pCore 2 D :=
      le_sSup ⟨inferInstance,hD.of_equiv (topEquiv (G := D)).symm⟩
    have he : (⊤ : Subgroup D) = ⊥ := le_bot_iff.mp (hcore ▸ ht)
    have hh := congrArg (fun C : Subgroup D => Nat.card C) he
    simpa only [card_top,card_bot] using hh
  have odd_bound (ho : Odd (Nat.card D)) : Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
    have hAo : Odd (Nat.card A) := ho.of_dvd_nat (card_subgroup_dvd_card A)
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    have hAc : Nat.card A = 1 := by
      rw [hk] at hAo ⊢
      have he : k = 0 := by
        by_contra hn
        exact (Nat.not_even_iff_odd.mpr hAo) (even_two.pow_of_ne_zero hn)
      rw [he,pow_zero]
    rw [hAc,one_pow]
    exact Nat.card_pos
  rcases hcases with h1 | h2 | h4 | h5 | h10 | h20
  · exact odd_bound (h1 ▸ (by decide : Odd 1))
  · have hh := trivial_of_pGroup (IsPGroup.of_card (n := 1) h2)
    omega
  · have hh := trivial_of_pGroup (IsPGroup.of_card (n := 2) h4)
    omega
  · exact odd_bound (h5 ▸ (by decide : Odd 5))
  · exact ten_or_twenty_quadratic_square_bound (Or.inl h10) hcore ρ hf A hp hq
  · exact ten_or_twenty_quadratic_square_bound (Or.inr h20) hcore ρ hf A hp hq
end Representation.RankOne.QuadraticRecognition
