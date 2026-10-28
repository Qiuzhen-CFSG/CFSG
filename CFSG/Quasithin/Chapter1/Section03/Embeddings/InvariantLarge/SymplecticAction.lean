module

public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSubgroups
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterOrder
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.GroupTheory.SylowNormalizerOuterAction
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements

/-!
# Symplectic Cartan restrictions in the invariant Ξ case

Let L be a self-centralizing normal subgroup of a finite group, identified
with the actual Sp₄(F), and let S be an ambient Sylow 2-subgroup. The
A.3.15(5) Cartan containment supplies B ≤ N_L(S ∩ L). The theorems below
use precisely that normalization consequence and B ≤ L, with no abstract
group-family tags or assumed abelianness.

The odd B embeds through Borel characters in Fˣ × Fˣ. This proves
abelianness and the split-field congruence. The actual normalizer action
factors through the outer quotient because its kernel centralizes B.
Under the explicit diagram-preserving semilinear classification, the
exceptional graph automorphism generates the outer group, whose order
divides 2n. Thus the actual automizer is cyclic. The local identity
B = [B, Φ(N_S(B))] then forces n even.
Only nontriviality and that commutator identity are needed for parity;
the source supplies both through its local Ξ input.

The semilinear classification remains the sole model-classification
parameter. Its proof and the transport from the original local Ξ setup
belong to the source theorem's assembly owner.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, A.3.15(5), printed pp.50--51,
and Proposition 1.3.4(3) and its proof, printed pp.509--511 (PDF pp.526--528).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SymplecticAction
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- Transfer the actual Cartan-normalizer configuration into the matrix model. -/
theorem cartan_embedding {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hBL : B ≤ L)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B) :
    ∃ f : B →* Fˣ × Fˣ, Function.Injective f := by
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal L
  let V := U.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let C := (B.subgroupOf L).map e.symm.toMonoidHom
  have hCn : C ≤ normalizer (V : Set (Sp F)) := by
    have hb : B.subgroupOf L ≤ normalizer ((S : Subgroup G).subgroupOf L) := by
      rw [← inf_subgroupOf_right (S : Subgroup G) L,
        ← subgroupOf_normalizer_eq (show (S : Subgroup G) ⊓ L ≤ L from inf_le_right)]
      exact subgroupOf_mono L hBn
    change C ≤ normalizer (((U : Subgroup L).map e.symm.toMonoidHom) : Set (Sp F))
    rw [← hU] at hb
    exact (map_mono hb).trans (fun _ hx => (U : Subgroup L).le_normalizer_map e.symm.toMonoidHom hx)
  have hi : IsPGroup p (B.subgroupOf L) := hP.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨f, hf⟩ := odd_sylow_normalizer_embedding hF hn V hCn hp (hi.map e.symm.toMonoidHom)
  let j : B ≃* C := (subgroupOfEquivOfLe hBL).symm.trans (e.symm.subgroupMap (B.subgroupOf L))
  exact ⟨f.comp j.toMonoidHom, hf.comp j.injective⟩


theorem cartan_abelian_card {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hBL : B ≤ L)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B) :
    IsMulCommutative B ∧ Nat.card B ∣ (2^n - 1)^2 := by
  obtain ⟨f, hf⟩ := cartan_embedding hF hn L e S B hBL hBn hp hP
  refine ⟨IsMulCommutative.of_comm (fun a b => hf (by simp only [map_mul, mul_comm])), ?_⟩
  simpa only [Nat.card_prod, Nat.card_units, hF, pow_two] using card_dvd_of_injective f hf

theorem cartan_congruence {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hBL : B ≤ L)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B) (hne : B ≠ ⊥) : 2^n ≡ 1 [MOD p] := by
  have hd : p ∣ Nat.card B := hP.card_eq_or_dvd.resolve_left
    (fun h => hne (Subgroup.card_eq_one.mp h))
  have hpq : p ∣ 2^n - 1 := (Fact.out : p.Prime).dvd_of_dvd_pow
    (hd.trans (cartan_abelian_card hF hn L e S B hBL hBn hp hP).2)
  exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hpq).symm

omit [Finite G] in
/-- The kernel of the actual outer conjugation action of N_S(B) centralizes B. -/
theorem outer_kernel_centralizes {p : ℕ}
    (L : Subgroup G) [L.Normal] (S : Sylow 2 G) (B : Subgroup G)
    (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B)
    (s : ((S : Subgroup G) ⊓ normalizer B : Subgroup G))
    (hs : MulAut.outerAction L (normalizerQuotientMap L S B s) = 1) :
    (s : G) ∈ centralizer (B : Set G) := by
  have hq : normalizerQuotientMap L S B s = 1 :=
    MulAut.outerAction_injective L hC (hs.trans (map_one (MulAut.outerAction L)).symm)
  exact normalizerQuotientMap_kernel_centralizes L S B hBn
    (S.isPGroup'.to_inf_left.disjoint_of_coprime hP (Nat.coprime_two_left.mpr hp)) s hq

omit [Finite G] in
/-- The automorphisms of B induced by N_S(B) form a cyclic group.
The exceptional graph map supplies cyclicity of the actual outer group;
the kernel-centralization argument makes the action a quotient of a subgroup
of that cyclic group. -/
theorem automizer_isCyclic {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B) : IsCyclic (automizer S B) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsCyclic (MulAut.Outer (Sp F)) :=
    ExceptionalGraph.outer_isCyclic_of_card hF hn hclass
  let : IsCyclic (MulAut.Outer L) :=
    isCyclic_of_injective (MulAut.outerCongr e).symm.toMonoidHom
      (MulAut.outerCongr e).symm.injective
  let : IsCyclic (G ⧸ L) :=
    isCyclic_of_injective (MulAut.outerAction L) (MulAut.outerAction_injective L hC)
  exact normalizerAction_isCyclic_of_quotient L S B hBn
    (S.isPGroup'.to_inf_left.disjoint_of_coprime hP (Nat.coprime_two_left.mpr hp))

omit [Finite G] in
theorem automizer_card_dvd {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B) : Nat.card (automizer S B) ∣ 2*n := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2 = 2^1) (Nat.pow_lt_pow_right (by decide) hn)
  have hd := normalizerAction_card_dvd_outer L S B hC hBn
    (S.isPGroup'.to_inf_left.disjoint_of_coprime hP (Nat.coprime_two_left.mpr hp))
  have he := Nat.card_congr (MulAut.outerCongr e).toEquiv
  rw [← he] at hd
  exact hd.trans (card_outer_dvd_two_mul hF hq hclass)

theorem even_parameter {n p : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hp : Odd p) (hP : IsPGroup p B) (hne : B ≠ ⊥)
    (hcomm : B = ⁅B, (frattini ((S : Subgroup G) ⊓ normalizer B : Subgroup G)).map
      ((S : Subgroup G) ⊓ normalizer B).subtype⁆) : Even n := by
  apply normalizerAction_even_of_card_dvd_two_mul (S : Subgroup G) B S.isPGroup' hne hcomm
  exact automizer_card_dvd hF hn hclass L e S B hC hBn hp hP


/-- The abelian and numerical clauses used in the p > 3 symplectic branch.
The precise semilinear classification remains an explicit input; cyclicity
of the automizer is not asserted by this theorem. -/
theorem abelian_and_parameter_restrictions {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hn : 1 < n) (hp : 3 < p)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hBL : B ≤ L) (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hP : IsPGroup p B) (hne : B ≠ ⊥)
    (hcomm : B = ⁅B, (frattini ((S : Subgroup G) ⊓ normalizer B : Subgroup G)).map
      ((S : Subgroup G) ⊓ normalizer B).subtype⁆) :
    IsMulCommutative B ∧ 2^n ≡ 1 [MOD p] ∧ Even n := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  exact ⟨(cartan_abelian_card hF hn.le L e S B hBL hBn ho hP).1,
    cartan_congruence hF hn.le L e S B hBL hBn ho hP hne,
    even_parameter hF hn hclass L e S B hC hBn ho hP hne hcomm⟩

/-- All Cartan action and parameter restrictions needed in the p > 3
symplectic branch of Proposition 1.3.4(3). The explicit semilinear coverage
premise is the only remaining model-classification input. Nontriviality
and the Frattini commutator identity supplied by Ξ suffice for parity. -/
theorem abelian_cyclic_and_parameter_restrictions {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hn : 1 < n) (hp : 3 < p)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L) (S : Sylow 2 G)
    (B : Subgroup G) (hBL : B ≤ L) (hC : centralizer (L : Set G) = ⊥)
    (hBn : B ≤ normalizer ((S : Subgroup G) ⊓ L : Subgroup G))
    (hP : IsPGroup p B) (hne : B ≠ ⊥)
    (hcomm : B = ⁅B, (frattini ((S : Subgroup G) ⊓ normalizer B : Subgroup G)).map
      ((S : Subgroup G) ⊓ normalizer B).subtype⁆) :
    IsMulCommutative B ∧ IsCyclic (automizer S B) ∧ 2^n ≡ 1 [MOD p] ∧ Even n := by
  obtain ⟨ha, hq, hn'⟩ := abelian_and_parameter_restrictions hF hn hp hclass
    L e S B hBL hC hBn hP hne hcomm
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  exact ⟨ha, automizer_isCyclic hF hn hclass L e S B hC hBn ho hP, hq, hn'⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SymplecticAction
