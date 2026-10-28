module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupAction.ElementaryNineSylowLine
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
/-!
# Four fixed spaces for an elementary nine-group

In a binary representation of an elementary group of order nine with no
common fixed vectors, the fixed spaces of its four cubic subgroups form
an internal direct sum. Coprime fixed-point generation gives spanning;
the cubic norm projectors kill the other three fixed spaces and prove
independence. Their dimensions consequently add to the original dimension.
This is the linear decomposition used in Aschbacher–Smith D.2.28–29.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped BigOperators IsMulCommutative
namespace Representation.ElementaryNineFixedDecomposition
variable {A V : Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) A V)

private theorem distinct_lines_generate (hA : Nat.card A = 9)
    (K L : Subgroup A) (hK : Nat.card K = 3) (hL : Nat.card L = 3) (hne : K ≠ L) :
    K ⊔ L = ⊤ := by
  have hd : Nat.card (K ⊓ L : Subgroup A) ∣ 3 := hK ▸ card_dvd_of_le inf_le_left
  have hb : K ⊓ L = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact card_eq_one.mp h1
    · have h₁ : K ⊓ L = K := eq_of_le_of_card_ge inf_le_left (by rw [hK,h3])
      have h₂ : K ⊓ L = L := eq_of_le_of_card_ge inf_le_right (by rw [hL,h3])
      exact (hne (h₁.symm.trans h₂)).elim
  have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes K L
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hK,hL,hb,card_bot,one_mul] at hm
  exact eq_top_of_card_eq _ (by rw [←hm,hA])

/-- The four cubic-line fixed spaces span every fixed-point-free binary
representation of an elementary group of order nine. -/
theorem iSup_fixed_eq_top (hA : Nat.card A = 9) (hfixed : fixedSpace ρ ⊤ = ⊥) :
    (⨆ K : {K : Subgroup A // Nat.card K = 3}, fixedSpace ρ K.val) = ⊤ := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 (Multiplicative V)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  have hg := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := Multiplicative V) (A := A) (q := 2) (by rw [hA]; decide)
  apply BinaryGroupAction.submoduleEquivSubgroup.injective
  rw [OrderIso.map_iSup,OrderIso.map_top]
  simp only [← BinaryGroupAction.fixedPoints_eq ρ]
  apply top_unique
  rw [← hg]
  apply iSup₂_le
  intro K hcyc
  have hd : K.index ∣ 3 := by
    rw [Subgroup.index_eq_card,← hcyc.exponent_eq_card]
    exact (Group.exponent_quotient_dvd K).trans (IsElementaryAbelian.exponent_dvd_p 3 A)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · rw [Subgroup.index_eq_one.mp h1,BinaryGroupAction.fixedPoints_eq,hfixed]
    exact bot_le
  · have hK : Nat.card K = 3 := by
      have hh := K.index_mul_card
      rw [h3,hA] at hh
      omega
    exact le_iSup_of_le ⟨K,hK⟩ le_rfl

omit [FiniteDimensional (ZMod 2) V] in
/-- The norm projectors onto distinct cubic-line fixed spaces annihilate
one another; hence those four fixed spaces are independent. -/
theorem fixed_independent (hA : Nat.card A = 9) (hfixed : fixedSpace ρ ⊤ = ⊥) :
    iSupIndep (fun K : {K : Subgroup A // Nat.card K = 3} => fixedSpace ρ K.val) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let norm (K : Subgroup A) : V →ₗ[ZMod 2] V := ∑ k : K, ρ (k:A)
  have hnfix (K : Subgroup A) (v : V) : norm K v ∈ fixedSpace ρ K := by
    intro a
    change ρ (a:A) ((∑ k : K, ρ (k:A)) v) = (∑ k : K, ρ (k:A)) v
    simp only [LinearMap.sum_apply,map_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft a)
    intro k
    exact (LinearMap.congr_fun (ρ.map_mul (a:A) (k:A)) v).symm
  have hnid (K : Subgroup A) (hK : Nat.card K = 3) (v : V) (hv : v ∈ fixedSpace ρ K) :
      norm K v = v := by
    change (∑ k : K, ρ (k:A)) v = v
    have hv' (k : K) : ρ (k:A) v = v := hv k
    simp only [LinearMap.sum_apply,hv',Finset.sum_const,Finset.card_univ,
      ← Nat.card_eq_fintype_card,hK]
    have hh : (2:ℕ) • v = 0 := ZModModule.char_nsmul_eq_zero 2 v
    simp only [show 3 = 2+1 from rfl,add_nsmul,one_nsmul,hh,zero_add]
  have hnpre (K L : Subgroup A) (v : V) (hv : v ∈ fixedSpace ρ L) :
      norm K v ∈ fixedSpace ρ L := by
    intro a
    change ρ (a:A) ((∑ k : K, ρ (k:A)) v) = (∑ k : K, ρ (k:A)) v
    simp only [LinearMap.sum_apply,map_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      ρ (a:A) (ρ (k:A) v) = ρ (k:A) (ρ (a:A) v) := by
        rw [←Module.End.mul_apply,←map_mul,mul_comm, map_mul,Module.End.mul_apply]
      _ = ρ (k:A) v := congrArg (ρ (k:A)) (hv a)
  have hnkill (K L : Subgroup A) (hK : Nat.card K = 3) (hL : Nat.card L = 3)
      (hne : K ≠ L) : fixedSpace ρ L ≤ (norm K).ker := by
    intro v hv
    let := BinaryGroupAction.action ρ
    have hKfix : K ≤ MulAction.stabilizer A (Multiplicative.ofAdd (norm K v)) :=
      fun a ha => congrArg Multiplicative.ofAdd (hnfix K v ⟨a,ha⟩)
    have hLfix : L ≤ MulAction.stabilizer A (Multiplicative.ofAdd (norm K v)) :=
      fun a ha => congrArg Multiplicative.ofAdd (hnpre K L v hv ⟨a,ha⟩)
    have hall : (⊤ : Subgroup A) ≤ MulAction.stabilizer A (Multiplicative.ofAdd (norm K v)) :=
      (distinct_lines_generate hA K L hK hL hne) ▸ sup_le hKfix hLfix
    have hh : norm K v ∈ fixedSpace ρ ⊤ :=
      fun a => congrArg Multiplicative.toAdd (hall a.property)
    rw [hfixed] at hh
    exact hh
  rw [iSupIndep_def]
  intro K
  have hle : (⨆ L : {K : Subgroup A // Nat.card K = 3}, ⨆ (_ : L ≠ K),
      fixedSpace ρ L.val) ≤ (norm K.val).ker := by
    refine iSup_le fun L => iSup_le fun hn => ?_
    exact hnkill K L K.property L.property (fun he => hn (Subtype.ext he.symm))
  apply Submodule.disjoint_def.mpr
  intro v hvK hvL
  exact (hnid K K.property v hvK).symm.trans (hle hvL)

/-- The four fixed-space dimensions add to the dimension of the original space. -/
theorem sum_fixed_finrank_eq [Fintype {K : Subgroup A // Nat.card K = 3}]
    (hA : Nat.card A = 9) (hfixed : fixedSpace ρ ⊤ = ⊥) :
    (∑ K : {K : Subgroup A // Nat.card K = 3},
      Module.finrank (ZMod 2) (fixedSpace ρ K.val)) = Module.finrank (ZMod 2) V := by
  classical
  let W := fun K : {K : Subgroup A // Nat.card K = 3} => fixedSpace ρ K.val
  have hi : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (fixed_independent ρ hA hfixed) (iSup_fixed_eq_top ρ hA hfixed)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hi
  exact (Module.finrank_directSum (R := ZMod 2) (fun K => W K)).symm.trans e.finrank_eq

end Representation.ElementaryNineFixedDecomposition
