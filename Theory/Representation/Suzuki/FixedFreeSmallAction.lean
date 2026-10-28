module
public import Theory.Representation.Suzuki.NormalSmallSection
public import Theory.Representation.SevenMultiplicity.Sections
public import Theory.Representation.FrattiniAction
public import Theory.GroupAction.Quotient
/-!
# Fixed-point-free elements in small binary Suzuki actions

A nonzero binary module of degree less than eight times the field exponent
with a fixed-point-free element has the natural degree. Indeed an
irreducible submodule is faithful, the Suzuki degree gap identifies it with
the natural module, and any nonzero quotient would have at least the same
degree. Fixed points lift across characteristic quotients of two-groups
for an odd-order actor. Applying the module result to successive Frattini
quotients gives the corresponding group-order restriction.

In particular, a Suzuki action on a two-group of order q¹⁰ with Frattini
subgroup of order at least q⁴ has no odd-order fixed-point-free element.
This is the composition-factor obstruction used in Fong--Seitz I (6C),
printed p.41, for the intersection of the two rank-one Cartans. The actor
is the concrete Suzuki group with positive native parameter; Sz(2) is not
covered by the simplicity and degree arguments here.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Representation.SuzukiSmallDegree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem faithful_of_fixedFree {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) [Nontrivial V]
    (t : SuzukiMatrixGroup m) (hf : ∀ v, ρ t v = v → v = 0) :
    Function.Injective ρ := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  apply ρ.ker_eq_bot_iff.mp
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have he : ρ t = 1 := show t ∈ ρ.ker from ht ▸ mem_top _
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    exact (hv (hf v (by rw [he]; rfl))).elim

/-- A nonzero small binary Suzuki module with a fixed-point-free element
has exactly the natural degree. No semisimplicity of the Suzuki action is assumed. -/
theorem finrank_eq_four_of_fixedFree {m : ℕ} (hm : 0 < m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) [Nontrivial V]
    (t : SuzukiMatrixGroup m) (hf : ∀ v, ρ t v = v → v = 0)
    (hsmall : Module.finrank (ZMod 2) V < 8*(2*m+1)) :
    Module.finrank (ZMod 2) V = 4*(2*m+1) := by
  obtain ⟨U,hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let := hU
  let := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  have hfU := FixedFreeSections.subrepresentation_fixedFree ρ t hf U
  obtain ⟨e⟩ := natural_equiv_of_smallDegree (by omega) U.toRepresentation
    (faithful_of_fixedFree hm U.toRepresentation t hfU) hU
    ((Submodule.finrank_le U.toSubmodule).trans_lt (by omega))
  have hdU := e.toLinearEquiv.finrank_eq.trans (SuzukiNatural.natural_finrank m)
  have hd := Submodule.finrank_quotient_add_finrank U.toSubmodule
  have hQ : Subsingleton (V ⧸ U.toSubmodule) := by
    by_contra hn
    let : Nontrivial (V ⧸ U.toSubmodule) := not_subsingleton_iff_nontrivial.mp hn
    have hfQ := FixedFreeSections.quotient_fixedFree ρ t hf U
    have hlo := Suzuki.finrank_ge (by omega : 1 ≤ m) U.quotientRepresentation
      (faithful_of_fixedFree hm U.quotientRepresentation t hfQ)
    omega
  let := hQ
  have hz : Module.finrank (ZMod 2) (V ⧸ U.toSubmodule) = 0 := Module.finrank_zero_of_subsingleton
  omega
end Representation.SuzukiSmallDegree

namespace SuzukiFixedFreeAction
private theorem quotient_fixedFree
    {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    (ρ : R →* MulAut A) (hA : IsPGroup 2 A) (t : R)
    (ho : Odd (orderOf t)) (hf : ∀ x, ρ t x = x → x = 1)
    (N : Subgroup A) [N.Characteristic] :
    ∀ x, (quotientAut N (ρ t)) x = x → x = 1 := by
  let C := zpowers t
  let : MulDistribMulAction C A := MulDistribMulAction.compHom A (ρ.comp C.subtype)
  have hN : IsInvariant C A N := by
    constructor
    intro c a
    change a ∈ N ↔ a ∈ N.comap (ρ c).toMonoidHom
    rw [N.characteristic_iff_comap_eq.mp inferInstance]
  let : MulDistribMulAction C (A ⧸ N) := quotientMulDistribMulAction N hN
  let : Group.IsNilpotent A := hA.isNilpotent
  have hcop : Nat.Coprime (Nat.card C) (Nat.card A) := by
    obtain ⟨k,hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA
    rw [hk,Nat.card_zpowers]
    exact ho.coprime_two_right.pow_right k
  intro x hx
  have hxt : (⟨t,mem_zpowers t⟩ : C) • x = x := by
    induction x using QuotientGroup.induction_on with
    | H x =>
        change (quotientAut N (ρ t)) (QuotientGroup.mk' N x) = QuotientGroup.mk' N x at hx
        rw [quotientAut_apply_mk] at hx
        exact hx
  have hxc : x ∈ FixedPoints.subgroup C (A ⧸ N) := by
    intro c
    obtain ⟨k,hk⟩ := mem_zpowers_iff.mp c.property
    have hc : c = (⟨t,mem_zpowers t⟩ : C)^k := Subtype.ext hk.symm
    rw [hc]
    exact MulAction.mem_fixedBy_zpow hxt k
  rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
    (inferInstance : Group.IsSolvable A) hcop N hN] at hxc
  obtain ⟨a,ha,rfl⟩ := hxc
  have ha1 := hf a (ha ⟨t,mem_zpowers t⟩)
  rw [ha1,map_one]

private theorem frattini_ne_top {A : Type*} [Group A] [Finite A] [Nontrivial A] :
    frattini A ≠ ⊤ := by
  intro h
  have he : (⊥ : Subgroup A) = ⊤ := frattini_nongenerating (by rw [h,bot_sup_eq])
  exact bot_ne_top he

private theorem frattini_quotient_card {A : Type*} [Group A] [Finite A] [Nontrivial A]
    {m : ℕ} (hm : 0 < m) (hA : IsPGroup 2 A)
    (ρ : SuzukiMatrixGroup m →* MulAut A) (t : SuzukiMatrixGroup m)
    (ho : Odd (orderOf t)) (hf : ∀ x, ρ t x = x → x = 1)
    (hsmall : Nat.card (A ⧸ frattini A) < 2^(8*(2*m+1))) :
    Nat.card (A ⧸ frattini A) = 2^(4*(2*m+1)) := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) := isElementaryAbelian_quotient_frattini
  let V := Additive (A ⧸ frattini A)
  let : Nontrivial (A ⧸ frattini A) := QuotientGroup.nontrivial_iff.mpr frattini_ne_top
  let σ := Representation.FrattiniAction.ofAutomorphismHom ((quotientAut (frattini A)).comp ρ)
  have hcard : Nat.card (A ⧸ frattini A) = 2^Module.finrank (ZMod 2) V := by
    change Nat.card V = _
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  have hfix : ∀ v : V, σ t v = v → v = 0 := by
    intro v hv
    exact congrArg Additive.ofMul (quotient_fixedFree ρ hA t ho hf (frattini A) v.toMul
      (congrArg Additive.toMul hv))
  have hd := Representation.SuzukiSmallDegree.finrank_eq_four_of_fixedFree hm σ t hfix
    ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hcard ▸ hsmall))
  rw [hcard,hd]

private theorem card_eq_one_of_small {A : Type*} [Group A] [Finite A]
    {m : ℕ} (hm : 0 < m) (hA : IsPGroup 2 A)
    (ρ : SuzukiMatrixGroup m →* MulAut A) (t : SuzukiMatrixGroup m)
    (ho : Odd (orderOf t)) (hf : ∀ x, ρ t x = x → x = 1)
    (hsmall : Nat.card A < 2^(4*(2*m+1))) : Nat.card A = 1 := by
  by_contra hn
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
    have := Nat.card_pos (α := A); omega)
  have hq := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini A))
    (QuotientGroup.mk'_surjective _)
  have he := frattini_quotient_card hm hA ρ t ho hf (hq.trans_lt
    (hsmall.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
  rw [he] at hq
  omega

/-- A Suzuki action with an odd fixed-point-free element on a nontrivial
small two-group forces the entire group, not only its Frattini quotient,
to have order q⁴. -/
theorem card_eq_four_of_fixedFree {A : Type*} [Group A] [Finite A] [Nontrivial A]
    {m : ℕ} (hm : 0 < m) (hA : IsPGroup 2 A)
    (ρ : SuzukiMatrixGroup m →* MulAut A) (t : SuzukiMatrixGroup m)
    (ho : Odd (orderOf t)) (hf : ∀ x, ρ t x = x → x = 1)
    (hsmall : Nat.card A < 2^(8*(2*m+1))) :
    Nat.card A = 2^(4*(2*m+1)) := by
  have hq := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini A))
    (QuotientGroup.mk'_surjective _)
  have he := frattini_quotient_card hm hA ρ t ho hf (hq.trans_lt hsmall)
  have hprod := (frattini A).index_mul_card
  change Nat.card (A ⧸ frattini A) * Nat.card (frattini A) = Nat.card A at hprod
  rw [he] at hprod
  have hsmallPhi : Nat.card (frattini A) < 2^(4*(2*m+1)) := by
    have hp : 2^(8*(2*m+1)) = 2^(4*(2*m+1))*2^(4*(2*m+1)) := by
      rw [←pow_add]; congr 1; omega
    rw [←hprod,hp] at hsmall
    exact (Nat.mul_lt_mul_left (by positivity : 0 < 2^(4*(2*m+1)))).mp hsmall
  let σ := (MulAut.characteristic (frattini A)).comp ρ
  have hfPhi : ∀ x : frattini A, σ t x = x → x = 1 := by
    intro x hx
    exact Subtype.ext (hf x (congrArg Subtype.val hx))
  have hPhi := card_eq_one_of_small hm (hA.to_subgroup _) σ t ho hfPhi hsmallPhi
  simpa only [hPhi,mul_one] using hprod.symm

/-- An action on a two-group of order q¹⁰ with a Frattini subgroup of
order at least q⁴ has no odd fixed-point-free element. -/
theorem no_fixedFree_of_card_ten {A : Type*} [Group A] [Finite A]
    {m : ℕ} (hm : 0 < m) (hA : IsPGroup 2 A)
    (ρ : SuzukiMatrixGroup m →* MulAut A) (t : SuzukiMatrixGroup m)
    (ho : Odd (orderOf t)) (hf : ∀ x, ρ t x = x → x = 1)
    (hc : Nat.card A = 2^(10*(2*m+1)))
    (hPhi : 2^(4*(2*m+1)) ≤ Nat.card (frattini A)) : False := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc]; exact one_lt_pow₀ (by decide) (by omega))
  have hprod := (frattini A).index_mul_card
  change Nat.card (A ⧸ frattini A) * Nat.card (frattini A) = Nat.card A at hprod
  have hpow : 2^(10*(2*m+1)) = 2^(6*(2*m+1))*2^(4*(2*m+1)) := by
    rw [←pow_add]; congr 1; omega
  have hq : Nat.card (A ⧸ frattini A) ≤ 2^(6*(2*m+1)) := by
    apply Nat.le_of_mul_le_mul_right (c := 2^(4*(2*m+1)))
    · exact (Nat.mul_le_mul_left _ hPhi).trans_eq (hprod.trans (hc.trans hpow))
    · positivity
  have he := frattini_quotient_card hm hA ρ t ho hf (hq.trans_lt
    ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)))
  rw [he,hc,hpow,mul_comm (2^(6*(2*m+1)))] at hprod
  have hcardPhi : Nat.card (frattini A) = 2^(6*(2*m+1)) :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hprod
  let : Nontrivial (frattini A) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcardPhi]; exact one_lt_pow₀ (by decide) (by omega))
  let σ := (MulAut.characteristic (frattini A)).comp ρ
  have hfPhi : ∀ x : frattini A, σ t x = x → x = 1 := by
    intro x hx
    exact Subtype.ext (hf x (congrArg Subtype.val hx))
  have hfour := card_eq_four_of_fixedFree hm (hA.to_subgroup _) σ t ho hfPhi (by
    rw [hcardPhi]; exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega))
  have hexp := Nat.pow_right_injective (by decide : 2 ≤ 2) (hcardPhi.symm.trans hfour)
  omega
end SuzukiFixedFreeAction
