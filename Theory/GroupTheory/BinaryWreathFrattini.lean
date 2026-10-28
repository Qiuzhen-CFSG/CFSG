module
public import Theory.Frattini.SubgroupIndexBound
public import Theory.GroupTheory.SylowFrattiniBounds
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic

/-!
# Sylow Frattini bounds for a binary wreath product

In the elementary abelian Frattini quotient of (R × R) ⋊ C₂, the swap
identifies the images of the two factors. Thus its order is at most twice
that of R/Φ(R). An odd-index embedding transports this bound to Sylow
subgroups of a wreath product with an arbitrary finite base group.

The consumer is the odd symplectic four-space Sylow calculation for
Aschbacher--Smith 4.4.10--11, p.621.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinaryWreathFrattini
local notation "C2" => Multiplicative (ZMod 2)
variable {R : Type*} [Group R] [Finite R]

/-- The nonidentity element interchanges the two factors. -/
@[expose] def action : C2 →* MulAut (R × R) where
  toFun c := if c.toAdd = 0 then 1 else MulEquiv.prodComm
  map_one' := by simp
  map_mul' c d := by
    obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
    obtain ⟨d,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective d
    fin_cases c <;> fin_cases d <;>
      apply MulEquiv.ext <;> rintro ⟨x,y⟩ <;> rfl

/-- The binary permutation wreath product. -/
abbrev W (R : Type*) [Group R] := (R × R) ⋊[action] C2

theorem isPGroup (hR : IsPGroup 2 R) : IsPGroup 2 (W R) := by
  obtain ⟨n,hn⟩ := hR.exists_card_eq
  apply IsPGroup.of_card (n := n+n+1)
  rw [SemidirectProduct.card, Nat.card_prod, hn]
  simp [pow_add]

theorem card_frattini_le (hR : IsPGroup 2 R) :
    Nat.card (W R ⧸ frattini (W R)) ≤ 2 * Nat.card (R ⧸ frattini R) := by
  let : Finite (W R) := Finite.of_equiv ((R × R) × C2) SemidirectProduct.equivProd.symm
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : Fact (IsPGroup 2 (W R)) := ⟨isPGroup hR⟩
  let E := W R ⧸ frattini (W R)
  let : IsElementaryAbelian 2 E := isElementaryAbelian_quotient_frattini
  let q : W R →* E := QuotientGroup.mk' _
  let a : R →* W R := SemidirectProduct.inl.comp (MonoidHom.inl R R)
  let b : C2 →* W R := SemidirectProduct.inr
  have hphi : frattini R ≤ (q.comp a).ker := by
    intro r hr
    apply (QuotientGroup.eq_one_iff (a r)).mpr
    exact frattini_map_le_of_isPGroup (p := 2) a (mem_map_of_mem a hr)
  let f : R ⧸ frattini R →* E := QuotientGroup.lift _ (q.comp a) hphi
  let g : (R ⧸ frattini R) × C2 →* E := f.coprod (q.comp b)
  have hswap (r : R) : q (SemidirectProduct.inl (1,r)) = q (a r) := by
    have h := congrArg q (SemidirectProduct.inl_aut (φ := action (R := R))
      (.ofAdd 1) (r,1))
    change q (SemidirectProduct.inl (1,r)) = _ at h
    simpa [a, map_mul, map_inv, mul_comm, mul_left_comm] using h
  have hg : Function.Surjective g := by
    intro e
    obtain ⟨⟨⟨r,s⟩,c⟩,rfl⟩ := QuotientGroup.mk'_surjective (frattini (W R)) e
    refine ⟨(QuotientGroup.mk' (frattini R) (r*s),c),?_⟩
    change q (a (r*s)) * q (b c) = q ⟨(r,s),c⟩
    rw [SemidirectProduct.mk_eq_inl_mul_inr, map_mul]
    have he : (r,s) = (r,1) * (1,s) := by simp
    rw [he]
    simp only [map_mul, hswap]
    rfl
  have hc := Nat.card_le_card_of_surjective g hg
  have hC : Nat.card C2 = 2 := by change Nat.card (ZMod 2) = 2; exact Nat.card_zmod 2
  simpa only [Nat.card_prod, hC, Nat.mul_comm] using hc


variable {H : Type*} [Group H]

/-- Apply a homomorphism to both factors. -/
@[expose] def map (f : R →* H) : W R →* W H :=
  SemidirectProduct.map (f.prodMap f) (MonoidHom.id C2) (by
    intro c
    ext ⟨r,s⟩ <;> by_cases hc : c = 1 <;> simp [action, hc])

omit [Finite R] in
theorem map_injective (f : R →* H) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro a b hab
  have h := congrArg SemidirectProduct.left hab
  have h' := congrArg SemidirectProduct.right hab
  apply SemidirectProduct.ext
  · exact Prod.ext (hf (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  · exact h'

variable [Finite H]

theorem sylow_card_frattini_le (P : Sylow 2 H) (Q : Sylow 2 (W H)) :
    Nat.card (Q ⧸ frattini Q) ≤ 2 * Nat.card (P ⧸ frattini P) := by
  let : Finite (W H) := Finite.of_equiv ((H × H) × C2) SemidirectProduct.equivProd.symm
  let : Finite (W P) := Finite.of_equiv ((P × P) × C2) SemidirectProduct.equivProd.symm
  let f := map (P : Subgroup H).subtype
  have hf : Function.Injective f := map_injective _ Subtype.val_injective
  have hc : Nat.card f.range = Nat.card P ^ 2 * 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, SemidirectProduct.card, Nat.card_prod]
    have hC : Nat.card C2 = 2 := by change Nat.card (ZMod 2) = 2; exact Nat.card_zmod 2
    rw [hC, pow_two]
  have hi : f.range.index = (P : Subgroup H).index ^ 2 := by
    have hh := f.range.card_mul_index
    rw [hc,SemidirectProduct.card,Nat.card_prod] at hh
    have hC : Nat.card C2 = 2 := by change Nat.card (ZMod 2) = 2; exact Nat.card_zmod 2
    rw [hC,← (P : Subgroup H).card_mul_index] at hh
    have hp := Nat.card_pos (α := P)
    nlinarith
  have hindex : ¬ 2 ∣ f.range.index := by
    rw [hi]
    exact fun h => P.not_dvd_index (Nat.prime_two.dvd_of_dvd_pow h)
  have ht : IsPGroup 2 f.range := (isPGroup P.isPGroup').of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  let S : Sylow 2 (W H) := ht.toSylow hindex
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (Q.equiv S)]
  change Nat.card (f.range ⧸ frattini f.range) ≤ _
  rw [← Theory.GroupTheory.SylowFrattiniBounds.card_congr (MonoidHom.ofInjective hf)]
  exact card_frattini_le P.isPGroup'

end BinaryWreathFrattini

