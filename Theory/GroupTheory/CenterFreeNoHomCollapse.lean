module
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.GroupAction.SubgroupConjugation

/-!
# A center-free central layer collapses when equivariant maps vanish

Let Q,C,Z be normal subgroups of a finite center-free group P, with
Z≤C≤Q, C an abelian two-group, Z centralizing Q, and [C,Q]≤Z. Suppose
an odd subgroup D and a two-subgroup R normalizing D generate P together
with Q, and [C,D]≤Z. If every P-equivariant homomorphism Q→Z killing C
is trivial, then C=Z. Conjugation equivariance uses the canonical normal
subgroup actions and keeps the normality instances explicit.

Coprime splitting reduces the conclusion to C_C(D)=1. The latter is
R-invariant. If nontrivial it contains a nonidentity R-fixed element c.
The central commutator [c,-] is a homomorphism Q→Z killing C. It is
equivariant under Q because Z centralizes Q, and under D and R because
both fix c; the generation hypothesis makes it P-equivariant. Vanishing
therefore makes c centralize Q,D,R, contradicting center-freeness.

This is the nonisomorphic-chief-module transfer used in Stellmacher
(9.1), Journal of Algebra190 (1997), p.48. The concrete absence of
nonzero equivariant maps and the normalizing odd/two complements are
separate inputs; no module classification is hidden in this theorem.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

public theorem eq_of_centerfree_no_equivariant_hom
    {P : Type*} [Group P] [Finite P]
    (Q C Z D R : Subgroup P) [Q.Normal] [C.Normal] [Z.Normal]
    [IsMulCommutative C]
    (hCp : IsPGroup 2 C) (hRp : IsPGroup 2 R)
    (hDodd : Odd (Nat.card D)) (hRD : R ≤ normalizer (D : Set P))
    (hgen : Q ⊔ D ⊔ R = ⊤) (hcenter : center P = ⊥)
    (hZC : Z ≤ C) (hCQ : C ≤ Q) (hZcentral : Z ≤ centralizer (Q : Set P))
    (hCQcomm : ⁅C, Q⁆ ≤ Z) (hCD : ⁅C, D⁆ ≤ Z)
    (hno : ∀ f : Q →* Z, C.subgroupOf Q ≤ f.ker →
      (∀ (g : P) (q : Q), f (MulAut.conjNormal g q) = MulAut.conjNormal g (f q)) →
      f = 1) : C = Z := by
  classical
  let K := C ⊓ centralizer (D : Set P)
  have hKp : IsPGroup 2 K := hCp.to_le inf_le_left
  have hRK : R ≤ normalizer (K : Set P) := by
    have hRC : R ≤ normalizer (C : Set P) := le_normalizer_of_normal
    have hRcentral : R ≤ normalizer (centralizer (D : Set P) : Set P) :=
      hRD.trans ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer
        (D : Set P))).mp inferInstance)
    exact (le_inf hRC hRcentral).trans inf_normalizer_le_normalizer_inf
  have hKbot : K = ⊥ := by
    by_contra hKne
    let _ : MulDistribMulAction R K := conjMulDistribMulActionOfLeNormalizer R K hRK
    have hdiv : 2 ∣ Nat.card K := hKp.card_eq_or_dvd.resolve_left
      (fun hcard => hKne (card_eq_one.mp hcard))
    have hone : (1 : K) ∈ MulAction.fixedPoints R K := by simp [MulAction.mem_fixedPoints]
    obtain ⟨c, hcR, hcne⟩ := hRp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := K) hdiv hone
    have hcC : (c : P) ∈ C := c.property.1
    have hcQ : (c : P) ∈ Q := hCQ hcC
    have hcD : (c : P) ∈ centralizer (D : Set P) := c.property.2
    have hcRcomm : (c : P) ∈ centralizer (R : Set P) := by
      rw [mem_centralizer_iff]
      intro r hr
      have hh := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hcR) ⟨r, hr⟩)
      change r * (c : P) * r⁻¹ = (c : P) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hvalue (q : Q) : ⁅(c : P), (q : P)⁆ ∈ Z :=
      hCQcomm (commutator_mem_commutator hcC q.property)
    let f : Q →* Z :=
      { toFun := fun q => ⟨⁅(c : P), (q : P)⁆, hvalue q⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := by
          intro first second
          apply Subtype.ext
          change ⁅(c : P), (first : P) * (second : P)⁆ =
            ⁅(c : P), (first : P)⁆ * ⁅(c : P), (second : P)⁆
          rw [commutatorElement_mul_right_eq_mul_conj]
          have hh := mem_centralizer_iff.mp (hZcentral (hvalue second)) first first.property
          calc
            _ = ⁅(c : P), (first : P)⁆ * ((first : P) * ⁅(c : P), (second : P)⁆) * (first : P)⁻¹ := by group
            _ = _ := by rw [hh]; group }
    have hkernel : C.subgroupOf Q ≤ f.ker := by
      intro q hq
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change ⁅(c : P), (q : P)⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (setLike_mul_comm (s := C) hcC hq)
    let compatible : Subgroup P :=
      { carrier := {g | ∀ q : Q, f (MulAut.conjNormal g q) = MulAut.conjNormal g (f q)}
        one_mem' := by intro q; simp
        mul_mem' := by
          intro a b ha hb q
          simp only [map_mul, MulAut.mul_apply]
          rw [ha, hb]
        inv_mem' := by
          intro a ha q
          apply (MulAut.conjNormal a : MulAut Z).injective
          rw [← ha]
          simp }
    have hQcompat : Q ≤ compatible := by
      intro g hg q
      apply Subtype.ext
      change (f (MulAut.conjNormal g q) : P) = g * (f q : P) * g⁻¹
      have hconj : MulAut.conjNormal g q = (⟨g, hg⟩ : Q) * q * (⟨g, hg⟩ : Q)⁻¹ := rfl
      rw [hconj, map_mul, map_mul, map_inv]
      have hc1 := mem_centralizer_iff.mp (hZcentral (f q).property) g hg
      have hc2 := mem_centralizer_iff.mp (hZcentral (f q).property) (f ⟨g,hg⟩)
        (hCQ (hZC (f ⟨g,hg⟩).property))
      change (f ⟨g,hg⟩ : P) * (f q : P) * (f ⟨g,hg⟩ : P)⁻¹ = g * (f q : P) * g⁻¹
      rw [hc1, hc2, mul_inv_cancel_right, mul_inv_cancel_right]
    have hfixedCompat (g : P) (hg : g * (c : P) = (c : P) * g) : g ∈ compatible := by
      intro q
      apply Subtype.ext
      change ⁅(c : P), g * (q : P) * g⁻¹⁆ = g * ⁅(c : P), (q : P)⁆ * g⁻¹
      rw [conjugate_commutatorElement, hg, mul_inv_cancel_right]
    have hDcompat : D ≤ compatible := by
      intro g hg
      exact hfixedCompat g (mem_centralizer_iff.mp hcD g hg)
    have hRcompat : R ≤ compatible := by
      intro g hg
      exact hfixedCompat g (mem_centralizer_iff.mp hcRcomm g hg)
    have hcompatible : ∀ g : P, ∀ q : Q,
        f (MulAut.conjNormal g q) = MulAut.conjNormal g (f q) := by
      have htop : (⊤ : Subgroup P) ≤ compatible := by
        rw [← hgen]
        exact sup_le (sup_le hQcompat hDcompat) hRcompat
      exact fun g => htop (mem_top g)
    have hf := hno f hkernel hcompatible
    have hcQcentral : (c : P) ∈ centralizer (Q : Set P) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hh := congrArg (fun φ : Q →* Z => ((φ ⟨q,hq⟩ : Z) : P)) hf
      change ⁅(c : P), q⁆ = 1 at hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    have hcZ : (c : P) ∈ center P := by
      have htop : (⊤ : Subgroup P) ≤ centralizer ({(c : P)} : Set P) := by
        rw [← hgen]
        refine sup_le (sup_le ?_ ?_) ?_
        · intro g hg
          exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcQcentral g hg)
        · intro g hg
          exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcD g hg)
        · intro g hg
          exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcRcomm g hg)
      rw [mem_center_iff]
      intro g
      exact mem_centralizer_singleton_iff.mp (htop (mem_top g))
    have hcOne : c = 1 := Subtype.ext (by simpa [hcenter] using hcZ)
    exact hcne hcOne.symm
  have hcop : Nat.Coprime (Nat.card D) (Nat.card C) := by
    obtain ⟨n, hn⟩ := hCp.exists_card_eq
    rw [hn]
    exact hDodd.coprime_two_right.pow_right n
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime C D
    le_normalizer_of_normal
    (Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := C)).comm a b) hcop
  have hCeq : C = ⁅C, D⁆ := by simpa only [show C ⊓ centralizer (D : Set P) = ⊥ from hKbot,
    sup_bot_eq] using hsplit
  exact le_antisymm (hCeq.le.trans hCD) hZC
end Subgroup
