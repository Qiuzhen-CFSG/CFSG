module

public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Recognition inside an elementary-eight parabolic

Let a finite group P have an elementary abelian normal subgroup K of order
eight, with conjugation kernel exactly K and |P| = 1344. A subgroup H whose
two-core is nontrivial and whose quotient by that core has order 168 equals P.

Indeed, the kernel of H's conjugation on K is a normal two-subgroup. Comparing
its index with both |H/O₂(H)| and |Aut(K)| forces the full automorphism action
and identifies its kernel with O₂(H). Linear automorphisms are transitive on
the nonidentity elements of K. Thus any nonzero H-invariant subgroup of K
fills K, yielding K ≤ H and then H = P.

This is the irreducibility step in Aschbacher–Smith I.5.10, printed p.422
(combined manuscript of 1 March 2004). The application uses the actual
displacement kernel in a binary four-dimensional point stabilizer.
-/

@[expose] public section

open scoped IsMulCommutative
namespace ElementaryEightParabolic

theorem automorphism_transitive {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E) (Additive.ofMul x) hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E) (Additive.ofMul y) hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨MulEquiv.toAdditive.symm g.toAddEquiv, ?_⟩
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  have h' : g (Additive.ofMul x) = Additive.ofMul y := by
    simpa [ex, ey, LinearEquiv.toSpanNonzeroSingleton] using h.symm
  exact congrArg Additive.toMul h'

variable {P : Type*} [Group P] [Finite P]
theorem eq_top_of_quotient_card (K : Subgroup P) [K.Normal] [IsElementaryAbelian 2 K]
    (hK : Nat.card K = 8) (hP : Nat.card P = 1344)
    (hker : (MulAut.conjNormal : P →* MulAut K).ker = K)
    (H : Subgroup P) (hquot : Nat.card (H ⧸ pCore 2 H) = 168)
    (hcore : pCore 2 H ≠ ⊥) : H = ⊤ := by
  let f : H →* MulAut K := (MulAut.conjNormal : P →* MulAut K).comp H.subtype
  have hk (h : H) : h ∈ f.ker ↔ h.val ∈ K := by
    change h.val ∈ (MulAut.conjNormal : P →* MulAut K).ker ↔ _
    rw [hker]
  let i : f.ker →* K := {
    toFun n := ⟨n.val.val, (hk n.val).mp n.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : K => (k : P)) h
  have hn : IsPGroup 2 f.ker :=
    (IsElementaryAbelian.isPGroup 2 K).of_injective i hi
  have hle : f.ker ≤ pCore 2 H := le_sSup ⟨inferInstance, hn⟩
  have hc := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  have hr : Nat.card f.range ≤ 168 := by
    exact f.range.card_le_card_group.trans_eq (card_mulAut_of_elementary_eight K hK)
  have he : Nat.card H = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have heq : Nat.card H = 168 * Nat.card (pCore 2 H) := by
    rw [← hquot]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 H)
  have hnpos : 0 < Nat.card f.ker := Nat.card_pos
  have hncard : Nat.card (pCore 2 H) ≤ Nat.card f.ker := by nlinarith
  have hN : f.ker = pCore 2 H := Subgroup.eq_of_le_of_card_ge hle hncard
  have hrcard : Nat.card f.range = 168 := by nlinarith
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply Subgroup.eq_top_of_card_eq
    exact hrcard.trans (card_mulAut_of_elementary_eight K hK).symm
  have hNne : f.ker ≠ ⊥ := by rwa [hN]
  obtain ⟨n, hn, hn1⟩ := (Subgroup.bot_or_exists_ne_one f.ker).resolve_left hNne
  let nK : K := ⟨n.val, (hk n).mp hn⟩
  have hnK : nK ≠ 1 := by
    intro h
    apply hn1
    apply Subtype.ext
    exact congrArg (fun k : K => (k : P)) h
  have hKH : K ≤ H := by
    intro k hk'
    by_cases hk1 : k = 1
    · subst k
      exact H.one_mem
    obtain ⟨a, ha⟩ := automorphism_transitive nK (⟨k, hk'⟩ : K) hnK
      (by intro h; exact hk1 (congrArg Subtype.val h))
    obtain ⟨h, hh⟩ := hsurj a
    have hv := congrArg Subtype.val (show f h nK = ⟨k, hk'⟩ by rw [hh]; exact ha)
    change h.val * n.val * h.val⁻¹ = k at hv
    rw [← hv]
    exact H.mul_mem (H.mul_mem h.property n.property) (H.inv_mem h.property)
  have hisurj : Function.Surjective i := by
    intro k
    exact ⟨⟨⟨k.val, hKH k.property⟩, (hk _).mpr k.property⟩, rfl⟩
  have hn8 : Nat.card f.ker = 8 :=
    (Nat.card_congr (Equiv.ofBijective i ⟨hi, hisurj⟩)).trans hK
  apply Subgroup.eq_top_of_card_eq
  rw [he, hrcard, hn8, hP]

theorem surjective_of_quotient_card (K : Subgroup P) [K.Normal] [IsElementaryAbelian 2 K]
    (hK : Nat.card K = 8) (hP : Nat.card P = 1344)
    (hker : (MulAut.conjNormal : P →* MulAut K).ker = K)
    {A : Type*} [Group A] [Finite A] (j : A →* P) (hj : Function.Injective j)
    (hquot : Nat.card (A ⧸ pCore 2 A) = 168) (hcore : pCore 2 A ≠ ⊥) :
    Function.Surjective j := by
  let e := MonoidHom.ofInjective hj
  have hq : Nat.card (j.range ⧸ pCore 2 j.range) = 168 := by
    rw [← Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hquot
  have hn : pCore 2 j.range ≠ ⊥ := by
    intro hn
    apply hcore
    have he := pCore_map_iso 2 e
    rw [hn] at he
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp he
  exact MonoidHom.range_eq_top.mp (eq_top_of_quotient_card K hK hP hker j.range hq hn)
end ElementaryEightParabolic
