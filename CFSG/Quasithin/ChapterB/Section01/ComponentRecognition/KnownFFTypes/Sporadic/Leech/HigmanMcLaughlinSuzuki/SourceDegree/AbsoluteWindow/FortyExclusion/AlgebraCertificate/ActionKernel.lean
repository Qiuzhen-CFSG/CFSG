module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.NormIdeal
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Extracting a norm certificate from a small binary action

Choose a basis inside the span of the actual group operators. Lifting those
basis operators to group elements supplies the spanning field of
`NormCertificate`, with size at most the square of the action dimension.
Nilpotence of the action kernel modulo the literal norm ideal remains a
separate hypothesis; a matrix realization alone supplies no such result.

The product-block lemma composes two nilpotence bounds. The concrete
fixed-vector quotient in `CosetModule` uses it to separate a finite action
calculation from the universal kernel argument.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, author-preprint p.16; Aschbacher--Smith K.4,
printed p.457. These are algebraic reductions, not the source conclusion.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Select actual group elements spanning modulo the action kernel, with the
endomorphism-space dimension as an upper bound. -/
theorem exists_spanning_mod_action_kernel (ρ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V) :
    ∃ (n : ℕ), n ≤ Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V ∧
    ∃ b : Fin n → KnownSimple.SporadicName.hs.Carrier, ∀ g,
      ∃ c : Fin n → ZMod 2,
        MonoidAlgebra.single g 1 -
          ∑ i, MonoidAlgebra.single (b i) (c i) ∈
            TwoSidedIdeal.ker ρ.asAlgebraHom := by
  classical
  let S := Submodule.span (ZMod 2) (Set.range ρ)
  obtain ⟨f, hf, hspan, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range ρ)
  choose b hb using hf
  refine ⟨Module.finrank (ZMod 2) S, ?_, b, ?_⟩
  · simpa only [Module.finrank_linearMap] using S.finrank_le
  · intro g
    have hg : ρ g ∈ Submodule.span (ZMod 2) (Set.range f) := by
      rw [hspan]
      exact Submodule.subset_span ⟨g, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hg
    refine ⟨c, (TwoSidedIdeal.mem_ker _).mpr ?_⟩
    simp only [map_sub, map_sum, Representation.asAlgebraHom_single]
    rw [one_smul, sub_eq_zero]
    simpa only [hb] using hc.symm

/-- A small binary action supplies the spanning field, while the explicit
kernel-nilpotence proof supplies the remaining universal algebra field. -/
noncomputable def of_nilpotentAction
    (ρ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V)
    (hd : Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V < 1600)
    (r : ℕ)
    (hr : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, ρ.asAlgebraHom x = 0) → xs.prod ∈ fiveNormIdeal) :
    NormCertificate := by
  classical
  apply Classical.choice
  obtain ⟨n, hn, b, hb⟩ := exists_spanning_mod_action_kernel ρ
  exact ⟨{
    ideal := TwoSidedIdeal.ker ρ.asAlgebraHom
    exponent := r
    nilpotent := fun xs hlen hmem =>
      hr xs hlen (fun x hx => (TwoSidedIdeal.mem_ker _).mp (hmem x hx))
    size := n
    size_lt := hn.trans_lt hd
    basis := b
    spanning := hb }⟩


private theorem product_blocks {A : Type*} [Ring A]
    (J K : TwoSidedIdeal A) (r s : ℕ)
    (hs : ∀ xs : List A, xs.length = s → (∀ x ∈ xs, x ∈ K) → xs.prod ∈ J)
    (xs : List A) (hlen : xs.length = r * s) (hm : ∀ x ∈ xs, x ∈ K) :
    ∃ ys : List A, ys.length = r ∧ (∀ y ∈ ys, y ∈ J) ∧ ys.prod = xs.prod := by
  induction r generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    exact ⟨[], rfl, by simp, rfl⟩
  | succ r ih =>
    have htake : (xs.take s).length = s := by
      rw [List.length_take, hlen]
      exact Nat.min_eq_left (by nlinarith)
    have hdrop : (xs.drop s).length = r * s := by
      rw [List.length_drop, hlen, Nat.succ_mul]
      omega
    obtain ⟨ys, hys, hmem, hprod⟩ := ih (xs.drop s) hdrop
      (fun x hx => hm x (List.mem_of_mem_drop hx))
    refine ⟨(xs.take s).prod :: ys, by simp [hys], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hs _ htake (fun x hx => hm x (List.mem_of_mem_take hx))
      · exact hmem y hy
    · rw [List.prod_cons, hprod, ← List.prod_append, List.take_append_drop]

/-- Compose two nilpotence bounds, with both ideal inclusions checked on products. -/
theorem nilpotent_products_trans (I J K : TwoSidedIdeal BinaryAlgebra) (r s : ℕ)
    (hr : ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, x ∈ J) → xs.prod ∈ I)
    (hs : ∀ xs : List BinaryAlgebra, xs.length = s →
      (∀ x ∈ xs, x ∈ K) → xs.prod ∈ J)
    (xs : List BinaryAlgebra) (hlen : xs.length = r * s)
    (hm : ∀ x ∈ xs, x ∈ K) : xs.prod ∈ I := by
  obtain ⟨ys, hys, hmem, hprod⟩ := product_blocks J K r s hs xs hlen hm
  rw [← hprod]
  exact hr ys hys hmem

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate
