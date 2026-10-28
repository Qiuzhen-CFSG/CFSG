module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Basic
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Comparison
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure

/-!
# Tightly embedded normalizers

I.7.6 gives commuting, disjoint conjugate Sylow intersections when the relative
normalizer is nontrivial. All six parts of I.7.7 then follow from the genuine
tightly embedded normalizer setup. The Sylow comparison supplies `S₁ ≃* R`,
discharging the structural branch proofs' additional premise. Their exhaustive
alternatives identify the actual dihedral, semidihedral, product and special
groups, and prove normality of `S₁` relative to `S₀`.

The direct products retain the multiplication maps and their ambient embeddings.
The normal closure `W` is taken inside `S`; its center is embedded back into
the ambient group. In the product branch `S₀ ∩ W = S₁` is the intersection
used for normality, correcting the printed `S ∩ W`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.6--7, printed pp.427--428 (PDF pp.438--439).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {K : Subgroup G} {g : G} {R S : Subgroup G}

/-- I.7.7(5): all three proper-normalizer alternatives, with the comparison
isomorphism supplied by I.7.7(2). Specialness is expressed by equality of
the center, derived subgroup and Frattini subgroup and an elementary center. -/
theorem lemma_I_7_7_5 (h : TightNormalizerSetup K g R S)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    let W := tightNormalClosure R S
    (Nat.card R = 2 ∧
        ((∃ m : ℕ, 2 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))) ∨
          (∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (S ≃* Semidihedral.StandardModel n hn)))) ∨
      (W = R ⊔ S1 ∧
        (∃ f : R × S1 ≃* W, ∀ r s, (f (r, s) : G) = (r : G) * (s : G)) ∧
        Nonempty (W ≃* R × R) ∧ S0 ⊓ W = S1) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* Multiplicative (Fin n → ZMod 2)) ∧
        Nat.card W = 2 ^ (3 * n) ∧
        center W = _root_.commutator W ∧
        _root_.commutator W = frattini W ∧
        IsElementaryAbelian 2 (center W) ∧
        (center W).map W.subtype = S1 ∧ W.relIndex S = 2) := by
  obtain ⟨e⟩ := lemma_I_7_7_2 h
  exact (h.properNormalizerStructure e hp).1

/-- I.7.7(6): the first normalizer factor is normal in `S₀`, including
the full-normalizer case, with no comparison premise left to discharge. -/
theorem lemma_I_7_7_6 (h : TightNormalizerSetup K g R S) :
    (((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)).subgroupOf
      (S ⊓ conjSubgroup K g)).Normal := by
  obtain ⟨e⟩ := lemma_I_7_7_2 h
  exact h.relativeNormal_of_factor_equiv e

/-- I.7.7 in full, under only its source hypotheses. The six clauses keep
the literal relative normalizers, Sylow image, product embeddings, normal
closure, model equivalences and relative normality. -/
theorem lemma_I_7_7 (h : TightNormalizerSetup K g R S) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    let W := tightNormalClosure R S
    (S1 = S0 ⊓ centralizer (R : Set G) ∧
      S ⊓ normalizer (R : Set G) = S1 ⊔ R ∧
      ∃ e : S1 × R ≃* ↥(S ⊓ normalizer (R : Set G)),
        ∀ s r, (e (s, r) : G) = (s : G) * (r : G)) ∧
    Nonempty (S1 ≃* R) ∧
    (∃ P : Sylow 2 ↥(conjSubgroup K g ⊓ normalizer (K : Set G)),
      (P : Subgroup _).map (conjSubgroup K g ⊓ normalizer (K : Set G)).subtype = S1) ∧
    (S1 < S0 → IsMulCommutative R) ∧
    (S1 < S0 →
      (Nat.card R = 2 ∧
        ((∃ m : ℕ, 2 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))) ∨
          (∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (S ≃* Semidihedral.StandardModel n hn)))) ∨
      (W = R ⊔ S1 ∧
        (∃ f : R × S1 ≃* W, ∀ r s, (f (r, s) : G) = (r : G) * (s : G)) ∧
        Nonempty (W ≃* R × R) ∧ S0 ⊓ W = S1) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* Multiplicative (Fin n → ZMod 2)) ∧
        Nat.card W = 2 ^ (3 * n) ∧
        center W = _root_.commutator W ∧
        _root_.commutator W = frattini W ∧
        IsElementaryAbelian 2 (center W) ∧
        (center W).map W.subtype = S1 ∧ W.relIndex S = 2)) ∧
    (S1.subgroupOf S0).Normal :=
  ⟨lemma_I_7_7_1 h, lemma_I_7_7_2 h, lemma_I_7_7_3 h,
    lemma_I_7_7_4 h, lemma_I_7_7_5 h, lemma_I_7_7_6 h⟩

end CFSG.Quasithin.ChapterI.Section06To08
