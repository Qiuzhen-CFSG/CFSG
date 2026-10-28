module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Reduction
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Involution
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Special

/-!
# Proper-normalizer structure for tightly embedded subgroups

For the genuine I.7.7 setup, `tightNormalClosure R S` is the normal closure
inside `S`, embedded in the ambient group. Splitting first on `|R| = 2`
and then on `W = RS₁` gives all three source alternatives. The first uses
actual dihedral and semidihedral models; the second specifies the multiplication
isomorphism; the third identifies the center, commutator and Frattini subgroup
of `W`, its order and its relative index in `S`.

Each branch also proves normality of `S₁` in `S₀`. In the product branch the
intersection identity is `S₀ ∩ W = S₁`, correcting the printed `S ∩ W`.
The full-normalizer case then gives relative normality without a properness
assumption.

The comparison isomorphism `S₁ ≃* R` remains an explicit premise, supplied
by the separate Sylow-comparison argument in the source theorem's assembly.
The branch proofs derive any needed abelianness from their branch hypotheses,
so this structural conclusion does not require an additional commutativity input.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.7(5--6), printed pp.427--428 (PDF pp.438--439).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08.TightNormalizerSetup
variable {G : Type*} [Group G] [Finite G]
variable {K : Subgroup G} {g : G} {R S : Subgroup G}

/-- I.7.7(5--6) under the earlier comparison isomorphism: the exhaustive
proper-normalizer alternatives, together with normality relative to `S₀`.
All model identifications are multiplicative equivalences, and the product
alternative retains the actual multiplication map and subgroup intersection. -/
theorem properNormalizerStructure (h : TightNormalizerSetup K g R S)
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    let W := tightNormalClosure R S
    ((Nat.card R = 2 ∧
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
      (S1.subgroupOf S0).Normal := by
  dsimp only
  by_cases hR2 : Nat.card R = 2
  · obtain ⟨hmodel, hnormal⟩ := h.involutionBranch e hp hR2
    exact ⟨Or.inl ⟨hR2, hmodel⟩, hnormal⟩
  · by_cases hW : tightNormalClosure R S =
        R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))
    · obtain ⟨hmul, hequiv, hinter, hnormal⟩ := h.productBranch e hW
      exact ⟨Or.inr (Or.inl ⟨hW, hmul, hequiv, hinter⟩), hnormal⟩
    · obtain ⟨n, hn, hmodel, hcard, hcenter, hderived, helem, hmap, hindex, hnormal⟩ :=
        h.specialBranch e hp hR2 hW
      exact ⟨Or.inr (Or.inr ⟨n, hn, hmodel, hcard, hcenter, hderived, helem, hmap, hindex⟩),
        hnormal⟩

/-- I.7.7(6) under the comparison isomorphism, including the full-normalizer
case. The source assembly supplies `e` from I.7.7(2). -/
theorem relativeNormal_of_factor_equiv (h : TightNormalizerSetup K g R S)
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) :
    (((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)).subgroupOf
      (S ⊓ conjSubgroup K g)).Normal := by
  by_cases hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) =
      S ⊓ conjSubgroup K g
  · rw [hfull, subgroupOf_self]
    infer_instance
  · exact (h.properNormalizerStructure e (lt_iff_le_and_ne.mpr ⟨inf_le_left, hfull⟩)).2

end CFSG.Quasithin.ChapterI.Section06To08.TightNormalizerSetup
