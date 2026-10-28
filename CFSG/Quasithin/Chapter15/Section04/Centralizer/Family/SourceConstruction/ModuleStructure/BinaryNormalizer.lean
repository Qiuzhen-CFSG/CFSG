module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.SinglePlane
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.DoublePlane
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.SourcePair

/-!
# The faithful binary cubic normalizers used in 15.4.12

For elementary binary W of order 2^(2s), s=1 or 2, and an order-3^s
subgroup A of Aut(W), identify its full normalizer with S₃ or the actual
quadratic-isometry group OrthogonalFourBinary. The chosen group coordinates
on W intertwine every original automorphism with the natural model action.

In the double case, the two cubic factors are exactly the actor lines with
nontrivial fixed space, equivalently those whose moved group has order four.
They generate A and their actual moved groups decompose W. This intrinsic
characterization gives unordered uniqueness, full-normalizer invariance, and
an interchange under any irreducible compatible actor.

SourcePair applies the result to SourceConstruction.Basic's literal image M Y
and quotientMap M. Agreement of its faithful W=[V,Y] action with conjugation
by Y proves M-equivariance; relative normality and T-irreducibility then yield
the quotient pair and an actual T-element swapping both residual preimages.
The parent ModuleStructure module retains construction of that faithful action,
the E.2.3 application, and final assembly of clauses (4)--(6).

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.4.12, printed pp.1160--1161; factor interchange at 15.4.18, p.1162.
-/

public section

open Subgroup
open OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

/-- Both source degrees, with full normalizers and compatible vector coordinates. -/
theorem binary_normalizer_coordinates {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (s : ℕ) (hs : s = 1 ∨ s = 2)
    (hW : Nat.card W = 2 ^ (2 * s)) (A : Subgroup (MulAut W)) (hA : Nat.card A = 3 ^ s) :
    (s = 1 ∧ ∃ (c : W ≃* BinaryPlane)
      (e : normalizer (A : Set (MulAut W)) ≃* Equiv.Perm (Fin 3)),
      ∀ (g : normalizer (A : Set (MulAut W))) (w : W),
        c ((g : MulAut W) w) = symmetricThreeAction (e g) (c w)) ∨
    (s = 2 ∧ ∃ (c : W ≃* ModelSpace)
      (e : normalizer (A : Set (MulAut W)) ≃* OrthogonalFourBinary.IsometryGroup),
      A.map (MulAut.congr c).toMonoidHom = modelRotations ∧
      ∀ (g : normalizer (A : Set (MulAut W))) (w : W),
        c ((g : MulAut W) w) = vectorAction (e g) (c w)) := by
  rcases hs with rfl | rfl
  · exact Or.inl ⟨rfl,single_normalizer_coordinates (by simpa using hW) A (by simpa using hA)⟩
  · exact Or.inr ⟨rfl,double_normalizer_coordinates (by simpa using hW) A (by simpa using hA)⟩

/-- Unordered uniqueness is literal equality of the two families of subgroups. -/
theorem FactorPair.range_eq {A W : Type*} [Group A] [Finite A] [Group W] [Finite W]
    [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 W]
    [MulDistribMulAction A W] [FaithfulSMul A W]
    (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    (P Q : FactorPair (A := A) (W := W)) : Set.range P.line = Set.range Q.line := by
  ext D
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := (Q.characterization hA hW (P.line i)).mp
      ((P.characterization hA hW (P.line i)).mpr ⟨i,rfl⟩)
    exact ⟨j,hj.symm⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := (P.characterization hA hW (Q.line i)).mp
      ((Q.characterization hA hW (Q.line i)).mpr ⟨i,rfl⟩)
    exact ⟨j,hj.symm⟩

/-- Full-normalizer coordinates and the intrinsic moved-space pair together. -/
theorem double_normalizer_and_factors {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 16)
    (A : Subgroup (MulAut W)) [IsElementaryAbelian 3 A] (hA : Nat.card A = 9) :
    ∃ (c : W ≃* ModelSpace)
      (e : normalizer (A : Set (MulAut W)) ≃* OrthogonalFourBinary.IsometryGroup)
      (P : FactorPair (A := A) (W := W)),
      A.map (MulAut.congr c).toMonoidHom = modelRotations ∧
      (∀ (n : normalizer (A : Set (MulAut W))) (w : W),
        c ((n : MulAut W) w) = vectorAction (e n) (c w)) ∧
      (∀ i, Nat.card (commutatorAction (P.line i) W) = 4) ∧
      IsCompl (commutatorAction (P.line false) W) (commutatorAction (P.line true) W) ∧
      ∀ (n : normalizer (A : Set (MulAut W))) i,
        ∃ j, (P.line i).map (A.normalizerMonoidHom n).toMonoidHom = P.line j := by
  obtain ⟨c,e,hc,he⟩ := double_normalizer_coordinates hW A hA
  obtain ⟨P⟩ := exists_factorPair (W := W) hA hW
  obtain ⟨hm,hd⟩ := P.moved_decomposition hW
  exact ⟨c,e,P,hc,he,hm,hd,normalizer_preserves_pair A hA hW P⟩

/-- Every irreducible subgroup of the full normalizer contains an element
interchanging the two distinguished actor factors. -/
theorem normalizer_irreducible_swap {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (A : Subgroup (MulAut W)) [IsElementaryAbelian 3 A]
    (hA : Nat.card A = 9) (hW : Nat.card W = 16)
    (P : FactorPair (A := A) (W := W))
    (T : Subgroup (normalizer (A : Set (MulAut W))))
    (hirr : ∀ D : Subgroup A,
      (∀ t : T, D.map (A.normalizerMonoidHom (t : normalizer (A : Set (MulAut W)))).toMonoidHom = D) → D = ⊥ ∨ D = ⊤) :
    ∃ t : T,
      (P.line false).map (A.normalizerMonoidHom (t : normalizer (A : Set (MulAut W)))).toMonoidHom = P.line true ∧
      (P.line true).map (A.normalizerMonoidHom (t : normalizer (A : Set (MulAut W)))).toMonoidHom = P.line false := by
  apply P.exists_swap hA hW (A.normalizerMonoidHom.comp T.subtype) _ hirr
  intro t
  let n : normalizer (A : Set (MulAut W)) := t
  refine ⟨(n : MulAut W), ?_⟩
  intro a w
  change (n : MulAut W) ((a : MulAut W) w) =
    (((n : MulAut W) * (a : MulAut W) * (n : MulAut W)⁻¹) : MulAut W)
      ((n : MulAut W) w)
  simp only [MulAut.mul_apply,MulAut.inv_apply_self]

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
