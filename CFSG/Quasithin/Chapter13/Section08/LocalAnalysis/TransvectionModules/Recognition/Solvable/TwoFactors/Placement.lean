module

public import Theory.GroupTheory.NormalSymmetricThreePairRank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.FactorAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.SourceFactors

/-!
# Rank placement in the two actual transvection factors

The internal B.1.8 product identifies the normal transvection closure with
S₃ × S₃. Each pulled-back coordinate is a normal S₃, hence one of the
literal factors by `normal_symmetricThree_eq_factor`. The generic rank
placement theorem therefore applies to a two-perfect {2, 3}-subgroup
normalizing those factors, without a separate compatibility hypothesis.

The final corollary uses the literal L₁* in H/O₂(H), the previously proved
factor normalization, and the three-rank bound on H. The local-model order
restriction remains explicit; the marked cubic construction and the final
source contradiction belong to the source-assembly owner.

Source: Aschbacher–Smith, proof of 13.8.5, combined manuscript of
1 March 2004, printed p.947 (PDF p.964).
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
open ChapterB
local notation "S3" => Equiv.Perm (Fin 3)
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E}

private def firstCoordinateEquiv {X : Type*} [Group X] (e : X ≃* (S3 × S3)) :
    (((⊤ : Subgroup S3).prod ⊥).comap e.toMonoidHom) ≃* S3 where
  toFun x := (e x).1
  invFun x := ⟨e.symm (x, 1), by simp [Subgroup.mem_prod]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [e.apply_symm_apply]
    exact Prod.ext rfl x.property.2.symm
  right_inv x := by simp
  map_mul' x y := congrArg Prod.fst (e.map_mul (x : X) (y : X))

private def secondCoordinateEquiv {X : Type*} [Group X] (e : X ≃* (S3 × S3)) :
    (((⊥ : Subgroup S3).prod ⊤).comap e.toMonoidHom) ≃* S3 where
  toFun x := (e x).2
  invFun x := ⟨e.symm (1, x), by simp [Subgroup.mem_prod]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [e.apply_symm_apply]
    exact Prod.ext x.property.1.symm rfl
  right_inv x := by simp
  map_mul' x y := congrArg Prod.snd (e.map_mul (x : X) (y : X))

/-- The pulled-back first coordinate is one of the actual B.1.8 factors. -/
theorem firstFactor_eq_ambientFactor (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) :
    ∃ i, Theory.GroupTheory.NormalSymmetricThreePairRank.firstFactor
      (normalClosure ({t} : Set A)) (twoFactorModel d hJ hc) = ambientFactor t d i := by
  let e := twoFactorModel d hJ hc
  let N := ((⊤ : Subgroup S3).prod ⊥).comap e.toMonoidHom
  have : N.Normal := by
    dsimp [N]
    infer_instance
  obtain ⟨i, hi⟩ := normal_symmetricThree_eq_factor d hJ hc N (firstCoordinateEquiv e)
  exact ⟨i, congrArg (fun U : Subgroup (normalClosure ({t} : Set A)) =>
    U.map (normalClosure ({t} : Set A)).subtype) hi⟩

/-- The pulled-back second coordinate is one of the actual B.1.8 factors. -/
theorem secondFactor_eq_ambientFactor (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) :
    ∃ i, Theory.GroupTheory.NormalSymmetricThreePairRank.secondFactor
      (normalClosure ({t} : Set A)) (twoFactorModel d hJ hc) = ambientFactor t d i := by
  let e := twoFactorModel d hJ hc
  let N := ((⊥ : Subgroup S3).prod ⊤).comap e.toMonoidHom
  have : N.Normal := by
    dsimp [N]
    infer_instance
  obtain ⟨i, hi⟩ := normal_symmetricThree_eq_factor d hJ hc N (secondCoordinateEquiv e)
  exact ⟨i, congrArg (fun U : Subgroup (normalClosure ({t} : Set A)) =>
    U.map (normalClosure ({t} : Set A)).subtype) hi⟩

/-- Rank and order place the given two-perfect subgroup inside the literal
normal transvection closure, and make it a three-group. -/
theorem le_normalClosure_and_isThreeGroup [Finite A] (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (B : Subgroup A)
    (hB : IsPPerfect 2 B) (hrank : primeRank 3 A ≤ 2)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n)
    (hnorm : ∀ i, B ≤ normalizer (ambientFactor t d i : Set A)) :
    B ≤ normalClosure ({t} : Set A) ∧ IsPGroup 3 B := by
  apply Theory.GroupTheory.NormalSymmetricThreePairRank.le_pair_and_isThreeGroup
    (normalClosure ({t} : Set A)) (twoFactorModel d hJ hc) B hB hrank horder
  · obtain ⟨i, hi⟩ := firstFactor_eq_ambientFactor t d hJ hc
    rw [hi]
    exact hnorm i
  · obtain ⟨i, hi⟩ := secondFactor_eq_ambientFactor t d hJ hc
    rw [hi]
    exact hnorm i

open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

/-- Placement of the literal L₁* in the source quotient. The source's
three-rank bound is transported through O₂(H); its local model must supply
the displayed order restriction. -/
theorem source_one_le_normalClosure_and_isThreeGroup
    {G : Type*} [Group G] [Finite G] (L T V₁ G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (ρ : Representation (ZMod 2) (Source.Hstar H) E) (t : Source.Hstar H)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : d.count = 2) (hrank : primeRank 3 H ≤ 2)
    (horder : ∃ m n : ℕ, Nat.card (Source.starImage H (one L T V₁)) ∣ 2 ^ m * 3 ^ n) :
    Source.starImage H (one L T V₁) ≤ normalClosure ({t} : Set (Source.Hstar H)) ∧
      IsPGroup 3 (Source.starImage H (one L T V₁)) := by
  refine le_normalClosure_and_isThreeGroup t d hJ hc _ ?_ ?_ horder ?_
  · exact starImage_isPPerfect H (one L T V₁) (le_sup_left.trans hH.1.2)
      (isPPerfect_embedded_pResidual 2 (parabolic L T V₁))
  · exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide)
      (pCore 2 H) pCore_isPGroup).trans hrank
  · exact source_one_normalizes_factors L T V₁ G₁ M H hH ρ t d hJ hc

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
