module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.LocalPair
public import Theory.SpecificGroups.PSL3.LinearThreeBinaryLocals
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.Common
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The binary PSL₃ local E₁ members

Both actual local groups are S₄. Their intrinsic two-core quotients are S₃;
an elementary actor escaping the core has a nontrivial image of order two.
The order-six calculation proves that the nontrivial three-core is its full
commutator with that image, that the remaining quotient is a two-group, and
that the actor image has rank one. The transport uses the literal local
embedding and the quotient map by the intrinsic two-core.

The elementary tau inclusion gives containment of the actor in the local.
Alignment with the unipotent Sylow and `localImage_sylow` establish E0.
No ambient generalized-Fitting or SQTK condition is needed for this helper;
the caller retains responsibility for its explicit tau containment premise.

Source: Aschbacher–Smith, E.1.1–5, pp.209–210, the binary PSL₃ case of
E.1.14(1), p.214, and F.1.12(I)(1), pp.262–264.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

private noncomputable def binaryLocalModelEquivS4 (hF : Nat.card F = 2) (b : Bool) :
    localModel F b ≃* Equiv.Perm (Fin 4) := by
  cases b
  · exact binaryLineLocalEquivS4 F hF
  · exact binaryPointLocalEquivS4 F hF

/-- Transport of the intrinsic binary two-core quotient through the literal local embedding. -/
noncomputable def localImage_binaryCoreQuotientEquiv
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (hF : Nat.card F = 2) (b : Bool) :
    (localImage L e b ⧸ pCore 2 (localImage L e b)) ≃* Equiv.Perm (Fin 3) := by
  let E : localModel F b ≃* localImage L e b :=
    (localModel F b).equivMapOfInjective (linearThreeEmbedding L e)
      (embedding_injective L e)
  exact (QuotientGroup.congr _ _ E (pCore_map_iso 2 E)).symm.trans
    (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv (binaryLocalModelEquivS4 hF b))

private theorem alternating_three_selfCentralizing :
    centralizer (alternatingGroup (Fin 3) : Set (Equiv.Perm (Fin 3))) ≤
      alternatingGroup (Fin 3) := by
  intro x hx
  have hc := mem_centralizer_iff.mp hx
  exact (show ∀ x : Equiv.Perm (Fin 3),
    (∀ y : Equiv.Perm (Fin 3), y ∈ alternatingGroup (Fin 3) → y * x = x * y) →
      x ∈ alternatingGroup (Fin 3) by
        simp only [Equiv.Perm.mem_alternatingGroup]
        decide +kernel) x hc

/-- All four E.1.2(E1) clauses at the prime three, for the actual local quotient and actor. -/
theorem localImage_binary_odd_data
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (hF : Nat.card F = 2)
    (b : Bool) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAK : A ≤ localImage L e b) (hne : ¬ A ≤ coreImage L e b) :
    let H := localImage L e b
    let Q := H ⧸ pCore 2 H
    let a := (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
    IsPGroup 2 (Q ⧸ pCore 3 Q) ∧ pCore 3 Q ≠ ⊥ ∧
      pCore 3 Q = ⁅pCore 3 Q, a⁆ ∧ Group.rank a = 1 := by
  let := hA
  let H := localImage L e b
  let B := A.subgroupOf H
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAK
  let E := localImage_binaryCoreQuotientEquiv L e hF b
  let f : H →* Equiv.Perm (Fin 3) := E.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change E ((QuotientGroup.mk' (pCore 2 H)) x) = 1 ↔ x ∈ pCore 2 H
    rw [E.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hb : B.map f ≠ ⊥ := by
    intro hh
    have hle : B ≤ pCore 2 H := hk ▸ (map_eq_bot_iff B).mp hh
    apply hne
    rw [← map_subgroupOf_eq_of_le hAK]
    exact map_mono hle
  apply ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.intrinsic_of_epimorphism
    B f hf hk
  apply ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.primeSection
    Nat.prime_three (by decide) (alternatingGroup (Fin 3))
    (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
    (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
    alternating_three_selfCentralizing (B.map f) hb

/-- The binary local E₁ member. Ambient tau containment remains explicit for final assembly. -/
theorem localImage_binary_isEMemberAt
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (hF : Nat.card F = 2)
    (T : Sylow 2 G)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (b : Bool) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (htau : tau (T : Subgroup G) A ≤ localImage L e b)
    (hne : ¬ A ≤ coreImage L e b) :
    IsEMemberAt 1 (T : Subgroup G) A (localImage L e b) := by
  let := hA
  have hAK : A ≤ localImage L e b :=
    (le_sup_left.trans (sup_pCore_le_tau T A hAT)).trans htau
  have hd := localImage_binary_odd_data L e hF b A hA hAK hne
  have ho : ECaseOdd A (localImage L e b) := ⟨3, Nat.prime_three, by decide, hd⟩
  refine ⟨⟨hA, hAT, hAK, le_inf (tau_le _ _) htau, ?_, Or.inl ho⟩,
    Or.inl ⟨ho, hd.2.2.2.le⟩⟩
  exact localImage_sylow L e T (f := 1) (by decide) (by simpa using hF) halign b

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
