module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Source
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.EvenRankTwo

/-!
# The literal A.3.18 reduction on the displaced component normalizer

This is the field-reduction interface used after the crossing plane has been
chosen.  The subgroup `E` is retained as the actual nontrivial two-subgroup
centralized by the marked Sylow; hence its normalizer is a genuine two-local.
The earlier 2.5.6 source theorem supplies the ordinary component in that
normalizer and the original source marking.  A.3.18 is then applied to the
literal relative component, transporting the central quotient model through
its inclusion in the original component.

The theorem deliberately stops at the source dichotomy.  The later exceptional
`L_3(4)` E9 argument must still construct its Sylow-three subgroup and the
Frattini-adjusted action from the selected crossing data.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction
open ComponentRefinement
open CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open NonEnlargement
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

variable {G : Type*} [Group G] [Finite G]
variable {M H K S T E : Subgroup G} {z : G}

private noncomputable def centerQuotientCongr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) : (X ⧸ center X) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

/-- Apply the literal A.3.18 dichotomy to the ordinary component in `N(E)`.

The hypotheses `hE`, `hEC`, and `hSE` are the actual crossing-plane placement
from 2.5.7.  No abstract field-reduction or universal A.3.18 input is used.
-/
theorem a318_dichotomy_in_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H = K ⊔ S)
    {n p : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n))
    (hE : E ≠ ⊥) (hEC : E ≤ S ⊓ centralizer (K : Set G))
    (hSE : S ≤ normalizer (E : Set G))
    (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    (K.subgroupOf (normalizer (E : Set G)) =
            if p = 3 then theta (normalizer (E : Set G))
            else primeToResidual p (normalizer (E : Set G))) ∨
        (p = 3 ∧
          ClassicalGroup.IsPSL
            (K.subgroupOf (normalizer (E : Set G)) ⧸
              center (K.subgroupOf (normalizer (E : Set G)))) 3 (2 ^ n) ∧
          IsPGLThree
            ((theta (normalizer (E : Set G))) ⧸
              pPrimeCore 3 (theta (normalizer (E : Set G)))) (2 ^ n)) := by
  obtain ⟨P₀, hP₀⟩ := d.sylow_intersection
  have hSp : IsPGroup 2 S := by
    rw [← hP₀]
    exact P₀.isPGroup'.map (H ⊓ M).subtype
  have hEp : IsPGroup 2 E := hSp.to_le (hEC.trans inf_le_left)
  have hJtwo : IsTwoLocal (normalizer (E : Set G)) :=
    ⟨E, hE, hEp, rfl⟩
  have hJ := hG.twoLocal_sqtk hJtwo
  have hHJ : H ≤ normalizer (E : Set G) := normalizes_centralizer_subgroup hgen hEC hSE
  have hKJ : K ≤ normalizer (E : Set G) := hK.1.trans hHJ
  have hKinJ : IsComponentIn K (normalizer (E : Set G)) :=
    component_in_normalizer_of_binary_rank_two hG sourceC T₀ hM hT₀M hunique hempty
      d hK hgen hn hm hE hEC hSE
  obtain ⟨hJgamma, ⟨P, hP⟩, _⟩ := centralizer_subgroup_normalizer d hgen hE hEC hSE
  obtain ⟨c⟩ := exists_setup_of_same_sylow T₀ hM hT₀M hunique d hJgamma P hP hKinJ
  let eK : K.subgroupOf (normalizer (E : Set G)) ≃* K := subgroupOfEquivOfLe hKJ
  have hZK : IsPGroup 2 (center K) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  have hZ : IsPGroup 2 (center (K.subgroupOf (normalizer (E : Set G)))) :=
    hZK.of_equiv (centerCongr eK.symm)
  have hm' : ClassicalGroup.IsPSL
      (K.subgroupOf (normalizer (E : Set G)) ⧸
        center (K.subgroupOf (normalizer (E : Set G)))) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp
      (K.subgroupOf (normalizer (E : Set G)) ⧸
        center (K.subgroupOf (normalizer (E : Set G)))) 2 (2 ^ n) := by
    rcases hm with hlin | hsp
    · exact Or.inl (hlin.of_mulEquiv (centerQuotientCongr eK))
    · exact Or.inr (hsp.of_mulEquiv (centerQuotientCongr eK))
  have hdich := even_rank_two_dichotomy hJ c.component hZ hn hp ho hd hm'
  exact hdich


/-- The same reduction with the source's literal displaced core `Dˣ`.

Here `Dˣ` is represented by `D.conjBy x⁻¹`, matching the crossing-plane
convention used by the preceding source modules.  The three placement
hypotheses are exactly the inputs still supplied by the normalizer-rechoice
part of 2.5.7.
-/
theorem a318_dichotomy_on_displaced_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H = K ⊔ S)
    {n p : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n))
    (D : Subgroup G) (x : G)
    (hD : D.conjBy x⁻¹ ≠ ⊥)
    (hDxC : D.conjBy x⁻¹ ≤ S ⊓ centralizer (K : Set G))
    (hSDx : S ≤ normalizer (D.conjBy x⁻¹ : Set G))
    (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    (K.subgroupOf (normalizer (D.conjBy x⁻¹ : Set G)) =
        if p = 3 then theta (normalizer (D.conjBy x⁻¹ : Set G))
        else primeToResidual p (normalizer (D.conjBy x⁻¹ : Set G))) ∨
      (p = 3 ∧
        ClassicalGroup.IsPSL
          (K.subgroupOf (normalizer (D.conjBy x⁻¹ : Set G)) ⧸
            center (K.subgroupOf (normalizer (D.conjBy x⁻¹ : Set G)))) 3 (2 ^ n) ∧
        IsPGLThree
          ((theta (normalizer (D.conjBy x⁻¹ : Set G))) ⧸
            pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹ : Set G)))) (2 ^ n)) := by
  exact a318_dichotomy_in_normalizer hG sourceC T₀ hM hT₀M hunique hempty d hK hgen
    hn hm hD hDxC hSDx hp ho hd

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction
