module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenSixExclusion
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenSevenExclusion
public import Theory.Representation.BinaryAlternatingSixNormalDegree
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape.Components
import all CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFactors
import Theory.GroupTheory.GeneralizedFitting.ComponentPrimeRankNormal
import Theory.GroupTheory.PrimeRankSquareFree
import Theory.GroupTheory.PrimeRankZero

/-!
# The original marked fixed line selects the cubic A6 fitting component

The actual ambient binary six-space excludes ordinary A6 and A7. The
outer A6--C3 row has a literal ordinary A6 component; the five-rank bound
makes that component normal in the whole actor, where the proved normal
A6 degree obstruction applies. The surviving fitting component retains its
actual cubic center, A6 central quotient, and full B.5 moved-section source.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem not_outer_six_three_source (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (c : OuterSixThreeShape (offenderSubgroup ρ)) : False := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  let N := c.first.map J.subtype
  let eN := (c.first.equivMapOfInjective J.subtype J.subtype_injective).symm.trans c.firstEquiv
  have hc : IsComponent D N := by
    let := c.first_isComponent.2
    exact ⟨c.first_isComponent.1.trans' (inferInstance : J.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (c.first.equivMapOfInjective J.subtype J.subtype_injective)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup N := eN.isSimpleGroup
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hz : center N=⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative N (center_eq_top_iff.mp he))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hrD : primeRank 5 D≤1 := primeRank_le_one_of_square_not_dvd (no_twentyFive hf hd.le)
  have hNc : Nat.card N=360 := by
    rw [Nat.card_congr eN.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hrN : primeRank 5 N≠0 := by
    intro he
    exact (PrimeRank.eq_zero_iff_not_dvd_card (G := N) (p := 5)).mp he
      (by rw [hNc]; decide)
  let : N.Normal := hc.normal_of_centerless_of_primeRank hz 5 (by omega)
  exact AlternatingSix.BinarySmallDegrees.not_normal_six_space ρ hf hi hd N eN

/-- The genuine B.5 source and the actual fixed-line two-group leave only
the literal cubic fitting component, without replacing the original actor. -/
theorem cubic_from_source (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (small : ∀ S : Sylow 2 D, Nat.card S≤16)
    (C : Subgroup D) (hCJ : C≤offenderSubgroup ρ)
    (eC : C≃*alternatingGroup (Fin 5)) (hCfix : fixedSpace ρ C≠⊥)
    (A : Subgroup D) (hA : IsPGroup 2 A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ A)=1) :
    let J := offenderSubgroup ρ
    let F := generalizedFitting J
    IsQuasisimple F ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion (ρ.comp J.subtype) F) ∧
      Nonempty (center F≃*Multiplicative (ZMod 3)) ∧
      Nonempty ((F ⧸ center F)≃*alternatingGroup (Fin 6)) := by
  rcases rows_from_source ρ hf hi hd.le cover small C hCJ eC hCfix with
    ⟨hq,⟨c⟩,⟨e⟩ | ⟨e⟩ | ht⟩ | ⟨c⟩
  · obtain ⟨e⟩ := e
    exact (not_ordinary_six_source ρ hf hi hd hq c e).elim
  · obtain ⟨e⟩ := e
    exact (not_seven_source ρ hf hi hd hq c e A hA hfix).elim
  · exact ⟨hq,⟨c⟩,ht⟩
  · obtain ⟨c⟩ := c
    exact (not_outer_six_three_source ρ hf hi hd c).elim

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
