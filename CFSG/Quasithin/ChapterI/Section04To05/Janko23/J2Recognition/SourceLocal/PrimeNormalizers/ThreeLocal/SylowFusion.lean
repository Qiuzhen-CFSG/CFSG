module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Extension
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.ActionTypes
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.ProjectiveLift
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCosetFusion


/-!
# The two three-classes and the marked Sylow normalizer

This module proves the assembly of Aschbacher, *Sporadic Groups* (1994),
47.3(2)–(4), printed pp.261–262, from `CentralizerCalculation` and the
exact earlier-source order, selected involution geometry, and five-local
conclusions. `SecondNormalizer` excludes the C₃ × A₅ centralizer alternative
using the five-local data and constructs the second-class normalizer.
`ProjectiveLift` constructs the cyclic eight-complement and its action
through the actual PGL₂(9) quotient of the first-class normalizer.

The order calculation gives extraspecial Sylow subgroups with their embedded
centers in the source vertex orbit. Transitivity on the intrinsic Frattini
quotient lifts to conjugacy of noncentral elements: inner conjugation supplies
the required central adjustment. The two source involution conditions then
classify all elements of order three. This proves both the first-class/center
equivalence and weak closure, and fills every field of the original contracts.

`threeFusion_and_sylowStructure` discharges both constructions. No normalizer,
action, fusion or weak-closure premise remains beyond the specified source
inputs. The parent three-local calculation owns the construction of
`CentralizerCalculation`; the earlier 47.1 and 47.2 calculations own the
order, `SelectedGeometry`, and `FiveLocal.SourceConclusion` premises.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem exists_conjugate_in_sylowThree (P : Sylow 3 G) (x : G) (hx : orderOf x = 3) :
    ∃ a : P, IsConj x (a : G) ∧ orderOf a = 3 := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G Q P
  let a : Q := ⟨x, hQ (mem_zpowers x)⟩
  refine ⟨Q.equivSMul g a, isConj_iff.mpr ⟨g, rfl⟩, ?_⟩
  rw [(Q.equivSMul g).orderOf_eq, ← orderOf_coe a]
  exact hx

theorem threeA_of_mem_sylow_center (P : Sylow 3 G) (hP : IsExtraspecial 3 P)
    (hV : (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X)
    (x : P) (hx : orderOf x = 3) (hxZ : x ∈ center P) : ThreeA D (x : G) := by
  let := hP
  have ho : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  refine ⟨ho, ?_⟩
  have he : zpowers (x : G) = (center P).map (P : Subgroup G).subtype :=
    eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem _ hxZ))
      (by rw [Nat.card_zpowers, ho, card_map_of_injective
        (P : Subgroup G).subtype_injective, IsExtraspecial.center_order_p 3 P])
  rwa [he]

namespace SylowNormalizerAction

/-- The inner action supplies the central adjustment missing from quotient transitivity. -/
theorem isConj_noncentral {P : Sylow 3 G} (A : SylowNormalizerAction P)
    (hP : IsExtraspecial 3 P) {x y : P} (hx : x ∉ center P) (hy : y ∉ center P) :
    IsConj (x : G) (y : G) := by
  let := hP
  have hn (z : P) (hz : z ∉ center P) : QuotientGroup.mk' (frattini P) z ≠ 1 := by
    intro h
    apply hz
    have hm := (QuotientGroup.eq_one_iff z).mp h
    rwa [IsExtraspecial.frattini_eq_center (p := 3)] at hm
  obtain ⟨b, hb⟩ := A.transitive _ _ (hn x hx) (hn y hy)
  let e := (P : Subgroup G).normalizerMonoidHom b
  have he : QuotientGroup.mk' (center P) (e x) = QuotientGroup.mk' (center P) y := by
    rw [sylowFrattiniAction_apply_mk] at hb
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hm := QuotientGroup.eq_iff_div_mem.mp hb
    rw [IsExtraspecial.frattini_eq_center (p := 3)] at hm
    exact hm
  have hex : e x ∉ center P := by
    intro h
    apply hx
    apply mem_center_iff.mpr
    intro z
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp h (e z)
  have hc := (P : Subgroup G).subtype.map_isConj
    (IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 3) hex he)
  exact (isConj_iff.mpr ⟨((b : normalizer (P : Set G)) : G), rfl⟩).trans hc

/-- All noncentral elements belong to the second source class. -/
theorem threeB_of_noncentral {P : Sylow 3 G} (A : SylowNormalizerAction P)
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (hB : SecondNormalizerFamily D) (hP : IsExtraspecial 3 P)
    (hV : (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X)
    {x : P} (hx : x ∉ center P) : ThreeB D (x : G) := by
  obtain ⟨b, hb⟩ := threeB_exists S
  obtain ⟨y, hy, hyo⟩ := exists_conjugate_in_sylowThree P b hb.1
  have hyB := threeB_of_isConj hy hb
  have hyZ : y ∉ center P := fun hz =>
    threeA_not_threeB H hB (threeA_of_mem_sylow_center P hP hV y hyo hz) hyB
  exact threeB_of_isConj (A.isConj_noncentral hP hyZ hx) hyB

/-- The first source class inside P is precisely its center. -/
theorem threeA_iff_center {P : Sylow 3 G} (A : SylowNormalizerAction P)
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (hB : SecondNormalizerFamily D) (hP : IsExtraspecial 3 P)
    (hV : (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X)
    (x : P) (hx : orderOf x = 3) : ThreeA D (x : G) ↔ x ∈ center P := by
  constructor
  · intro hA
    by_contra hz
    exact threeA_not_threeB H hB hA (A.threeB_of_noncentral H S hB hP hV hz)
  · exact threeA_of_mem_sylow_center P hP hV x hx

/-- Element fusion forces weak closure of the literal embedded center. -/
theorem center_weakly_closed {P : Sylow 3 G} (A : SylowNormalizerAction P)
    (H : CentralizerCalculation D) (S : InvolutionGeometry.SelectedGeometry D)
    (hB : SecondNormalizerFamily D) (hP : IsExtraspecial 3 P)
    (hV : (center P).map (P : Subgroup G).subtype ∈ MulAction.orbit (ConjAct G) D.X)
    (g : G)
    (hg : ((center P).map (P : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G)) :
    ((center P).map (P : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
      (center P).map (P : Subgroup G).subtype := by
  let := hP
  let Z := (center P).map (P : Subgroup G).subtype
  let Zg := Z.map (MulAut.conj g).toMonoidHom
  have hc : Nat.card Z = 3 := by
    rw [card_map_of_injective (P : Subgroup G).subtype_injective,
      IsExtraspecial.center_order_p 3 P]
  have hcg : Nat.card Zg = 3 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hc]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Zg) 3 (by rw [hcg])
  have hao : orderOf (a : G) = 3 := (orderOf_coe a).trans ha
  have hgen : zpowers (a : G) = Zg := eq_of_le_of_card_ge
    (zpowers_le.mpr a.property) (by rw [Nat.card_zpowers, hao, hcg])
  have hAg : ThreeA D (a : G) := ⟨hao, by
    rw [hgen]
    exact MulAction.mem_orbit_of_mem_orbit (ConjAct.toConjAct g) hV⟩
  have hmem := (A.threeA_iff_center H S hB hP hV ⟨a, hg a.property⟩
    ((orderOf_coe _).symm.trans hao)).mp hAg
  have hle : Zg ≤ Z := by
    rw [← hgen]
    exact zpowers_le.mpr (mem_map_of_mem _ hmem)
  exact eq_of_le_of_card_ge hle (by rw [hc, hcg])

end SylowNormalizerAction

/-- Conditional assembly of every field of 47.3(2)–(4). The two remaining
calculations are explicit and must be discharged by source assembly. -/
theorem threeFusion_and_sylowStructure_of_calculations
    (H : CentralizerCalculation D) (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D) (hB : SecondNormalizerFamily D)
    (hActions : ∀ P : Sylow 3 G, Nonempty (SylowNormalizerAction P)) :
    ThreeFusion D ∧ ∀ P : Sylow 3 G, Nonempty (SylowThreeStructure D P) := by
  classical
  have hP (P : Sylow 3 G) := sylowThree_extraspecial hG S hB P
  have hV (P : Sylow 3 G) := sylowThree_center_vertex H hG S hB P
  have hcover (x : G) (hx : orderOf x = 3) : ThreeA D x ∨ ThreeB D x := by
    let P : Sylow 3 G := Classical.choice inferInstance
    obtain ⟨a, ha, hao⟩ := exists_conjugate_in_sylowThree P x hx
    by_cases hz : a ∈ center P
    · exact Or.inl (threeA_of_isConj ha.symm
        (threeA_of_mem_sylow_center P (hP P) (hV P) a hao hz))
    · exact Or.inr (threeB_of_isConj ha.symm
        ((hActions P).some.threeB_of_noncentral H S hB (hP P) (hV P) hz))
  constructor
  · obtain ⟨a, hao, ha⟩ := exists_threeA D
    obtain ⟨b, hb⟩ := threeB_exists S
    refine ⟨⟨a, b, ha, hb, ?_, ?_, ?_, hcover⟩, hB⟩
    · intro hab
      exact threeA_not_threeB H hB (threeA_of_isConj hab ha) hb
    · intro x
      exact ⟨threeA_isConj D H a hao, fun hx => threeA_of_isConj hx ha⟩
    · intro x
      exact ⟨fun hx => threeB_isConj S hb hx, fun hx => threeB_of_isConj hx hb⟩
  · intro P
    let A := (hActions P).some
    exact ⟨{
      card := sylowThree_card hG P
      extraspecial := hP P
      center_vertex := hV P
      weakly_closed := A.center_weakly_closed H S hB (hP P) (hV P)
      complement := A.complement
      complement_cyclic := A.cyclic
      complement_card := A.card
      split := A.split
      faithful := A.faithful
      transitive := A.transitive
      class_in_sylow := A.threeA_iff_center H S hB (hP P) (hV P) }⟩

/-- Aschbacher 47.3(2)–(4), conditional only on the first centralizer calculation
and the exact earlier conclusions of 47.1–47.2. The second-normalizer and
projective-action constructions are discharged, preserving the literal
embedded center, normalizer complement, and intrinsic Frattini action. -/
theorem threeFusion_and_sylowStructure
    (H : CentralizerCalculation D) (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    (F : FiveLocal.SourceConclusion D S.t) :
    ThreeFusion D ∧ ∀ P : Sylow 3 G, Nonempty (SylowThreeStructure D P) := by
  have hB : SecondNormalizerFamily D := SecondNormalizer.secondNormalizerFamily H S F
  apply threeFusion_and_sylowStructure_of_calculations H hG S hB
  intro P
  exact ProjectiveLift.sylowNormalizerAction H P
    (sylowThree_extraspecial hG S hB P) (sylowThree_center_vertex H hG S hB P)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
