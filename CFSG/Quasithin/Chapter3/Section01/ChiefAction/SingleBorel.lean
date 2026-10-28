module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.BorelGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NaturalCoordinates
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.LinearTwoField
public import Theory.Representation.BinaryOffender.Stability
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Excluding the single higher-field natural source branch

The original quasisimple moved section gives injective whole-module natural
coordinates. Its embedded generalized Fitting subgroup is an actual simple,
even component. The source Borel lifting theorem kills those coordinates on
any seed fixed by lifts centralizing V, contradicting a nonzero seed.
All component, parity, and whole-module assertions are derived from the source
section and faithful irreducibility, rather than supplied as model premises.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 3.1.9(5), printed p.578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3
open ChapterB ChapterB.QuasisimpleSource HigherFieldBorelFixedSpaces
variable {G D W : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.quasisimple_natural_seed_excluded
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hvne : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier)
    (e : ActionEquiv (s.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (linearNatural F 2)) : False := by
  let Y := offenderSubgroup ρ
  let A := generalizedFitting Y
  let : Y.Normal := offenderSubgroup_normal ρ
  let : IsQuasisimple A := hqs
  let L := A.map Y.subtype
  let eA := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let eL := eA.symm.trans e.groupEquiv
  let : IsSimpleGroup PSL(2,F.Carrier) := ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup L := (eL.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
  let : IsSimpleGroup A := eA.isSimpleGroup
  have hL : IsComponent D L :=
    ⟨(inferInstance : A.Normal).isSubnormal.trans' (inferInstance : Y.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv eA⟩
  have heven : 2 ∣ Nat.card L := by
    rw [Nat.card_congr eL.toEquiv]
    have hfcard : 2 ∣ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact dvd_pow_self 2 F.degree_pos.ne'
    have hdiv := (upperUnipotent F.Carrier).card_subgroup_dvd_card
    rw [card_upperUnipotent] at hdiv
    exact hfcard.trans hdiv
  obtain ⟨f,hfi,hfe⟩ := whole_natural_coordinate_of_moved_section ρ hfaith hi Y A
    (A.nontrivial_iff_ne_bot.mp inferInstance) s F e
  have hfeL (g : L) (w : W) : f (ρ (g : D) w) = binaryNatural 2 (eL g) (f w) := by
    have he : (((eA.symm g : A) : Y) : D) = (g : D) :=
      congrArg Subtype.val (eA.apply_symm_apply g)
    rw [←he]
    exact hfe (eA.symm g) w
  have hz := h.natural_component_fixed_seed_coordinate_zero hP hres q hq hc hn ρ v hv
    hL heven hF eL f hfeL
  exact hvne (hfi (hz.trans f.map_zero.symm))
/-- The quasisimple source branch cannot be linear natural over any binary field. -/
theorem QrcHypotheses.quasisimple_natural_seed_impossible
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G))
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hvne : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (linearNatural F 2)) : False := by
  let : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)) := hqs
  exact h.quasisimple_natural_seed_excluded hP hres q hq hc hn ρ hfaith hi v hvne hv hqs s F
    (quasisimple_linear_two_card_ge_four F e.groupEquiv) e

end CFSG.Quasithin.Chapter3
