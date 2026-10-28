module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointStarNonsplit
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointConstrainedSixExclusion
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedSymplecticFixedPoint
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5G2Fixed
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalA5EightExclusion

/-!
# The original triple-six point has no constrained escaping component

The unchanged whole module and its actual point supply the nonsplit
classified star cover. The original normal A₅ seed excludes the small
linear and derived G₂ rows; the whole six-space excludes A₆. The literal
symplectic and G₂ covers have no original globally fixed point, while the
normal A₅ seed obstruction excludes A₈. Thus every genuine natural branch
is impossible for the original selected constrained component.

Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The constrained branch is excluded from the original point data,
with its full module and actual selected component unchanged. -/
theorem original_tripleSix_point_no_constrained_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G))) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬ J ≤ (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)).subgroupOf
      (centralizer ({(t : G)} : Set G)))
    (hf : generalizedFitting J = pCore 2 J) : False := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let Jg := J.map H.subtype
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let ρ := starRepresentation Jg Q
  let O := offenderSubgroup ρ
  let C := starImage Jg Q Jg
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hn := (tripleSixPointResidual_component D a t ht heven).1
  let eA5 := tripleSixPointResidualQuotientEquiv D a t ht heven
  have htc : (t : G) ∈ centralizer (Jg : Set G) := by
    apply mem_centralizer_iff.mpr
    intro j hj
    exact mem_centralizer_singleton_iff.mp ((map_subtype_le J) hj)
  have hpoint (hz : U ⊓ centralizer (Jg : Set G) = ⊥) : False := by
    have ht1 : (t : G) = 1 := mem_bot.mp (hz ▸ (show (t : G) ∈
      U ⊓ centralizer (Jg : Set G) from ⟨t.property,htc⟩))
    exact ht (Subtype.ext ht1)
  obtain ⟨hCO,c,_,_,_,_,_,hi,hnatural⟩ :=
    original_tripleSix_point_star_nonsplit_at h structural D a t ht heven J hJ hq hout hf
  let eC : C ≃* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm
  cases hnatural with
  | linearTwo F ha =>
    obtain ⟨b⟩ := ha
    exact h28.no_constrained_component_star_linear_two J hJ hq hout hf F
      (eC.trans b.groupEquiv)
  | symplectic F ha =>
    obtain ⟨b⟩ := ha
    exact hpoint (h28.constrained_normal_a5_symplectic_module_centralizer hn eA5
      J hJ hq hout hf c hi F b)
  | g2 F ha =>
    obtain ⟨b⟩ := ha
    exact hpoint (h28.constrained_normal_a5_g2_fixed_eq_bot hn eA5
      J hJ hq hout hf c.sectionData hi F b)
  | alternatingSix ha =>
    obtain ⟨b⟩ := ha
    exact original_tripleSix_point_no_constrained_six_at h structural D a t ht heven
      J hJ hq hout hf (eC.trans b.groupEquiv)
  | alternatingEight ha =>
    obtain ⟨b⟩ := ha
    exact h28.no_constrained_normal_a5_star_alternating_eight hn eA5 J hJ hq hout hf
      (eC.trans b.groupEquiv)
  | derivedG2 ha =>
    obtain ⟨b⟩ := ha
    exact h28.no_constrained_normal_a5_star_g2_derived_two hn eA5 J hJ hq hout hf
      (eC.trans b.groupEquiv)
  | linearThree ha =>
    obtain ⟨b⟩ := ha
    exact h28.no_constrained_normal_a5_star_linear_three_two hn eA5 J hJ hq hout hf
      (eC.trans b.groupEquiv)

end CFSG.Quasithin.Chapter12.Section07
