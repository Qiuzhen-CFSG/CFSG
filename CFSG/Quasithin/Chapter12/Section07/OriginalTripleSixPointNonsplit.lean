module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import Theory.Representation.HexacodeAction.FullWeightVectorNonsplit

/-!
# Nonsplitting at the original triple-six point

An invariant complement to the actual scalar point in U would map through
the original chart to an invariant binary complement of the full-weight
field line. The full-weight stabilizer calculation excludes that complement.

Source: Aschbacher--Smith, 12.7.4(2), printed pp.839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original point has no complement in U invariant under its actual
point centralizer. The complement and scalar point are subgroups of the
unchanged ambient group. -/
theorem tripleSixPoint_nonsplit (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (A : Subgroup G) (hAU : A ≤ U)
    (hA : K ⊓ centralizer ({(t : G)} : Set G) ≤ normalizer A)
    (hdis : Disjoint (tripleSixPoint D a t) A) :
    tripleSixPoint D a t ⊔ A ≠ U := by
  intro hsup
  let f := tripleSixPointCoordinates D a
  let w := (f t).toAdd
  let P := Submodule.span Hexacode.F {w}
  let E : Subgroup U ≃o Submodule (ZMod 2) Atlas.Codes.hexacode :=
    f.mapSubgroup.trans (Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2))
  let W := E (A.subgroupOf U)
  have hpoint : E ((tripleSixPoint D a t).subgroupOf U) = P.restrictScalars (ZMod 2) := by
    have hm : ((tripleSixPoint D a t).subgroupOf U).map f.toMonoidHom =
        P.toAddSubgroup.toSubgroup := by
      change (((P.toAddSubgroup.toSubgroup.comap f.toMonoidHom).map U.subtype).comap
        U.subtype).map f.toMonoidHom = _
      rw [comap_map_eq_self_of_injective U.subtype_injective,
        map_comap_eq_self_of_surjective f.surjective]
    change AddSubgroup.toZModSubmodule 2
      (Subgroup.toAddSubgroup' (((tripleSixPoint D a t).subgroupOf U).map f.toMonoidHom)) = _
    rw [hm]
    rfl
  have hcompl : IsCompl ((tripleSixPoint D a t).subgroupOf U) (A.subgroupOf U) := by
    constructor
    · apply disjoint_iff.mpr
      apply bot_unique
      intro u hu
      apply Subtype.ext
      exact show (u : G) = 1 from (disjoint_iff.mp hdis).le hu
    · apply codisjoint_iff.mpr
      rw [← subgroupOf_sup (tripleSixPoint_properties D a t ht).2.1 hAU,
        hsup, subgroupOf_self]
  have hW : Hexacode.fullWeightVectorStabilizer w ≤ subspaceStabilizer Hexacode.evenAction W := by
    apply le_subspaceStabilizer
    intro g hg x hx
    obtain ⟨c, hc⟩ := tripleSixPointCentralizerProjection_surjective D a t ⟨g, hg⟩
    change Multiplicative.ofAdd x ∈ (A.subgroupOf U).map f.toMonoidHom at hx
    obtain ⟨u, hu, hux⟩ := hx
    have he := tripleSixPointCentralizerProjection_conjugate D a t c u
    have hg' : (tripleSixPointCentralizerProjection D a t c).val = g := congrArg Subtype.val hc
    rw [hg'] at he
    have hx' : (f u).toAdd = x := congrArg Multiplicative.toAdd hux
    rw [hx'] at he
    change Multiplicative.ofAdd (Hexacode.evenAction g x) ∈ (A.subgroupOf U).map f.toMonoidHom
    refine ⟨f.symm (Multiplicative.ofAdd (Hexacode.evenAction g x)), ?_, f.apply_symm_apply _⟩
    change ((f.symm (Multiplicative.ofAdd (Hexacode.evenAction g x))) : G) ∈ A
    rw [he]
    exact (mem_normalizer_iff.mp (hA c.property) u).mp hu
  have hfull := tripleSixPoint_full_weight D a t ht heven
  have hw : w ≠ 0 := by
    intro h
    have hh : f t = 1 := h
    exact ht (f.injective (hh.trans f.map_one.symm))
  have hweight : hammingNorm w.val = 6 :=
    hfull.2.2 ⟨w, Submodule.mem_span_singleton_self w⟩ (fun h => hw (congrArg Subtype.val h))
  apply Hexacode.fullWeightVectorStabilizer_nonsplit w hweight W hW
  rw [← hpoint]
  exact E.isCompl_iff.mp hcompl

end CFSG.Quasithin.Chapter12.Section07
