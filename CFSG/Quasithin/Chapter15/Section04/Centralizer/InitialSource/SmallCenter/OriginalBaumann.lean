module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.BaumannApplication
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking

/-!
# The original common Baumann marking in every selected local class

Restriction to M preserves the exact ambient image of Baum(T). Its
canonical subgroup equivalence transports the constructed local-class
embedding back to the original Baum(T). The elementwise map equation is
retained, so a single characteristic pair in that common group applies
across all original M, with no new choice of pair or identification.

Source: Aschbacher--Smith C.1.18--19 and 15.4.7, printed pp.126--127,1158.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The internal Baumann subgroup has exactly its original ambient image. -/
theorem restricted_baumann_map (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    (ChapterB.baumann (T.subtype hTM : Subgroup M)).map M.subtype =
      ChapterB.baumann (T : Subgroup G) := by
  unfold ChapterB.baumann ChapterB.thompsonAlpha
  rw [map_inf _ _ _ M.subtype_injective,map_centralizer_subtype,
    ←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
  rw [←inf_assoc,inf_eq_left.mpr hTM]

/-- The selected local class is marked by the ONE original Baum(T), so
any universally chosen pair in that group applies in every original M. -/
theorem member_original_baumann_localClass {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ∃ (K : Subgroup M) (e : ChapterB.baumann (T : Subgroup G) →* K),
      InLocalClass e ∧
      (∀ b, ((e b : M) : G) = (b : G)) ∧
      K ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ := by
  obtain ⟨K,hBK,hclass,hgen⟩ := member_baumann_localClass h hZ
  let B := ChapterB.baumann (T.subtype h.sylow_le : Subgroup M)
  let a : B ≃* ChapterB.baumann (T : Subgroup G) :=
    (B.equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr (restricted_baumann_map T M h.sylow_le))
  let e := (inclusion hBK).comp a.symm.toMonoidHom
  refine ⟨K,e,hclass.precomp_equiv a.symm,?_,hgen⟩
  intro b
  exact congrArg Subtype.val (a.apply_symm_apply b)
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
