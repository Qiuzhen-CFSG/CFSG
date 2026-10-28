module
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.SectionActions
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The simple component in the chief quotient

A genuine component is perfect. When it is simple, its normal two-core is
trivial: the alternative would make the nontrivial perfect group nilpotent.
The resulting core-quotient isomorphism supplies simplicity and nonabelianness
for the literal core-section action. Thus the original nonabelian factor
hypothesis supplies generation of J N_T(J) via the established action image.

Source: Aschbacher--Smith, E.1.11, printed p.213, after the chief factor has
been reduced to a direct product of nonabelian simple groups. The simplicity
instance comes from that source branch, not from quasisimplicity alone.
-/

@[expose] public section
open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem simple_component_core_bot (J : Subgroup G) (hJ : IsComponent G J)
    [IsSimpleGroup J] : pCore 2 J = ⊥ := by
  let : Group.IsPerfect J := hJ.2.toIsPerfect
  rcases (inferInstance : (pCore 2 J).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup J) := h ▸ (pCore_isPGroup (p := 2) (G := J))
    exact False.elim (Group.IsPerfect.not_isNilpotent J (hp.of_equiv topEquiv).isNilpotent)

/-- In the chief quotient's nonabelian branch, the simple component has trivial
2-core; its core quotient really is the original component. -/
noncomputable def simpleComponentCoreEquiv (J : Subgroup G) (hJ : IsComponent G J)
    [IsSimpleGroup J] : (J ⧸ pCore 2 J) ≃* J :=
  (QuotientGroup.quotientMulEquivOfEq (by exact simple_component_core_bot J hJ)).trans
    QuotientGroup.quotientBot

theorem simpleComponentCoreEquiv_mk (J : Subgroup G) (hJ : IsComponent G J)
    [IsSimpleGroup J] (x : J) :
    simpleComponentCoreEquiv J hJ (QuotientGroup.mk' (pCore 2 J) x) = x := rfl

/-- The actual simple component and S=N_T(J) satisfy the local generation
conclusion in E.1.11, using only the original factor-action hypothesis. -/
theorem NonabelianSectionActionBound.simpleComponentNormalizer {i : ℕ} {T : Subgroup G}
    (h : NonabelianSectionActionBound i T) (hT : IsPGroup 2 T)
    (J : Subgroup G) (hJ : IsComponent G J) [IsSimpleGroup J] :
    IsEGenerated i (J ⊔ (T ⊓ normalizer J) : Subgroup G) := by
  let := (simpleComponentCoreEquiv J hJ).isSimpleGroup
  let : Group.IsPerfect J := hJ.2.toIsPerfect
  let : Group.IsPerfect (J ⧸ pCore 2 J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  exact h.coreNormalizer hT J hJ.1 (Group.IsPerfect.not_isMulCommutative _)

end CFSG.Quasithin.ChapterE
