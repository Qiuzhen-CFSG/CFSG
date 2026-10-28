module

public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceOutside
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl

/-!
# The local-family opening of original 15.1.20

For every K in the literal family L(G₁,S), perfectness and source 14.1.6
show that K outside M_Z is also outside M. The original equality J(S)=J(T)
then makes K fail to normalize J(S). If J(S) were contained in O₂(⟨K,S⟩),
Thompson heredity would make that core's normalizer normalize J(S), a
contradiction. This is the nontrivial Thompson action needed at the start
of the FF-module argument in 15.1.20(2).

No ambient C-component hypothesis or new component-selection record is
imposed on K. In particular the results apply to the local parabolic
residuals and the J₄ local subgroup in the source proof. The subsequent
FF-module classification and block reconstruction are separate steps.

Source: Aschbacher--Smith 15.1.20(1--2), printed pp.1094--1097.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Source 15.1.20(1) for the entire local family, with the original G₁ and M_Z. -/
theorem localFamily_not_le_M (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) : ¬ K ≤ M := by
  intro hKM
  let : Group.IsPerfect (K.subgroupOf (K ⊔ d.S)) := hK.2.1.perfect
  let e : K.subgroupOf (K ⊔ d.S) ≃* K := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  exact hout (le_inf hK.1
    ((perfect_subgroup_centralizes_localModule hG T hempty hM hKM).trans
      (localModule_centralizer_le_partner T M hu)))

/-- The ambient Thompson-normalizer control applies to every escaping local member. -/
theorem localFamily_thompson_escape (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) :
    ¬ K ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  intro hn
  rw [show elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) from he] at hn
  exact d.localFamily_not_le_M hG hempty hM hu hK hout
    (hn.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1)

/-- The precise non-core premise in the opening FF-module argument of 15.1.20(2). -/
theorem localFamily_thompson_not_le_core (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hout : ¬ K ≤ d.MZ) :
    ¬ elementaryAbelianMaxJ d.S ≤ (K ⊔ d.S).pCoreIn 2 := by
  intro hJQ
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hQS : (K ⊔ d.S).pCoreIn 2 ≤ d.S := by
    have hh := map_mono (f := (K ⊔ d.S).subtype) (pCore_isPGroup.le_sylow_of_normal P)
    rwa [hP] at hh
  have he : elementaryAbelianMaxJ ((K ⊔ d.S).pCoreIn 2) = elementaryAbelianMaxJ d.S :=
    elementaryAbelianMaxJ_eq_of_intermediate d.S _ hJQ hQS
  have hn : K ⊔ d.S ≤ normalizer ((K ⊔ d.S).pCoreIn 2 : Set G) :=
    (K ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ d.S)
        (pCore 2 (K ⊔ d.S : Subgroup G)))
  have hJN := hn.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  rw [he] at hJN
  exact d.localFamily_thompson_escape hG hempty hM hJ hu h hK hout
    (le_sup_left.trans hJN)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
