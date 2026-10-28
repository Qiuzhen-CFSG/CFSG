module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.CoreCandidates
public import Theory.GroupTheory.EmbeddedCoreCentralizer

/-!
# Ambient normality and centralizers in both core cases

The two surviving core cases give normality of the derived subgroup E and
the exact ambient centralizer F. Full Ree uses characteristicity in F or P
and index two in the intrinsic centralizer; Tits uses F = E. The general
embedded-core detection lemma applies to the literal embedding.

Source: Aschbacher--Smith 14.2.21, printed p.989.
-/

public section
open Subgroup ReeTwo.ParabolicConcrete
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction

private theorem relative_centralizer {A : Type*} [Group A] (R D : Subgroup A)
    (hD : D ≤ R) : centralizer (D.subgroupOf R : Set R) =
      (centralizer (D : Set A)).subgroupOf R := by
  ext x
  constructor
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, hD hy⟩ hy)
  · intro hx y hy
    exact Subtype.ext (hx y hy)

private theorem derived_characteristic {A : Type*} [Group A] (P : Subgroup A) [P.Normal] :
    ((⁅P,P⁆).subgroupOf P).Characteristic := by
  have h : (⁅P,P⁆).subgroupOf P = commutator P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (commutator_le_left _ _), map_subtype_commutator]
  rw [h]
  infer_instance

private theorem centralizer_eq_image {A M : Type*} [Group A] [Group M]
    (i : A →* M) (hi : Function.Injective i) (P E : Subgroup A)
    (hC : centralizer (E.map i : Set M) ≤ P.map i) :
    centralizer (E.map i : Set M) = (centralizer (E : Set A)).map i := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, _, rfl⟩ := hC hg
    refine ⟨x, ?_, rfl⟩
    intro y hy
    apply hi
    simpa only [map_mul] using hg (i y) (mem_map_of_mem _ hy)
  · exact map_centralizer_le_centralizer_image _ _

private theorem ree_index : reeE.relIndex reeF = 2 := by
  have hEF : reeE ≤ reeF := by rw [← reeW_inf_F]; exact inf_le_right
  have hc := (reeE.subgroupOf reeF).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hEF).toEquiv, reeE_card, reeF_card] at hc
  change reeE.relIndex reeF * 32 = 64 at hc
  omega

private theorem ree_detection {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (R : Subgroup Tits.ExceptionalParabolics.FullRee.first) (hFR : reeF ≤ R)
    [(reeE.subgroupOf R).Characteristic]
    (hR : R.map i = pCore 2 M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    (reeE.map i).Normal ∧ centralizer (reeE.map i : Set M) ≤ pCore 2 M := by
  have hEF : reeE ≤ reeF := by rw [← reeW_inf_F]; exact inf_le_right
  have he := hEF.trans hFR
  apply ambient_centralizer_detection i hi R reeE he hR hc
  · rw [relative_centralizer R reeE he]
    exact subgroupOf_mono _ hEF
  · right
    rw [relative_centralizer R reeE he, relIndex_subgroupOf hFR]
    exact ree_index

/-- Either surviving core case gives the required normal E and its exact ambient centralizer. -/
theorem ree_normal_centralizer {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hcases : pCore 2 M = reeF.map i ∨ pCore 2 M = reeQ.map i) :
    (reeE.map i).Normal ∧ centralizer (reeE.map i : Set M) = reeF.map i := by
  have h : (reeE.map i).Normal ∧ centralizer (reeE.map i : Set M) ≤ pCore 2 M := by
    rcases hcases with h | h
    · let := reeE_characteristic_in_F
      exact ree_detection i hi reeF le_rfl h.symm hc
    · let := derived_characteristic reeQ
      exact ree_detection i hi reeQ reeF_le_Q h.symm hc
  refine ⟨h.1, centralizer_eq_image i hi reeQ reeE (h.2.trans ?_)⟩
  rcases hcases with h | h
  · rw [h]; exact map_mono reeF_le_Q
  · exact h.le

/-- The same detection in the Tits model uses its self-centralizing derived subgroup. -/
theorem tits_normal_centralizer {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hcases : pCore 2 M = titsF.map i ∨ pCore 2 M = titsQ.map i) :
    (titsE.map i).Normal ∧ centralizer (titsE.map i : Set M) = titsF.map i := by
  have h : (titsE.map i).Normal ∧ centralizer (titsE.map i : Set M) ≤ pCore 2 M := by
    rcases hcases with h | h
    · rw [titsF_eq_E] at h
      rw [← h]
      exact ⟨inferInstance, hc⟩
    · let := derived_characteristic titsQ
      have he : titsE ≤ titsQ := commutator_le_left _ _
      have hec : centralizer (titsE.subgroupOf titsQ : Set titsQ) =
          titsE.subgroupOf titsQ := by
        rw [relative_centralizer _ _ he]
        exact congrArg (fun S => S.subgroupOf titsQ) titsF_eq_E
      exact ambient_centralizer_detection i hi titsQ titsE he h.symm hc
        hec.symm.le (Or.inl hec.le)
  refine ⟨h.1, centralizer_eq_image i hi titsQ titsE (h.2.trans ?_)⟩
  rcases hcases with h | h
  · rw [h]; exact map_mono titsF_le_Q
  · exact h.le
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction
