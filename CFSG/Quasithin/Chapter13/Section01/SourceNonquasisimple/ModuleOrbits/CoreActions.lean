module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Core
public import Theory.Alternating.Aut

/-!
# The source two-core in a faithful five-letter action

The action of O₂(XT) commutes with the component action on U. It lies in
T, so a faithful five-letter marking puts it in C_S₅(A₅)=1. Thus it fixes
the whole original moved subgroup. This applies to both five-letter rows.

Source: Aschbacher--Smith, proof of 13.1.12, printed p.873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The original action kernel on any subgroup of the normalizer. -/
theorem restricted_action_kernel {L J : Subgroup G}
    (hJ : J ≤ normalizer (L : Set G)) :
    ((action L).comp (inclusion hJ)).ker =
      (centralizer (normalizerMoved L : Set G)).subgroupOf J := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha u hu
    have he := congrArg (fun f : MulAut (normalizerMoved L) =>
      (f ⟨u,hu⟩ : G)) ha
    change (a : G) * u * (a : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro ha
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
    have hc : (u : G) * (a : G) = (a : G) * (u : G) := ha u u.property
    rw [← hc, mul_inv_cancel_right]

/-- A faithful S₅ image with the actual component image A₅ forces the
original O₂(XT) to centralize U. No point-centralizer premise is used. -/
theorem radicalCore_centralizes_of_five_image
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5))
    (hk : q.ker = (centralizer (normalizerMoved L : Set G)).subgroupOf
      (L ⊔ (T : Subgroup G)))
    (hc : (L.subgroupOf (L ⊔ (T : Subgroup G))).map q = alternatingGroup (Fin 5)) :
    (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      centralizer (normalizerMoved L : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  have hT := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hJ : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer hT
  let a := (action L).comp (inclusion hJ)
  have ha : a.ker = q.ker := (restricted_action_kernel hJ).trans hk.symm
  have hRT : (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (XiP p L ⊔ (T : Subgroup G))
      (T.subtype (show (T : Subgroup G) ≤ XiP p L ⊔ (T : Subgroup G) from le_sup_right))
    change _ ≤ ((T : Subgroup G).subgroupOf (XiP p L ⊔ (T : Subgroup G))).map
      (XiP p L ⊔ (T : Subgroup G)).subtype at hh
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤
      XiP p L ⊔ (T : Subgroup G) from le_sup_right)] at hh
  intro r hr
  let rJ : J := ⟨r,(show (T : Subgroup G) ≤ J from le_sup_right) (hRT hr)⟩
  have hrq : q rJ ∈ centralizer (alternatingGroup (Fin 5) : Set (Equiv.Perm (Fin 5))) := by
    rw [← hc]
    rintro x ⟨l,hl,rfl⟩
    have hcomm : a rJ * a l = a l * a rJ :=
      LinearThree.radicalCore_commutes_component_action h hmany hL hn ho hd
        (inclusion hJ rJ) hr ⟨l,hl⟩
    have hker : ⁅rJ,l⁆ ∈ a.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    rw [ha,MonoidHom.mem_ker,map_commutatorElement] at hker
    exact (commutatorElement_eq_one_iff_mul_comm.mp hker).symm
  rw [_root_.GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 5 (by decide),
    mem_bot] at hrq
  have hrk : rJ ∈ q.ker := hrq
  rw [hk] at hrk
  exact hrk

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
