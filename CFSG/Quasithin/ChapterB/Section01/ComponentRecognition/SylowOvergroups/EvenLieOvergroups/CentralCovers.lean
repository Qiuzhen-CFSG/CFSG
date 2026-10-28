module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.RankOneModels
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Proper Sylow-overgroup bounds in quasisimple central covers

An actual equivalence L/Z(L) ≃ M transfers a proper Sylow-overgroup bound
on M to L. Perfectness prevents a proper X < L from surjecting onto
L/Z(L), since adjoining central elements cannot enlarge its derived
subgroup. Grün's lemma makes L/Z(L) centreless. Its given bound therefore
places F*(XZ(L)/Z(L)) in the two-core.

Apply generalized-Fitting functoriality and the central-kernel core formula
to the literal restricted quotient map X → XZ(L)/Z(L). Its kernel is
exactly X ∩ Z(L), so the resulting bound retains this full central factor:
F*(X) ≤ O₂(X)(X ∩ Z(L)). No assumption that X contains Z(L) is needed.

The concrete binary PSL₂ theorem supplies the model premise for a central
quotient, and the B.1.13 application uses K subnormal in K ∨ T. This is a
conditional lifting theorem; the full characteristic-two Lie branch must
supply each remaining model bound. A central quotient of Lie type does
not here identify L with a standard Lie carrier.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.13,
printed p.74 (PDF p.85), the proper-Sylow-overgroup contradiction.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
variable {L M : Type*} [Group L] [Group M] [Finite L]

/-- Lift the proper Sylow-overgroup bound through the actual central quotient. -/
theorem properSylowFittingBound_of_centralQuotient [IsQuasisimple L]
    (e : L ⧸ center L ≃* M) (hM : ProperSylowFittingBound M) :
    ProperSylowFittingBound L := by
  have hbound := properSylowFittingBound_of_equiv e hM
  intro S X hSX hX
  let f := QuotientGroup.mk' (center L)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hk : f.ker ≤ center L := by rw [QuotientGroup.ker_mk']
  let Y := X.map f
  let Q := S.mapSurjective hf
  have hQY : (Q : Subgroup (L ⧸ center L)) ≤ Y := map_mono hSX
  have hY : Y ≠ ⊤ := by
    intro he
    apply hX
    apply top_unique
    apply perfect_le_of_map_le_of_central_kernel f hk (⊤ : Subgroup L) X
    change _ ≤ Y
    rw [he]
    exact le_top
  have hfitY : generalizedFitting Y ≤ pCore 2 Y := by
    simpa only [Group.IsPerfect.center_quotient_center_eq_bot, bot_subgroupOf, sup_bot_eq]
      using hbound Q Y hQY hY
  let q : X →* Y := f.subgroupMap X
  have hker : q.ker = (center L).subgroupOf X := by
    ext x
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff x.val).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff x.val).mpr hx)
  have hcentral : q.ker ≤ center X := by
    rw [hker]
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y.val)
  have h := generalizedFitting_le_pCore_sup_ker_of_central_kernel q
    (f.subgroupMap_surjective X) hcentral hfitY
  rwa [hker] at h

/-- Apply the lifted bound to the exact relative-subnormal B.1.13 configuration. -/
theorem eq_component_of_centralQuotient_bound
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L) (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (e : L ⧸ center L ≃* M) (hM : ProperSylowFittingBound M) : K = L := by
  let := hL.2
  exact eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_centralQuotient e hM)

open BenderSuzuki.Converse

/-- The concrete binary PSL₂ bound applies to every quasisimple central cover. -/
theorem properSylowFittingBound_of_psl2_centralQuotient [IsQuasisimple L]
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n) (e : L ⧸ center L ≃* PSL2 F) :
    ProperSylowFittingBound L :=
  properSylowFittingBound_of_centralQuotient e
    (properSylowFittingBound_psl2 F n hn hcard (MulEquiv.refl _))

/-- The binary PSL₂ central quotient discharges the proper-overgroup premise of B.1.13. -/
theorem eq_component_of_psl2_centralQuotient
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L) (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n) (e : L ⧸ center L ≃* PSL2 F) : K = L := by
  let := hL.2
  exact eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_psl2_centralQuotient F n hn hcard e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
