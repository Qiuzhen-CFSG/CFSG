module
public import Theory.SpecificGroups.SU3.SmallSpecialThreeCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSpecialUnitaryApplication

/-!
# The original Borel-core actors on the small unitary three-cores

Restrict the literal original full-Borel-core action to O₃ of the marked
local quotient. The representative formula remains the original ambient
conjugation. For PSU₃(2), preservation of an actual Sylow two-subgroup and
the self-centralizing elementary nine show that restriction has exactly
the original action kernel. For SU₃(2), the characteristic group of order
27 covers the actual elementary nine with the original cubic scalar kernel;
the original Borel-core actors fix that denominator pointwise.

These statements supply the small three-group actions required for the
remaining automorphism argument. Extraspeciality and innerness/semilinear
coverage are not asserted, nor is unrestricted small-unitary enlargement.
The existing conditional 6.5--6.6 applications retain those obligations.
Source: DGS, Groups and Graphs (1985), p.104 and 6.1, pp.118--119;
Aschbacher--Smith F.1.1 and F.1.9, pp.259--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Restrict the original full-Borel-core action to the actual characteristic three-core. -/
@[expose] def originalMarkedThreeCoreAction (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D) :
    (commonBorel L S).pCoreIn 2 →* MulAut (pCore 3 D) :=
  (MulAut.characteristic (pCore 3 D)).comp (originalMarkedBorelCoreAction h i e)

/-- On every original local representative lying in the three-core, restriction is the same ambient conjugation. -/
theorem originalMarkedThreeCoreAction_mk (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D)
    (r : (commonBorel L S).pCoreIn 2) (x : L i)
    (hx : e (QuotientGroup.mk' (pCore 2 (L i)) x) ∈ pCore 3 D) :
    (originalMarkedThreeCoreAction h i e r ⟨e (QuotientGroup.mk' (pCore 2 (L i)) x),hx⟩ : D) =
      e (QuotientGroup.mk' (pCore 2 (L i))
        ((L i).normalizerMonoidHom ⟨r,
          (SuzukiContainment.reduced_hypothesis h).S_normalizes i r.property⟩ x)) :=
  originalMarkedBorelCoreAction_mk h i e r x

/-- A single actual quotient Sylow is preserved by every original Borel-core actor. -/
theorem original_marked_borel_core_preserves_sylow (h : HypothesisF11 L S) (i : Fin 2)
    {D : Type*} [Group D] (e : (L i ⧸ pCore 2 (L i)) ≃* D) :
    ∃ T : Sylow 2 D, ∀ r : (commonBorel L S).pCoreIn 2,
      (T : Subgroup D).map (originalMarkedBorelCoreAction h i e r).toMonoidHom = T := by
  have hB : ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup _) = pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
    apply f11_borel_core_sylow (SuzukiContainment.reduced_hypothesis h)
    exact (normal_subgroupOf_iff_le_normalizer
      (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
        from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)
  obtain ⟨T,hT⟩ := markedBorelCoreAction_normalizer_displacements
    ((SuzukiContainment.reduced_hypothesis h).starredLocalRankOneData i) hB
    (((SuzukiContainment.reduced_hypothesis h).starredQuotientEquiv i).symm.trans e)
  exact ⟨T,fun r => (hT ((MulEquiv.subgroupCongr (SuzukiContainment.reduced_borel_core h).symm) r)).1⟩

/-- In the degree-one projective row the elementary nine detects exactly the original full-quotient action kernel. -/
theorem original_small_projective_three_core_action_ker (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (originalMarkedThreeCoreAction h i e).ker = (originalMarkedBorelCoreAction h i e).ker := by
  obtain ⟨T,hT⟩ := original_marked_borel_core_preserves_sylow h i e
  ext r
  constructor
  · intro hr
    apply HermitianForm.SmallThreeCore.projective_aut_eq_one_of_core_and_sylow
      J hc hconj T (originalMarkedBorelCoreAction h i e r) (hT r)
    intro n hn
    exact congrArg Subtype.val (DFunLike.congr_fun hr (⟨n,hn⟩ : pCore 3 _))
  · intro hr
    change MulAut.characteristic (pCore 3 _) (originalMarkedBorelCoreAction h i e r) = 1
    rw [show originalMarkedBorelCoreAction h i e r = 1 from hr,map_one]

/-- The original full Borel core fixes the exact scalar kernel in the special three-core, without semilinear coverage. -/
theorem original_small_special_three_core_scalar_fixed (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (r : (commonBorel L S).pCoreIn 2) (z : pCore 3 J.specialSubgroup)
    (hz : z ∈ (HermitianForm.SmallThreeCore.specialCoreProjection J).ker) :
    originalMarkedThreeCoreAction h i e r z = z := by
  apply Subtype.ext
  exact original_small_special_borel_core_fixes_center h i J hc hconj e r z.val
    (J.specialToProjective_ker_le_center (congrArg Subtype.val hz))

/-- The actual special three-core is a central cover of the actual elementary nine, and the original Borel-core action fixes its cubic denominator. -/
theorem original_small_special_three_core_cover (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    let q := HermitianForm.SmallThreeCore.specialCoreProjection J
    Nat.card (pCore 3 J.specialSubgroup) = 27 ∧
    Nat.card (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) = 9 ∧
    IsElementaryAbelian 3 (pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
    Function.Surjective q ∧
    q.ker = J.specialToProjective.ker.subgroupOf (pCore 3 J.specialSubgroup) ∧
    Nat.card q.ker = 3 ∧ q.ker ≤ center (pCore 3 J.specialSubgroup) ∧
    commutator (pCore 3 J.specialSubgroup) ≤ q.ker ∧
    ∀ r : (commonBorel L S).pCoreIn 2, ∀ z ∈ q.ker,
      originalMarkedThreeCoreAction h i e r z = z := by
  exact ⟨HermitianForm.SmallThreeCore.special_core_card J hc hconj,
    (HermitianForm.SmallThreeCore.projective_core_structure J hc hconj).1,
    (HermitianForm.SmallThreeCore.projective_core_structure J hc hconj).2.1,
    HermitianForm.SmallThreeCore.specialCoreProjection_surjective J,
    HermitianForm.SmallThreeCore.specialCoreProjection_ker J,
    HermitianForm.SmallThreeCore.specialCoreProjection_ker_card J hc hconj,
    HermitianForm.SmallThreeCore.specialCoreProjection_ker_central J,
    HermitianForm.SmallThreeCore.special_core_commutator_scalar J hc hconj,
    fun r z hz => original_small_special_three_core_scalar_fixed h i J hc hconj e r z hz⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
