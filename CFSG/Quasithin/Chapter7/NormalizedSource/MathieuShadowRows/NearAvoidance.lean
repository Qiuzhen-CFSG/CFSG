module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.NearAvoidance.Native
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneThompson
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan

/-!
# Transport of M22 cocode avoidance to the original local action

A marked subspace is the image of the literal original subgroup under its
full-automizer marking. The native near-offender bound makes the first higher
Thompson subgroup centralize the whole orbit whenever a subspace of rank
above four avoids the distinguished vectors. No inner-actor restriction or
kernel quotient is added.
Source: Aschbacher--Smith H.15.2(3), E.6.27, 8.1.2, pp.398--399,713.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open MathieuCode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
open ChapterE
variable {G : Type*} [Group G] [Finite G] (W : Subgroup G) [IsElementaryAbelian 2 W]

def markedCocodeSpace (U : Subgroup G) (E : Additive W ≃ₗ[ZMod 2] M22Cocode) :
    Submodule (ZMod 2) M22Cocode :=
  ((Chapter7.moduleSubgroup W).symm (U.subgroupOf W)).map E.toLinearMap

theorem markedCocodeSpace_finrank (U : Subgroup G) (hUW : U ≤ W)
    (E : Additive W ≃ₗ[ZMod 2] M22Cocode) :
    Module.finrank (ZMod 2) (markedCocodeSpace W U E) = rank U := by
  rw [markedCocodeSpace,E.finrank_map_eq,←Chapter7.ambientSubmodule_log_card W,
    Chapter7.ambientSubmodule,(Chapter7.moduleSubgroup W).apply_symm_apply,
    map_subgroupOf_eq_of_le hUW]
  rfl

omit [Finite G] in
theorem markedCocodeSpace_le_fixed (A U : Subgroup G)
    (hAN : A ≤ normalizer (W : Set G)) (hAU : A ≤ centralizer (U : Set G))
    (f : Automizer W →* m22PairStabilizer) (E : Additive W ≃ₗ[ZMod 2] M22Cocode)
    (hE : ∀ a v, E (automizerRepresentation W a v) = m22OuterCocodeRepresentation (f a) (E v))
    (B : Subgroup (Automizer W)) (hB : B ≤ inducedAutomizer W A) :
    markedCocodeSpace W U E ≤ fixedSpace m22OuterCocodeRepresentation (B.map f) := by
  rw [←fixedSpace_map_equivariant (automizerRepresentation W) m22OuterCocodeRepresentation f E hE B]
  apply Submodule.map_mono
  intro v hv
  apply BinaryOffender.fixedSpace_antitone (automizerRepresentation W) hB
  apply (mem_fixedSpace_inducedAutomizer W A hAN v).mpr
  exact le_centralizer_iff.mp hAU hv

omit [Finite G] in
theorem markedCocodeSpace_avoids (U M : Subgroup G)
    (E : Additive W ≃ₗ[ZMod 2] M22Cocode)
    (hcontrol : ∀ x : W, E (Additive.ofMul x) ∈ m22WeightTwoFamily →
      centralizer ({(x : G)} : Set G) ≤ M)
    (hescape : ¬ centralizer (U : Set G) ≤ M) :
    Disjoint (markedCocodeSpace W U E : Set M22Cocode) m22WeightTwoFamily := by
  apply Set.disjoint_left.mpr
  rintro v ⟨u,hu,rfl⟩ hv
  have huG : (u.toMul : G) ∈ U := hu
  exact hescape ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huG)).trans
    (hcontrol u.toMul hv))

/-- The near-offender premise of E.6.27 on the full original local action. -/
theorem cocode_local_thompson_bound (A U : Subgroup G)
    (hWA : W ≤ A) (hAN : A ≤ normalizer (W : Set G))
    (hUW : U ≤ W) (hAU : A ≤ centralizer (U : Set G))
    (a : Automizer W →* m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive W ≃ₗ[ZMod 2] M22Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = m22OuterCocodeRepresentation (a b) (E v))
    (ha : Disjoint (markedCocodeSpace W U E : Set M22Cocode) m22WeightTwoFamily)
    (hr : 4 < rank U) : ChapterB.thompsonJ A 1 ≤ centralizer (W : Set G) := by
  have hdim := markedCocodeSpace_finrank W U hUW E
  apply sSup_le
  intro B hB
  by_contra hn
  let := hB.2.1
  have hBN := hB.1.trans hAN
  let I := inducedAutomizer W B
  have hI : IsElementaryTwo I :=
    ⟨fun hb => hn ((inducedAutomizer_eq_bot_iff hBN).mp hb),inducedAutomizer_elementary W B hBN⟩
  have hIm : IsElementaryTwo (I.map a) := by
    let := hI.2
    exact ⟨fun hb => hI.1 ((I.map_eq_bot_iff_of_injective hinj).mp hb),IsElementaryAbelian.map a⟩
  have hnear := thompson_family_fixedCodim_le W A hWA hAN B hB
  rw [fixedCodim_map_equivariant (automizerRepresentation W) m22OuterCocodeRepresentation
    a E hE,←rank_map_injective a hinj] at hnear
  have hfix := markedCocodeSpace_le_fixed W B U hBN (hB.1.trans hAU) a E hE I le_rfl
  have hd := MathieuCode.NormalizedShadowRows.NearAvoidance.nearOffender_avoiding_bound _ hIm hnear _ hfix ha
  omega
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
