module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.EightKernel
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.CentralCovers
public import Theory.GroupTheory.SylowOvergroupCharacteristic
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# The four-dimensional binary and eight-letter B.1.13 branches

The proved full-transvection-direction argument places any proper
Sylow overgroup in GL₄(2) in a proper subspace parabolic. Its radical is
self-centralizing and lies in the supplied Sylow, proving characteristic
two. Actual exceptional isomorphisms transport this to A₈ and PSL₄(2).
Thus such A₈ overgroups have no components, and the original B.1.13
relative-subnormal seed equals its covering component in this row.

Source: Aschbacher–Smith B.1.13, printed p.74, used by C.1.27, p.133.
-/

public section
open Subgroup Theory.GroupTheory BinaryLinear
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
open ChapterB.ComponentRecognition.SylowOvergroups

/-- Every proper binary four-dimensional Sylow overgroup has a self-centralizing core. -/
theorem linearFour_sylow_overgroup_core
    (S : Sylow 2 (BinaryLinear.GL (Fin 4 → ZMod 2)))
    (X : Subgroup (BinaryLinear.GL (Fin 4 → ZMod 2)))
    (hSX : (S : Subgroup _) ≤ X) (hX : X ≠ ⊤) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  obtain ⟨W, hW0, hWt, hXP⟩ := exists_invariant_subspace S X hSX hX
  exact centralizer_pCore_le_of_sylow_le_normalizer S X (parabolic W) (radical W)
    hSX hXP (radical_le_parabolic W) (parabolic_le_normalizer W) (radical_two W)
    (centralizer_radical_le hW0 hWt)

/-- Transport the same actual core estimate to the eight-letter alternating group. -/
theorem alternatingEight_sylow_overgroup_core
    (S : Sylow 2 (alternatingGroup (Fin 8)))
    (X : Subgroup (alternatingGroup (Fin 8)))
    (hSX : (S : Subgroup _) ≤ X) (hX : X ≠ ⊤) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  let e := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  have hY : X.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hX
    apply map_injective (f := e.toMonoidHom) e.injective
    exact he.trans (map_top_of_surjective _ e.surjective).symm
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap X)).mpr
    (linearFour_sylow_overgroup_core (S.mapSurjective e.surjective)
      (X.map e.toMonoidHom) (map_mono hSX) hY)

/-- The degree-eight component contract is vacuous by the actual core estimate. -/
theorem alternatingEight_properSylowComponentModels :
    AlternatingProperSylowComponentModels 8 := by
  intro S X hSX hX D hD
  exact (not_isComponent_of_twoCore
    (alternatingEight_sylow_overgroup_core S X hSX hX) D hD).elim

/-- The corresponding intrinsic B.1.13 bound on the projective binary model. -/
theorem linearFour_properSylowFittingBound : ProperSylowFittingBound PSL(4,ZMod 2) := by
  let : Finite (OuterCyclic.LinearGroup 4) :=
    Finite.of_injective (fun g : OuterCyclic.LinearGroup 4 =>
      (g : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))) DFunLike.coe_injective
  apply properSylowFittingBound_of_equiv
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  intro S X hSX hX
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
    (linearFour_sylow_overgroup_core S X hSX hX)]
  exact le_sup_left

/-- The literal central-cover consumer preserves the original component and seed. -/
theorem eq_component_of_linearFour_centralQuotient
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L) (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (e : L ⧸ center L ≃* PSL(4,ZMod 2)) : K = L :=
  eq_component_of_centralQuotient_bound K L T hL hLK hkind hK hKL e
    linearFour_properSylowFittingBound

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
