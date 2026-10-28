module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.LocalSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.InternalModule

/-!
# Faithful action on the actual component module

Before choosing module coordinates, the Sylow-central seed and `I = LS`
show that `[U_I,I]` lies in `U_L`. An element centralizing `U_L` therefore
has square centralizing `U_I`. Its image in the star quotient belongs to a
normal two-subgroup, and that quotient has trivial two-core. Consequently
`C_I(U_L) = C_I(U_I)`, and conjugation on the actual elementary abelian
`U_L` descends faithfully through the original star map.

This is preparation for the FF classification application, not recognition
of the module. No natural coordinates or covering classification are inputs.
All subgroup normality below is relative to the local overgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.14
and the paragraph preceding 15.3.32, printed pp.78 and 1132.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G]

private theorem commutator_le_of_seed (U W L S Z : Subgroup G) [W.Normal]
    (hUL : ⁅U, L⁆ ≤ W) (hU : U = Z ⊔ W)
    (hZS : Z ≤ centralizer (S : Set G)) (hLS : L ⊔ S = ⊤) : ⁅U, ⊤⁆ ≤ W := by
  let q := QuotientGroup.mk' W
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective W
  have hUW : U.map q = Z.map q := by
    rw [hU, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hL : L.map q ≤ centralizer (U.map q : Set (G ⧸ W)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hUL)
  have hS : S.map q ≤ centralizer (U.map q : Set (G ⧸ W)) := by
    rw [hUW]
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, commutator_eq_bot_iff_le_centralizer.mpr hZS, Subgroup.map_bot]
  have hc : (⊤ : Subgroup (G ⧸ W)) ≤ centralizer (U.map q : Set (G ⧸ W)) := by
    rw [← map_top_of_surjective q hq, ← hLS, Subgroup.map_sup]
    exact sup_le hL hS
  have hm : (⁅U, ⊤⁆ : Subgroup G).map q = ⊥ := by
    rw [map_commutator, map_top_of_surjective q hq]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm

private theorem square_centralizes (U W : Subgroup G) [IsElementaryAbelian 2 W]
    (hc : ⁅U, ⊤⁆ ≤ W) {k : G} (hk : k ∈ centralizer (W : Set G)) :
    k ^ 2 ∈ centralizer (U : Set G) := by
  intro u hu
  have ht : ⁅k, u⁆ ∈ W := by
    apply hc
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_top k) hu
  have hkt : k * ⁅k, u⁆ = ⁅k, u⁆ * k := (hk _ ht).symm
  have htt : ⁅k, u⁆ * ⁅k, u⁆ = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) ⁅k, u⁆ ht
  have hku : k * u = ⁅k, u⁆ * u * k := by simp only [commutatorElement_def]; group
  calc
    u * k ^ 2 = (⁅k, u⁆ * ⁅k, u⁆) * u * k ^ 2 := by rw [htt, one_mul]
    _ = ⁅k, u⁆ * (⁅k, u⁆ * u * k) * k := by group
    _ = ⁅k, u⁆ * (k * u) * k := by rw [← hku]
    _ = k * (⁅k, u⁆ * u * k) := by rw [← mul_assoc, ← hkt]; group
    _ = k ^ 2 * u := by rw [← hku, pow_two, mul_assoc]

private theorem centralizer_eq_of_twoReduced {H : Type*} [Group H]
    (U W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hWU : W ≤ U) (hc : ⁅U, ⊤⁆ ≤ W)
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥) :
    centralizer (W : Set G) = q.ker := by
  apply le_antisymm ?_ (hk ▸ centralizer_le hWU)
  let K := (centralizer (W : Set G)).map q
  have hnormal : K.Normal := (inferInstance : (centralizer (W : Set G)).Normal).map q hq
  have hp : IsPGroup 2 K := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    rintro ⟨x, g, hg, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (q g) ^ (2 ^ 1) = 1
    rw [pow_one, ← map_pow]
    exact (hk ▸ square_centralizes U W hc hg : g ^ 2 ∈ q.ker)
  have hK : K ≤ pCore 2 H := le_sSup ⟨hnormal, hp⟩
  intro g hg
  exact mem_bot.mp (hcore ▸ hK (mem_map_of_mem q hg))

/-- The full local overgroup acts trivially on `U_I/U_L`. -/
theorem span_commutator_le_component [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) :
    ⁅(d.UI I).subgroupOf I, ⊤⁆ ≤ (d.componentModule I c.L).subgroupOf I := by
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hUI := span_le d hSI
  have hWI := (componentModule_le_span d c).trans hUI
  have hZI : d.Z ≤ I := (le_conjugateSpanBy d.Z I).trans hUI
  let _ : ((d.componentModule I c.L).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  apply commutator_le_of_seed _ _ (c.L.subgroupOf I) (d.S.subgroupOf I) (d.Z.subgroupOf I)
  · apply (map_le_map_iff_of_injective I.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hUI,
      map_subgroupOf_eq_of_le (component_le c), map_subgroupOf_eq_of_le hWI]
  · rw [span_eq_seed_sup_componentModule d c hn hI, subgroupOf_sup hZI hWI]
  · intro z hz s hs
    exact Subtype.ext (d.Z_le_centralizer_S hz s hs)
  · apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (component_le c),
      map_subgroupOf_eq_of_le hSI, ← MonoidHom.range_eq_map, range_subtype]
    exact hI.symm

/-- The component module has the same action kernel as the original span,
without assuming its recognition as a natural module. -/
theorem component_centralizer_eq_star_kernel [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
    (hchar : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    centralizer ((d.componentModule I c.L).subgroupOf I : Set I) = (d.starMap I).ker := by
  have hSI : d.S ≤ I := hP ▸ map_subtype_le _
  have hUI := span_le d hSI
  have hWI := (componentModule_le_span d c).trans hUI
  have hZS : d.Z ≤ d.S := (le_conjugateSpanBy d.Z d.M).trans
    (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)
  let _ := componentModule_elementary d c hchar P hP
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hWI
  let _ : ((d.componentModule I c.L).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  exact centralizer_eq_of_twoReduced ((d.UI I).subgroupOf I)
    ((d.componentModule I c.L).subgroupOf I) (comap_mono (componentModule_le_span d c))
    (span_commutator_le_component d c hn hI) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (d.starMap_ker (hZS.trans hSI)) (d.star_twoCore_eq_bot ⟨P, hP⟩ hZS)

open scoped IsMulCommutative
variable [Finite G] (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hchar : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)

include hchar P hP in
/-- The elementary abelian structure on the internal realization of `U_L`. -/
theorem component_internal_elementary :
    IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I) := by
  let _ := componentModule_elementary d c hchar P hP
  exact IsElementaryAbelian.subgroupOf
    ((componentModule_le_span d c).trans (span_le d (hP ▸ map_subtype_le _)))

variable [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]

/-- Conjugation on the actual component module, using the original star quotient.
The elementary instance is supplied by `component_internal_elementary`. -/
noncomputable def componentAction : Representation (ZMod 2) (d.Star I)
    (Additive ((d.componentModule I c.L).subgroupOf I)) := by
  let _ : ((d.componentModule I c.L).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  exact Representation.NormalElementaryQuotient.representation
    ((d.componentModule I c.L).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (component_centralizer_eq_star_kernel d c hn hI hchar P hP).symm

/-- Faithfulness precedes the classification of this representation. -/
theorem componentAction_faithful :
    Function.Injective (componentAction d c hn hI hchar P hP) := by
  let _ : ((d.componentModule I c.L).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  exact Representation.NormalElementaryQuotient.representation_injective
    ((d.componentModule I c.L).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (component_centralizer_eq_star_kernel d c hn hI hchar P hP).symm

/-- The action agrees with ambient conjugation by every original actor. -/
theorem componentAction_apply (i : I)
    (u : Additive ((d.componentModule I c.L).subgroupOf I)) :
    (((componentAction d c hn hI hchar P hP (d.starMap I i) u).toMul : I) : G) =
      (i : G) * ((u.toMul : I) : G) * (i : G)⁻¹ := by
  let _ : ((d.componentModule I c.L).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  exact congrArg I.subtype (Representation.NormalElementaryQuotient.representation_apply
    ((d.componentModule I c.L).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (component_centralizer_eq_star_kernel d c hn hI hchar P hP).symm i u)

/-- A nontrivial component inside the actual Thompson subgroup supplies an
FF-offender on `U_L`. The nontriviality is that of its actual star image. -/
theorem componentAction_isFFModule :
    Representation.BinaryOffender.IsFFModule (componentAction d c hn hI hchar P hP) := by
  let _ := c.star_quasisimple.simple
  have _ : Nontrivial (d.starImage I c.L) :=
    (QuotientGroup.mk'_surjective (center (d.starImage I c.L))).nontrivial
  have hL : d.starImage I c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let _ : ((d.componentModule I c.L).subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (componentModule_normalizes d c hn)
  apply Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    ((d.componentModule I c.L).subgroupOf I) (d.starMap I) (QuotientGroup.mk'_surjective _)
    (component_centralizer_eq_star_kernel d c hn hI hchar P hP).symm (⊤ : Subgroup I) le_top
  intro hJ
  apply hL
  apply (Subgroup.map_eq_bot_iff _).mpr
  have hJ' : (Stellmacher.elementaryAbelianMaxJ I).subgroupOf I ≤ (d.starMap I).ker := by
    rw [LocalData.thompson_subgroupOf]
    exact hJ
  exact (comap_mono c.le_thompson).trans hJ'

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition

end
