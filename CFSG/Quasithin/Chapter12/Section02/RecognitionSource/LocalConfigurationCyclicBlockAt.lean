module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlock
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At

/-!
# The cyclic block with structural input at the original G and T

The block argument uses structure only to normalize V by T and identify
C_T(V) with O₂(LT). The fundamental setup gives this identity with the
local normalization premise. The original simple action and displacement
argument then identifies [O₂(L),L] with V, and the existing intrinsic block
recognition supplies the literal quotient and its module.

These additive adapters preserve the universal block APIs. They feed the
same-G,T cyclic construction without requiring structure at other Sylow
subgroups or ambient groups.
Source: Aschbacher–Smith, 12.2.24 and its preceding paragraph, printed p.804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}

private theorem cyclic_sylow_centralizer_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  rw [D.fundamentalSetup_module, ho] at he
  simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he

/-- The original component commutator layer, using only structure at G,T. -/
theorem cyclic_component_commutator_eq_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d)
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
    (hc : Nat.card P = p)
    (hd : ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V) :
    ⁅L.pCoreIn 2, L⁆ = V := by
  let J := L ⊔ (T : Subgroup G)
  have hTV := ((structural L h).2.2 V D).1
  have hJV : J ≤ normalizer (V : Set G) := sup_le D.normalizes hTV
  have hUJ : U ≤ J := (S.core_le_sylow_of_prime_order hc).trans le_sup_right
  let a : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion hJV)
  let : IsSimpleGroup (MulAut V) := A.simple_aut h.quasisimple
  have ha : Function.Surjective a := by
    intro b
    obtain ⟨l,hl⟩ := A.componentAut_surjective D b
    exact ⟨⟨l,(show L ≤ J from le_sup_left) l.property⟩,hl⟩
  let Q := pCore 2 J
  let Z := V.subgroupOf J
  let X := L.subgroupOf J
  let E := U.subgroupOf J
  let : Z.Normal := normal_subgroupOf_of_le_normalizer hJV
  have hE : E.map a ≠ ⊥ := by
    intro he
    have hUC : U ≤ centralizer (V : Set G) := by
      intro x hx
      have hk : (⟨x,hUJ hx⟩ : J) ∈ a.ker :=
        (map_eq_bot_iff E).mp he hx
      have hk' : (⟨x,hJV (hUJ hx)⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker := hk
      rw [normalizerMonoidHom_ker] at hk'
      exact hk'
    have heq : U = U ⊓ V := by rw [← S.action_kernel, inf_eq_left.mpr hUC]
    have hh := congrArg (fun X : Subgroup G => Nat.card X) heq
    rw [S.core_card, S.hyperplane] at hh
    have hexp := (Nat.pow_right_injective (by decide : 1 < 2)) hh
    have hn := A.dimension.1
    omega
  have hdisp : ⁅Q,E⁆ ≤ Z := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    dsimp only [Q,E,Z]
    rw [map_commutator, map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (D.le_component.trans le_sup_left)]
    change ⁅J.pCoreIn 2,U⁆ ≤ V
    rw [← cyclic_sylow_centralizer_eq_core h D hTV]
    exact hd.trans inf_le_right
  have hpX : IsPPerfect 2 X := h.maximal_faithful.2.1.2.1.of_surjective
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.surjective
  have hk : IsPGroup 2 a.ker := by
    rw [show a.ker = pCore 2 J from A.joinAut_ker D hTV]
    exact pCore_isPGroup
  have hbound := commutator_le_of_pPerfect_simple_image a ha hk
    Q Z X E hpX hE hdisp
  have hb : ⁅J.pCoreIn 2,L⁆ ≤ V := by
    have hm := map_mono (f := J.subtype) hbound
    dsimp only [Q,X,Z] at hm
    simpa only [pCoreIn, map_commutator, map_subgroupOf_eq_of_le
      (show L ≤ J from le_sup_left), map_subgroupOf_eq_of_le
      (D.le_component.trans (show L ≤ J from le_sup_left))] using hm
  apply le_antisymm
  · exact (commutator_mono (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)) le_rfl).trans hb
  · rw [D.eq_commutator]
    exact commutator_mono D.le_componentCore le_rfl

/-- Source 12.2.24 on the unchanged component and intrinsic block quotient. -/
theorem linearTwoBlock_of_cyclic_core_displacement_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d)
    (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
    (hc : Nat.card P = p)
    (hd : ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V) :
    ChapterC.IsLinearTwoBlock L d :=
  linearTwoBlock_of_commutator_eq h D A
    (cyclic_component_commutator_eq_at h D structural A S hc hd)

/-- Discharge block recognition in the original cyclic analysis from local
structure. The construction and prime-order premises are supplied by SourceAt. -/
theorem cyclicLocalAnalysis_of_invariant_odd_and_prime_steps_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : NaturalLocalAnalysis T L V d)
    (oddStep : ∃ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v)
    (primeStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U :=
  cyclicLocalAnalysis_of_invariant_odd_steps
    (((structural L h).2.2 V D).1) oddStep primeStep
    (fun _ _ _ _ _ _ _ S hc hd =>
      linearTwoBlock_of_cyclic_core_displacement_at h D structural A S hc hd)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
