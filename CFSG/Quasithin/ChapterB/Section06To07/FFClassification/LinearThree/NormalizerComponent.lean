module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ParabolicQuotient

/-!
# The repeated natural SL3 obstruction from the original normalizer action

Construct both invariant parabolics using the natural representation of the
actual N_H(L). The quotient to N_H(L)/C_H(L) is injective on the simple
perfect component, so the parabolic pair and prescribed Sylow intersection
pass to the automizer. Its earlier minimal-parabolic theorem now contradicts
the transported pair. The module itself is never quotiented by centralizer
scalars, and no descent of its representation is required.

Source: Aschbacher--Smith B.6.9, printed p.116, using B.6.8(3).
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Repeated natural action on the actual normalizer already excludes the SL3 branch;
centralizer scalars need not disappear on the module. -/
theorem component_normalizer_not_repeated_natural_three
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G)
    (ρ : Representation (ZMod 2) (normalizer (L : Set G)) V)
    (F : BinaryField) (r : ℕ) (hr : 0 < r) :
    ¬ IsRepeatedLinearNatural
      (ρ.comp (L.subgroupOf (normalizer (L : Set G))).subtype) F 3 r := by
  intro h
  let N := normalizer (L : Set G)
  let L₀ := L.subgroupOf N
  let q := NormalizerAction.quotient L
  let := hL.2
  have hcent : center L = ⊥ := by
    obtain hb | ht := IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) inferInstance
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  have hc : Function.Injective (NormalizerAction.componentMap L) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact (NormalizerAction.componentMap_ker L).trans hcent
  have hqL : Function.Injective (q.comp L₀.subtype) := by
    intro x y hxy
    have he : (⟨(x.val : G),x.property⟩ : L) = ⟨(y.val : G),y.property⟩ := hc hxy
    have hval : ((x.val : N) : G) = ((y.val : N) : G) :=
      congrArg (fun z : L => (z : G)) he
    exact Subtype.ext (Subtype.ext hval)
  obtain ⟨S₀,hS₀⟩ := component_normalizer_sylow T hL ho
  obtain ⟨S,hS,hmin⟩ := component_automizer_minimalParabolic T hP hL heven ho
  have hmap : (S : Subgroup _) = (S₀ : Subgroup N).map q := by rw [hS₀]; exact hS
  have hgen : L₀.map q ⊔ (S : Subgroup _) = ⊤ := by
    rw [hS]
    exact component_automizer_sylow_supplement T hL ho
  obtain ⟨P,Q,hPQ,hPe,hQe,hnP,hnQ,hiP,hiQ⟩ :=
    exists_sylow_invariant_linear_three_parabolics S₀ L₀ ρ F r hr h
  exact not_minimalParabolic_quotient_of_two_overgroups S₀ L₀ q hqL S hmap hgen
    P Q hPQ hPe hQe hnP hnQ hiP hiQ hmin

/-- The same original-normalizer obstruction for a single natural SL3 module. -/
theorem component_normalizer_not_natural_three
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G)
    (ρ : Representation (ZMod 2) (normalizer (L : Set G)) V)
    (F : BinaryField) :
    ¬ IsLinearNatural (ρ.comp (L.subgroupOf (normalizer (L : Set G))).subtype) F 3 := by
  rintro ⟨c⟩
  apply component_normalizer_not_repeated_natural_three T hP hL heven ho ρ F 1 (by decide)
  refine ⟨⟨c.groupEquiv, c.linearEquiv.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → F.Carrier)).symm, ?_⟩⟩
  intro g v
  funext i
  exact c.intertwines g v

end CFSG.Quasithin.ChapterB
