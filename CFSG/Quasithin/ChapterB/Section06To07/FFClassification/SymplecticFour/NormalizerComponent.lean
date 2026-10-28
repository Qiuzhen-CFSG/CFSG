module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SymplecticFour.Component
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ParabolicQuotient

/-!
# The natural Sp4 obstruction from the original normalizer action

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
open ChapterK.Symplectic
variable {G F V : Type*} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Natural action on the actual normalizer already excludes the Sp4 branch;
centralizer scalars need not disappear on the module. -/
theorem component_normalizer_not_natural_symplectic_four
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) {L : Subgroup G}
    (hL : IsComponent G L) [IsSimpleGroup L] (heven : 2 ∣ Nat.card L)
    (ho : componentOrbit L (T : Subgroup G) = pResidual 2 G)
    (ρ : Representation (ZMod 2) (normalizer (L : Set G)) V)
    (hcard : 2 < Nat.card F) :
    ¬ Nonempty (NaturalIdentification (F := F)
      (ρ.comp (L.subgroupOf (normalizer (L : Set G))).subtype)) := by
  rintro ⟨h⟩
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
  obtain ⟨P,Q,hPQ,hPe,hQe,_,hnP,hnQ,hiP,hiQ⟩ :=
    exists_sylow_invariant_symplectic_parabolics S₀ L₀ ρ h hcard
  exact not_minimalParabolic_quotient_of_two_overgroups S₀ L₀ q hqL S hmap hgen
    P Q hPQ hPe hQe hnP hnQ hiP hiQ hmin
end CFSG.Quasithin.ChapterB
