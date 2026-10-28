module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.TerminalSource
public import Theory.Representation.BinaryPermutation.SixTransitivity
public import Theory.Representation.PSL3Two.NaturalOrbits

/-!
# Point conjugacy from the actual natural component markings

The natural SL3(2) and A6 actions are transitive on nonzero vectors.
Transport through the literal component quotient and module coordinates
produces conjugators inside the original K. Once the original fixed line
C_V(L) belongs to that module, every nonidentity point is conjugate to its
fixed generator. The terminal contradiction therefore needs only this
containment, with its former all-points conjugacy premise discharged.

The component marking, exclusion of the five-dimensional row, unique
escaping choice and returning conjugate still require the 13.4.10–17 source
arguments, owned by qt-d-1341-nonsolvable-source. Earlier structural, fusion
and action-kernel inputs retain final discharge with qt-d-1341-fixed-core-source.
This conditional terminal application does not complete the branch.

Source: Aschbacher–Smith 13.4.17(3–4) and the final argument of 13.4.1,
printed pp.914–915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {K W : Subgroup G}

omit [Finite G] in
private theorem conjugator_of_transitive_marking
    {Q X : Type*} [Group Q] [AddCommGroup X] [Module (ZMod 2) X]
    (hKW : K ≤ normalizer (W : Set G)) (ρ : Representation (ZMod 2) Q X)
    (q : K →* Q) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative X)
    (he : ∀ (k : K) (w : W),
      (e (W.normalizerMonoidHom ⟨k.val,hKW k.property⟩ w)).toAdd =
        ρ (q k) (e w).toAdd)
    (htrans : ∀ x y : X, x ≠ 0 → y ≠ 0 → ∃ a : Q, ρ a x = y)
    (v w : W) (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ k ∈ K, MulAut.conj k v.val = w.val := by
  have hve : (e v).toAdd ≠ 0 := fun hh => hv (e.injective (hh.trans e.map_one.symm))
  have hwe : (e w).toAdd ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  obtain ⟨a,ha⟩ := htrans _ _ hve hwe
  obtain ⟨k,rfl⟩ := hq a
  exact ⟨k,k.property,congrArg Subtype.val
    (e.injective (Multiplicative.toAdd.injective ((he k v).trans ha)))⟩

omit [Finite G] in
/-- The two fixed-free source rows give transitivity under the original K. -/
theorem component_nonzero_transitive
    (DK : ChosenModule T K W) {z : G} (marking : ComponentModuleAt DK z)
    (hfixed : W ⊓ centralizer (K : Set G) = ⊥)
    (v w : W) (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ k ∈ K, MulAut.conj k v.val = w.val := by
  cases marking with
  | linearThree q e he =>
    exact conjugator_of_transitive_marking DK.normalizes BinaryLinearThree.W
      (q.toMonoidHom.comp (QuotientGroup.mk' _))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he
      BinaryLinearThree.natural_transitive_nonzero v w hv hw
  | naturalSix q e he =>
    exact conjugator_of_transitive_marking DK.normalizes
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))
      (q.toMonoidHom.comp (QuotientGroup.mk' _))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he
      BinaryPermutation.alternatingSix_natural_nonzero_transitive v w hv hw
  | coreSix mK _ => exact (mK.fixed_ne_bot hfixed).elim

omit [Finite G] in
/-- One original fixed generator in the natural component module supplies
all the actual ambient point conjugacies in source 13.4.17(4). -/
theorem component_points_of_fixed_line
    {L V : Subgroup G} {D : ChosenModule T L V} (m : CoreMarking D)
    (DK : ChosenModule T K W) {z : G} (marking : ComponentModuleAt DK z)
    (hfixed : W ⊓ centralizer (K : Set G) = ⊥)
    (hd : m.constant.val ∈ W) :
    ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w := by
  intro w hw hw1
  obtain ⟨k,hk,he⟩ := component_nonzero_transitive DK marking hfixed
    ⟨m.constant.val,hd⟩ ⟨w,hw⟩
    (fun hh => m.constant_ne_one (Subtype.ext (congrArg (fun a : W => a.val) hh)))
    (fun hh => hw1 (congrArg Subtype.val hh))
  exact isConj_iff.mpr ⟨k,he⟩

/-- Terminal application: the marked natural rows and containment of the
original fixed line discharge the separate all-points conjugacy premise. -/
theorem false_of_terminal_component_fixed_line
    {L V : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (K W : Subgroup G) (DK : ChosenModule T K W)
    (hd : m.constant.val ∈ W)
    (y : G) (hAK : V.conjBy y ≤ normalizer (K : Set G))
    (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hgen : ⁅K,V.conjBy y⁆ = K)
    (marking : ComponentModuleAt DK z.val)
    (hfixed : W ⊓ centralizer (K : Set G) = ⊥) : False := by
  exact false_of_terminal_component_fixed_free h structural D m z hz1 hzT hzout
    hunique hfusion hkernel K W DK (component_points_of_fixed_line m DK marking hfixed hd)
    y hAK hAW hgen marking hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
