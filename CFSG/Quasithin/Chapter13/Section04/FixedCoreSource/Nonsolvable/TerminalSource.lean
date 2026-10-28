module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Terminal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CentralSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank
public import Theory.Representation.BinaryConjugationCoordinates
public import Theory.GroupAction.ElementaryEightActionRank

/-!
# Discharging the terminal natural-action and image-order premises

The literal conjugation kernel identifies the actor image with A/C_A(W).
The terminal corank bound makes that image have order at least eight. For
W of order eight, GL₃(2) gives the contradictory upper bound four. For the
natural A₆ module, normalization of K extends its original quotient marking
to an S₆ action; elementary two-rank bounds then force image order eight.
The common-fixed-space contradiction applies to this constructed action.
Finally K=[K,A] and W=[W,K] supply movement, so it is not an extra premise.

The component module classification, graph construction, unique escaping
weight, and returning conjugate that generates K remain with
qt-d-1341-nonsolvable-source. The fixed-point-free premise in the final
consumer is exactly the natural-row conclusion of 13.4.17(3), still to be
proved there. Earlier structural, fusion and fixed-line kernel inputs retain
final discharge with qt-d-1341-fixed-core-source. These terminal consumers
do not assert completion of the nonsolvable branch. Universal nonsolvability
at both original weight choices remains required for the earlier uniqueness.

Source: Aschbacher–Smith 13.4.13,13.4.17 and the final argument of13.4.1,
printed pp.911,913–915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
variable {G : Type*} [Group G]
/-- Extend the component marking to the actual normalizing actor, using the proved linear normalizer. -/
theorem exists_natural_six_actor
    (A K W : Subgroup G) (hAK : A ≤ normalizer (K : Set G))
    (hAW : A ≤ normalizer (W : Set G)) (hKW : K ≤ normalizer (W : Set G))
    (q : K →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (w : W),
      (e (W.normalizerMonoidHom ⟨k.val,hKW k.property⟩ w)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (q k) (e w).toAdd) :
    ∃ φ : A →* Equiv.Perm (Fin 6), ∀ (a : A) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val,hAW a.property⟩ w)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (φ a) (e w).toAdd := by
  let N := normalizer (W : Set G)
  let γ := (BinaryConjugationCoordinates.action W e).asGroupHom
  let B := K.subgroupOf N
  have hγK (k : K) : γ ⟨k.val,hKW k.property⟩ = alternatingHom (q k) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := e.surjective (Multiplicative.ofAdd v)
    have hw' : (e w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hw']
    exact (BinaryConjugationCoordinates.action_apply W e _ w).trans (he k w)
  have hmap : B.map γ = alternatingImage := by
    apply le_antisymm
    · rintro _ ⟨k,hk,rfl⟩
      exact ⟨q ⟨k.val,hk⟩,(hγK ⟨k.val,hk⟩).symm⟩
    · rintro _ ⟨k,rfl⟩
      obtain ⟨j,rfl⟩ := hq k
      exact ⟨⟨j.val,hKW j.property⟩,j.property,hγK j⟩
  let α : A →* N := inclusion hAW
  have hγmem (a : A) : γ (α a) ∈ symmetricImage := by
    rw [←normalizer_alternatingImage,←hmap]
    apply B.le_normalizer_map γ
    refine ⟨α a,?_,rfl⟩
    apply mem_normalizer_iff.mpr
    intro k
    change k.val ∈ K ↔ a.val * k.val * a.val⁻¹ ∈ K
    exact mem_normalizer_iff.mp (hAK a.property) k.val
  let β : A →* symmetricImage := (γ.comp α).codRestrict symmetricImage hγmem
  let eS : Equiv.Perm (Fin 6) ≃* symmetricImage :=
    MonoidHom.ofInjective symmetricHom_injective
  let φ : A →* Equiv.Perm (Fin 6) := eS.symm.toMonoidHom.comp β
  have hsf (a : A) : symmetricHom (φ a) = γ (α a) :=
    congrArg Subtype.val (eS.apply_symm_apply (β a))
  refine ⟨φ,?_⟩
  intro a w
  have hh := congrArg (fun f : LinearGroup => f.val (e w).toAdd) (hsf a)
  exact ((BinaryConjugationCoordinates.action_apply W e (α a) w).symm.trans hh.symm)
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G]
/-- The terminal corank bound forces the literal natural-six action image to have order eight. -/
theorem natural_action_card_eq_eight_of_corank
    (A W : Subgroup G) [IsElementaryAbelian 2 A]
    (hAW : A ≤ normalizer (W : Set G))
    (φ : A →* Equiv.Perm (Fin 6))
    (e : W ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (a : A) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        naturalRepresentation (Fin 6) (φ a) (e w).toAdd)
    (hr : 3 ≤ ChapterE.subgroupCorank A (A ⊓ centralizer (W : Set G))) :
    Nat.card φ.range = 8 := by
  have hidx := BinaryConjugationCoordinates.model_card_range A W hAW
    (naturalRepresentation (Fin 6)) (naturalRepresentation_injective (Fin 6) (by decide)) φ e he
  have hlog : 3 ≤ Nat.log 2 (Nat.card φ.range) := by
    rwa [hidx]
  have hlo : 8 ≤ Nat.card φ.range := Nat.pow_le_of_le_log Nat.card_pos.ne' hlog
  let : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hhi : Nat.card φ.range ≤ 8 :=
    (primeRank_le_iff_elementary_card_le _).mp
      BinaryNaturalDual.FiveActors.ModuleGeometry.symmetric_six_rank_le_three φ.range inferInstance
  exact le_antisymm hhi hlo

open Chapter12.Section02
variable [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked terminal contradiction without an assumed image order. -/
theorem false_of_marked_natural_terminal_without_image_order
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
    (W : Subgroup G) (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hmove : ¬ W ≤ centralizer (V.conjBy y : Set G))
    (φ : V.conjBy y →* Equiv.Perm (Fin 6))
    (e : W ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (a : V.conjBy y) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        naturalRepresentation (Fin 6) (φ a) (e w).toAdd) : False := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  have hr := m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hunique
  have hu := m.terminal_intersection_centralizes h structural hfusion hkernel W hpoints y hAW
  have hf := CoreMarking.terminal_corank_and_fixed_subgroups hr W y hu hmove
  have hcard := natural_action_card_eq_eight_of_corank (V.conjBy y) W hAW φ e he hf.1
  exact false_of_natural_image_and_fixed_subgroups (V.conjBy y) W hAW φ e he hcard
    (fun B hB hcor => (hf.2 B hB hcor).trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable


namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Subgroup Theory.GroupTheory Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem moves_of_component_generation (K A W : Subgroup G)
    (hKW : K ≤ normalizer (W : Set G)) (hgen : ⁅K,A⁆ = K)
    (hfull : W = ⁅W,K⁆) (hne : W ≠ ⊥) : ¬ W ≤ centralizer (A : Set G) := by
  intro hc
  have hKN : K ≤ normalizer (centralizer (W : Set G) : Set G) :=
    hKW.trans (normalizer_le_normalizer_centralizer W)
  have hKC : K ≤ centralizer (W : Set G) := by
    rw [←hgen]
    exact (commutator_mono le_rfl (le_centralizer_iff.mp hc)).trans
      (le_normalizer_iff_commutator_le_right.mp hKN)
  exact hne (hfull.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKC)))

/-- The natural-three row contradicts the actual terminal corank bound. -/
theorem false_of_terminal_eight
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
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hmove : ¬ W ≤ centralizer (V.conjBy y : Set G))
    (hW : Nat.card W = 8) : False := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  have hr := m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hunique
  have hu := m.terminal_intersection_centralizes h structural hfusion hkernel W hpoints y hAW
  have hf := CoreMarking.terminal_corank_and_fixed_subgroups hr W y hu hmove
  have hi := elementary_eight_centralizer_index_le_four (V.conjBy y) W hAW hW
  have hh : ChapterE.subgroupCorank (V.conjBy y)
      (V.conjBy y ⊓ centralizer (W : Set G)) ≤ 2 :=
    (Nat.log_mono_right hi).trans (by decide)
  omega

/-- The natural-six component supplies its ambient action, its image size, and its movement; no separate witnesses are assumed. -/
theorem false_of_terminal_natural_six_component
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
    (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAK : V.conjBy y ≤ normalizer (K : Set G))
    (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hgen : ⁅K,V.conjBy y⁆ = K)
    (q : K →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (w : W),
      (e (W.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ w)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (q k) (e w).toAdd) : False := by
  obtain ⟨φ,hφ⟩ := exists_natural_six_actor (V.conjBy y) K W hAK hAW DK.normalizes q hq e he
  exact false_of_marked_natural_terminal_without_image_order h structural D m z hz1 hzT hzout
    hunique hfusion hkernel W hpoints y hAW
    (moves_of_component_generation K (V.conjBy y) W DK.normalizes hgen DK.eq_commutator DK.ne_bot)
    φ e hφ
/-- The actual 13.4.10 component marking feeds the terminal proof once the
13.4.17 graph argument has excluded the fixed core row. -/
theorem false_of_terminal_component_fixed_free
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
    (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAK : V.conjBy y ≤ normalizer (K : Set G))
    (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hgen : ⁅K,V.conjBy y⁆ = K)
    (marking : ComponentModuleAt DK z.val)
    (hfixed : W ⊓ centralizer (K : Set G) = ⊥) : False := by
  cases marking with
  | linearThree _ e _ =>
    let := DK.elementary
    have hc : Nat.card W = 8 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 3 → ZMod 2) = 8
      simp
    exact false_of_terminal_eight h structural D m z hz1 hzT hzout hunique hfusion hkernel
      W hpoints y hAW
      (moves_of_component_generation K (V.conjBy y) W DK.normalizes hgen DK.eq_commutator DK.ne_bot) hc
  | naturalSix q e he =>
    exact false_of_terminal_natural_six_component h structural D m z hz1 hzT hzout
      hunique hfusion hkernel K W DK hpoints y hAK hAW hgen
      (q.toMonoidHom.comp (QuotientGroup.mk' (Section08.TransvectionRecognition.Component.ModelExtension.centralCore K)))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he
  | coreSix mK _ => exact mK.fixed_ne_bot hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
