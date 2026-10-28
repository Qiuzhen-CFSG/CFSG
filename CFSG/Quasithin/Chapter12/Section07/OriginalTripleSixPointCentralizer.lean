module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixFullPoint
public import Theory.Representation.HexacodeAction.FullWeightVectorStabilizer
public import Theory.GroupTheory.PCoreSurjective

/-!
# The original triple-six point centralizer has quotient A5

Restrict the original component quotient map, including the chart's actor
automorphism, to the literal K intersect C_G(t). Its image is the actual
hexacode vector stabilizer. Its kernel is the pullback of the original O2(K),
and hence a two-group. The full-weight vector-stabilizer identification makes
that kernel exactly O2 of the original point centralizer. The resulting A5
marking retains its value on every original element.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.7.4(2–3),
printed pp.839–840. The natural quotient and nonsplit whole-module action
are separate calculations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original chart transports the actual conjugation action of every
element of K, retaining the quotient actor and its chart automorphism. -/
theorem tripleSixPointCoordinates_conjugate (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (k : K) (v : U) :
    ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
      (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
        ((tripleSixPointCoordinates D a v).toAdd))) : G) =
      (k : G) * (v : G) * (k : G)⁻¹ := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have he := a.intertwines (QuotientGroup.mk' (pCore 2 K) k) w
  change (D.spaceEquiv (Multiplicative.ofAdd (a.linearEquiv.symm
    (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
      (a.linearEquiv w)))) : G) = _
  rw [← he, a.linearEquiv.symm_apply_apply, D.spaceEquiv_apply]
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg (fun z : U => (z : G)) (D.spaceEquiv.apply_symm_apply v))
  change (k : G) * (w.val.toMul.val : G) * (k : G)⁻¹ = _
  rw [hw]

/-- The actor in the original chart fixes t exactly when its original lift
centralizes the same ambient element. -/
theorem tripleSixPoint_actor_fixes_iff (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (k : K) :
    Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
      (tripleSixPointCoordinates D a t).toAdd = (tripleSixPointCoordinates D a t).toAdd ↔
        (k : G) ∈ centralizer ({(t : G)} : Set G) := by
  let w : D.space := (D.spaceEquiv.symm t).toAdd
  have hw : (w.val.toMul.val : G) = (t : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg (fun z : U => (z : G)) (D.spaceEquiv.apply_symm_apply t))
  have he := a.intertwines (QuotientGroup.mk' (pCore 2 K) k) w
  change Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
    (a.linearEquiv w) = a.linearEquiv w ↔ _
  rw [← he, a.linearEquiv.injective.eq_iff]
  constructor
  · intro h
    have hh := congrArg (fun v : D.space => (v.val.toMul.val : G)) h
    change (k : G) * (w.val.toMul.val : G) * (k : G)⁻¹ = (w.val.toMul.val : G) at hh
    rw [hw] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
  · intro h
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (k : G) * (w.val.toMul.val : G) * (k : G)⁻¹ = (w.val.toMul.val : G)
    rw [hw]
    exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp h)

/-- Restriction of the actual quotient projection to the original point
centralizer, with the chart's actor twist retained. -/
@[expose] def tripleSixPointCentralizerProjection (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) :
    (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) →*
      Hexacode.fullWeightVectorStabilizer (tripleSixPointCoordinates D a t).toAdd :=
  ((a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
    (inclusion (inf_le_left : K ⊓ centralizer ({(t : G)} : Set G) ≤ K))).codRestrict _
      (fun c => (tripleSixPoint_actor_fixes_iff D a t ⟨c, c.property.1⟩).mpr c.property.2)

/-- The restricted projection still acts by conjugation by the same original
point-centralizing element on every original vector. -/
theorem tripleSixPointCentralizerProjection_conjugate (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U)
    (c : (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) (v : U) :
    ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
      (Hexacode.evenAction (tripleSixPointCentralizerProjection D a t c).val
        ((tripleSixPointCoordinates D a v).toAdd))) : G) =
      (c : G) * (v : G) * (c : G)⁻¹ :=
  tripleSixPointCoordinates_conjugate D a ⟨c, c.property.1⟩ v

/-- Every model vector stabilizer element lifts to this actual centralizer. -/
theorem tripleSixPointCentralizerProjection_surjective (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) :
    Function.Surjective (tripleSixPointCentralizerProjection D a t) := by
  intro g
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g.val)
  have hc : (k : G) ∈ centralizer ({(t : G)} : Set G) := by
    apply (tripleSixPoint_actor_fixes_iff D a t k).mp
    rw [hk, a.groupEquiv.apply_symm_apply]
    exact g.property
  refine ⟨⟨k, k.property, hc⟩, ?_⟩
  apply Subtype.ext
  change a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k) = g.val
  rw [hk, a.groupEquiv.apply_symm_apply]

/-- The kernel is the literal original component core restricted to C_K(t). -/
theorem tripleSixPointCentralizerProjection_ker (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) :
    (tripleSixPointCentralizerProjection D a t).ker =
      (pCore 2 K).comap (inclusion (inf_le_left : K ⊓ centralizer ({(t : G)} : Set G) ≤ K)) := by
  ext c
  change tripleSixPointCentralizerProjection D a t c = 1 ↔
    (⟨c, c.property.1⟩ : K) ∈ pCore 2 K
  rw [← QuotientGroup.eq_one_iff]
  constructor
  · intro hc
    have he : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c, c.property.1⟩) = 1 :=
      congrArg Subtype.val hc
    exact a.groupEquiv.injective (he.trans a.groupEquiv.map_one.symm)
  · intro hc
    apply Subtype.ext
    change a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c, c.property.1⟩) = 1
    exact (congrArg a.groupEquiv hc).trans a.groupEquiv.map_one

private theorem coordinate_ne_zero (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1) :
    (tripleSixPointCoordinates D a t).toAdd ≠ 0 := by
  intro h
  have hh : tripleSixPointCoordinates D a t = 1 := h
  exact ht ((tripleSixPointCoordinates D a).injective
    (hh.trans (tripleSixPointCoordinates D a).map_one.symm))

/-- For the original even-orbit t, the projection kernel is exactly its
point centralizer's two-core, not merely a subgroup of that core. -/
theorem tripleSixPointCentralizerProjection_ker_eq_core (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    (tripleSixPointCentralizerProjection D a t).ker =
      pCore 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  let w := (tripleSixPointCoordinates D a t).toAdd
  have hw : w ≠ 0 := coordinate_ne_zero D a t ht
  have hp := tripleSixPoint_full_weight D a t ht heven
  let e := Hexacode.fullWeightVectorStabilizerEquiv w hw hp
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (Hexacode.fullWeightVectorStabilizer w) := e.isSimpleGroup
  have hcore : pCore 2 (Hexacode.fullWeightVectorStabilizer w) = ⊥ := by
    rcases (inferInstance : (pCore 2 (Hexacode.fullWeightVectorStabilizer w)).Normal).eq_bot_or_eq_top
      with hb | htop
    · exact hb
    · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2)
        (G := Hexacode.fullWeightVectorStabilizer w)).exists_card_eq
      rw [htop, card_top, Hexacode.fullWeightVectorStabilizer_card w hw hp] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 60)
      exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3))
  have hk : IsPGroup 2 (tripleSixPointCentralizerProjection D a t).ker := by
    rw [tripleSixPointCentralizerProjection_ker]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hc := (tripleSixPointCentralizerProjection D a t).comap_pCore_of_ker_isPGroup
    (tripleSixPointCentralizerProjection_surjective D a t) hk
  rw [hcore, MonoidHom.comap_bot] at hc
  exact hc

/-- The exact A5 marking of C_K(t)/O2(C_K(t)), induced by the original chart. -/
def tripleSixPointCentralizerEquiv (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    ((K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      pCore 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) ≃* alternatingGroup (Fin 5) :=
  ((QuotientGroup.quotientMulEquivOfEq
    (tripleSixPointCentralizerProjection_ker_eq_core D a t ht heven).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (tripleSixPointCentralizerProjection D a t)
        (tripleSixPointCentralizerProjection_surjective D a t))).trans
    (Hexacode.fullWeightVectorStabilizerEquiv _ (coordinate_ne_zero D a t ht)
      (tripleSixPoint_full_weight D a t ht heven))

/-- The quotient marking agrees on every original point-centralizing element
with the six-plane permutation marking of its actual chart image. -/
theorem tripleSixPointCentralizerEquiv_mk (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (c : (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) :
    tripleSixPointCentralizerEquiv D a t ht heven (QuotientGroup.mk' _ c) =
      Hexacode.fullWeightVectorStabilizerA5 _ (tripleSixPoint_full_weight D a t ht heven)
        (tripleSixPointCentralizerProjection D a t c) := by
  unfold tripleSixPointCentralizerEquiv
  rfl

/-- The literal triple-six row identifies the original point-centralizer
quotient, with no independent recognition or kernel assumption. -/
theorem original_tripleSix_pointCentralizer (D : ChosenModule T K U)
    (eK : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hd : Module.finrank (ZMod 2) D.space = 6)
    (hf : Function.Injective D.quotientAction) (hi : IsIrreducible D.quotientAction)
    (t : G) (htU : t ∈ U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({t} : Set G)).relIndex K) :
    Nonempty (((K ⊓ centralizer ({t} : Set G) : Subgroup G) ⧸
      pCore 2 (K ⊓ centralizer ({t} : Set G) : Subgroup G)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨a⟩ := original_tripleSix_coordinates D eK hd hf hi
  exact ⟨tripleSixPointCentralizerEquiv D a ⟨t, htU⟩
    (fun h => ht (congrArg Subtype.val h)) heven⟩

end CFSG.Quasithin.Chapter12.Section07
