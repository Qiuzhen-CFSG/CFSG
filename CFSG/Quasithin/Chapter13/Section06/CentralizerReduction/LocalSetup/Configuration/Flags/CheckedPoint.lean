module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Relabel
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Stellmacher.OmegaOneCenterMap

/-!
# The marked central point in the checked centralizer

An aligned flag puts z in the omega-center of T. Independently of alignment,
the actual a belongs to C_T(v), since the binary core is abelian and V ≤ T.
The coordinate displacement by v proves that its image in the range of the
literal map C_T(v) → C_G(v)/⟨v⟩ is central; injectivity of the module map
and the distinct coordinate supports prove that this image is nonidentity.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926,
the paragraph before Lemma 13.6.4 and the observation following it.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry Stellmacher
open FlagCoordinates
variable {G : Type*} [Group G] {L V : Subgroup G}

theorem Marking.markedZ_pow_two (s : Marking L V) : markedZ s ^ 2 = 1 := by
  change s.map (Multiplicative.ofAdd z) ^ 2 = 1
  rw [← map_pow, show (Multiplicative.ofAdd z) ^ 2 = 1 by
    rw [pow_two]
    change Multiplicative.ofAdd (z + z) = 1
    rw [show z + z = 0 by
      apply Subtype.ext; ext i; fin_cases i <;> decide]; rfl, map_one]

/-- An aligned source flag gives the flag marking, including its omega-center point. -/
def FlagSource.mark [Finite G] {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂)
    (hz : zpowers (markedZ d.module) = V₁)
    (hv : markedV d.module ∈ V₂) (hv₁ : markedV d.module ∉ V₁) :
    FlagMarking T L V V₁ V₂ where
  module := d.module
  action_kernel := d.action_kernel
  line_eq := hz
  vector_mem := hv
  vector_not_mem := hv₁
  z_central := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨d.V_le_T (map_mem d.module _), d.module.markedZ_pow_two, ?_⟩
    intro t ht
    have hn := d.one_invariant ht
    rw [← hz, normalizer_zpowers_eq_centralizer_of_order_two _
      (orderOf_eq_prime d.module.markedZ_pow_two (markedZ_ne_one d.module))] at hn
    exact mem_centralizer_singleton_iff.mp hn

/-- The actual a belongs to C_T(v), using V ≤ T. -/
def FlagSource.checkedPoint {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) : Tv (T : Subgroup G) (markedV d.module) :=
  ⟨markedA d.module, d.V_le_T (map_mem d.module _), by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [markedA, markedV, map_mul] using congrArg d.module.map
      (mul_comm (Multiplicative.ofAdd a) (Multiplicative.ofAdd v))⟩

@[simp] theorem FlagSource.checkedPoint_val {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) : (d.checkedPoint : G) = markedA d.module := rfl

/-- No collapse of a occurs in the literal quotient C_G(v)/⟨v⟩. -/
theorem FlagSource.checkedPoint_ne_one {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) :
    (checkedSylowMap (T : Subgroup G) (markedV d.module)).rangeRestrict d.checkedPoint ≠ 1 := by
  intro he
  have hq := congrArg Subtype.val he
  have ha : (inclusion inf_le_right d.checkedPoint : Gv (markedV d.module)) ∈
      vLine (markedV d.module) := (QuotientGroup.eq_one_iff _).mp hq
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ha
  have hG : markedV d.module ^ k = markedA d.module := congrArg Subtype.val hk
  apply a_not_mem_vline
  apply mem_zpowers_iff.mpr
  refine ⟨k, d.module.injective ?_⟩
  rw [map_zpow]
  exact hG

/-- The image of a is central in the actual checked image of C_T(v). -/
theorem FlagSource.checkedPoint_central {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) :
    (checkedSylowMap (T : Subgroup G) (markedV d.module)).rangeRestrict d.checkedPoint ∈
      center (checkedSylowMap (T : Subgroup G) (markedV d.module)).range := by
  let q := checkedSylowMap (T : Subgroup G) (markedV d.module)
  let vT : Tv (T : Subgroup G) (markedV d.module) :=
    ⟨markedV d.module, d.V_le_T (map_mem d.module _), mem_centralizer_singleton_iff.mpr rfl⟩
  have hvq : q vT = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)
  apply mem_center_iff.mpr
  intro u
  obtain ⟨t, rfl⟩ := q.rangeRestrict_surjective u
  apply Subtype.ext
  change q t * q d.checkedPoint = q d.checkedPoint * q t
  let n : normalizer (V : Set G) := ⟨t, d.T_normalizes t.property.1⟩
  have hv : rho (d.normalizerAction n) v = v := by
    apply Multiplicative.ofAdd.injective
    apply d.module.injective
    rw [← d.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp t.property.2)
  have hmove := a_displacement (d.normalizerAction n) hv
  have hconj := d.normalizer_equivariant n a
  have hd : t * d.checkedPoint * t⁻¹ = d.checkedPoint ∨
      t * d.checkedPoint * t⁻¹ = d.checkedPoint * vT := by
    rcases hmove with he | he
    · left
      apply Subtype.ext
      exact hconj.trans (congrArg (fun x : Space => d.module.map (Multiplicative.ofAdd x)) he)
    · right
      apply Subtype.ext
      have hh := hconj.trans (congrArg (fun x : Space => d.module.map (Multiplicative.ofAdd x)) he)
      change (t : G) * markedA d.module * (t : G)⁻¹ = markedA d.module * markedV d.module
      rw [ofAdd_add, map_mul] at hh
      exact hh
  apply mul_inv_eq_iff_eq_mul.mp
  rcases hd with hd | hd
  · simpa only [map_mul, map_inv] using congrArg q hd
  · simpa only [map_mul, map_inv, hvq, mul_one] using congrArg q hd
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
