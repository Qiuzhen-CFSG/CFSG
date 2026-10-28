module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2OddFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.GroupAction.OddOrbitFixedPoints
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# Detecting external central involutions on a natural block

In a characteristic-two group, an involution centralizing a full Sylow
two-subgroup lies in the center of the two-core. Its orbit under a subnormal
block is odd and stays in this abelian normal subgroup. The displacement
lies in the block's actual natural module. A nontrivial odd actor in the
block has only central fixed points there, so the orbit-product argument
forces the original involution to centralize the entire block.

This supplies the external-element step in the natural-block exclusion
of Aschbacher--Smith14.6.9, printed p.1025. The original orbit and unique
maximal Sylow overgroup construct the odd actor in the source consumer.
-/

public section
open Subgroup Theory.GroupTheory MulAction
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow-central involution fixed by a nontrivial odd subgroup of the
natural block centralizes the entire block, including its central layers. -/
theorem IsL2EvenBlock.centralizes_of_sylow_and_odd_fixed
    (S : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (K : Subgroup G) (hK : IsBlock K) {n : ℕ} (hn : IsL2EvenBlock K n)
    (D : Subgroup G) (hDK : D ≤ K) (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥)
    (z : G) (hz2 : z ^ 2 = 1)
    (hzS : z ∈ centralizer (S : Set G)) (hzD : z ∈ centralizer (D : Set G)) :
    z ∈ centralizer (K : Set G) := by
  let Q := pCore 2 G
  let V := (center Q).map Q.subtype
  let : V.Normal := inferInstanceAs ((center (pCore 2 G)).map (pCore 2 G).subtype).Normal
  let : IsMulCommutative V := map_isMulCommutative (center Q) Q.subtype
  let ρ : G →* MulAut V :=
    V.normalizerMonoidHom.comp
      ((MonoidHom.id G).codRestrict (normalizer (V : Set G))
        (fun g => (normalizer_eq_top (H := V)).symm ▸ mem_top g))
  let : MulDistribMulAction G V := MulDistribMulAction.compHom V ρ
  have hzQ : z ∈ Q := by
    have hc := centralizer_generalizedFitting_le G
    rw [hf] at hc
    exact hc (centralizer_le (pCore_isPGroup.le_sylow_of_normal S) hzS)
  have hzV : z ∈ V := by
    refine ⟨⟨z,hzQ⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (hzS q (pCore_isPGroup.le_sylow_of_normal S q.property))
  let v : V := ⟨z,hzV⟩
  have hvD (d : D) : (d : G) • v = v := by
    apply Subtype.ext
    change (d : G) * z * (d : G)⁻¹ = z
    rw [hzD d d.property,mul_inv_cancel_right]
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  have hPS : (P : Subgroup K) ≤ stabilizer K v := by
    intro k hk
    rw [hP] at hk
    apply Subtype.ext
    change (k : G) * z * (k : G)⁻¹ = z
    rw [hzS k hk,mul_inv_cancel_right]
  have ho : Odd (Nat.card (orbit K v)) := by
    have hi : ¬ 2 ∣ (stabilizer K v).index :=
      fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPS))
    rw [Nat.card_congr (orbitEquivQuotientStabilizer K v)]
    exact Nat.not_even_iff_odd.mp (fun he => hi he.two_dvd)
  let U := (blockU K).map K.subtype
  have hdisp (k : K) : ((k : G) • v) / v ∈ U.subgroupOf V := by
    change ((k : G) * z * (k : G)⁻¹) / z ∈ U
    apply hK.ambient_core_commutator.le
    rw [commutator_comm]
    simpa only [commutatorElement_def,div_eq_mul_inv] using
      (commutator_mem_commutator k.property hzQ)
  have hfixed (w : V) (hw : w ∈ U.subgroupOf V)
      (hwD : ∀ d : D, (d : G) • w = w) : ∀ k : K, (k : G) • w = w := by
    obtain ⟨u,hu,he⟩ := hw
    change (u : G) = (w : G) at he
    have huD : u ∈ centralizer (D.subgroupOf K : Set K) := by
      intro d hd
      apply Subtype.ext
      have hh := congrArg Subtype.val (hwD ⟨d,hd⟩)
      change (d : G) * (w : G) * (d : G)⁻¹ = (w : G) at hh
      rw [←he] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hod : Odd (Nat.card (D.subgroupOf K)) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv]
    have hdn : D.subgroupOf K ≠ ⊥ := by
      intro heq
      have hh := congrArg (map K.subtype) heq
      rw [map_subgroupOf_eq_of_le hDK,Subgroup.map_bot] at hh
      exact hD hh
    have hc := hn.blockU_odd_fixed_le_center (D.subgroupOf K) hod hdn ⟨hu,huD⟩
    intro k
    apply Subtype.ext
    change (k : G) * (w : G) * (k : G)⁻¹ = (w : G)
    have hkc : (k : G) * (u : G) = (u : G) * (k : G) :=
      congrArg Subtype.val (mem_center_iff.mp hc k)
    rw [←he,hkc,mul_inv_cancel_right]
  have hfix := Theory.GroupAction.OddOrbitFixedPoints.fixed_of_odd_orbit K D
    (hDK.trans K.le_normalizer) (U.subgroupOf V) v hvD
    (Subtype.ext hz2) ho hdisp hfixed
  intro k hk
  have he := congrArg Subtype.val (hfix ⟨k,hk⟩)
  change k*z*k⁻¹=z at he
  exact mul_inv_eq_iff_eq_mul.mp he

end CFSG.Quasithin.ChapterC
