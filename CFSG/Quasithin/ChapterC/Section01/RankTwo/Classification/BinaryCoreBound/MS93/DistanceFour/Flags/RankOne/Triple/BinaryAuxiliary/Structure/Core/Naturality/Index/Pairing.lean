module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic
/-!
# Bounding the auxiliary core by its commutator pairing

Modulo Z, the commutators of D and K are multiplicative in both variables
when D and K centralize X/Z. If D/U has order at most two and [U,K] ≤ Z,
evaluation at one coset representative generates the entire X/Z. The
kernel contains Q whenever [D,Q] ≤ Z, giving |X/Z| ≤ |K/(K ∩ Q)|.
Normality is required only for Z inside X.

This is the final size calculation for Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), (4.6.8), printed p.907.
The source application separately proves the fixed-preimage index bound
and supplies the literal parabolic core K/Q_alpha of order four.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreIndex

private theorem quotient_conjugate_eq {G : Type*} [Group G]
    (E X Z : Subgroup G) [(Z.subgroupOf X).Normal]
    (hZX : Z ≤ X) (hEX : ⁅E,X⁆ ≤ Z) (e : E) (x : X) :
    ∃ hx : (e : G) * (x : G) * (e : G)⁻¹ ∈ X,
      QuotientGroup.mk' (Z.subgroupOf X) ⟨_, hx⟩ =
        QuotientGroup.mk' (Z.subgroupOf X) x := by
  have hc := hEX (commutator_mem_commutator e.property x.property)
  have hx : (e : G) * (x : G) * (e : G)⁻¹ ∈ X := by
    have hh := X.mul_mem (hZX hc) x.property
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  refine ⟨hx, QuotientGroup.eq_iff_div_mem.mpr ?_⟩
  change (e:G) * (x:G) * (e:G)⁻¹ / (x:G) ∈ Z
  simpa only [div_eq_mul_inv, commutatorElement_def] using hc

private theorem exists_pairing {G : Type*} [Group G]
    (D K X Z : Subgroup G) [(Z.subgroupOf X).Normal]
    [IsMulCommutative (X ⧸ Z.subgroupOf X)]
    (hZX : Z ≤ X) (hDK : ⁅D,K⁆ ≤ X)
    (hDX : ⁅D,X⁆ ≤ Z) (hKX : ⁅K,X⁆ ≤ Z) :
    ∃ f : D →* (K →* (X ⧸ Z.subgroupOf X)), ∀ d k,
      f d k = QuotientGroup.mk' (Z.subgroupOf X)
        ⟨⁅(d : G),(k : G)⁆, hDK (commutator_mem_commutator d.property k.property)⟩ := by
  let q := QuotientGroup.mk' (Z.subgroupOf X)
  let c (d : D) (k : K) : X :=
    ⟨⁅(d : G),(k : G)⁆, hDK (commutator_mem_commutator d.property k.property)⟩
  let f : D →* (K →* (X ⧸ Z.subgroupOf X)) := {
    toFun d := {
      toFun k := q (c d k)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        change ⁅(d:G),1⁆ ∈ Z
        simp
      map_mul' k l := by
        obtain ⟨hc, he⟩ := quotient_conjugate_eq K X Z hZX hKX k (c d l)
        have hh : c d (k*l) = c d k * ⟨(k:G) * c d l * (k:G)⁻¹, hc⟩ := by
          apply Subtype.ext
          simpa only [c, Subgroup.coe_mul, mul_assoc] using
            commutatorElement_mul_right_eq_mul_conj (d:G) (k:G) (l:G)
        rw [hh, map_mul, he] }
    map_one' := by
      ext k
      apply (QuotientGroup.eq_one_iff _).mpr
      change ⁅(1:G),(k:G)⁆ ∈ Z
      simp
    map_mul' d e := by
      ext k
      obtain ⟨hc, he⟩ := quotient_conjugate_eq D X Z hZX hDX d (c e k)
      have hh : c (d*e) k = ⟨(d:G) * c e k * (d:G)⁻¹, hc⟩ * c d k := by
        apply Subtype.ext
        exact commutatorElement_mul_left_eq_conj_mul (d:G) (e:G) (k:G)
      change q (c (d*e) k) = q (c d k) * q (c e k)
      rw [hh, map_mul, he, mul_comm] }
  exact ⟨f, fun _ _ => rfl⟩

/-- If one binary coset generates D/U, the commutator pairing is generated
by evaluation at one representative. Its image is bounded by K/Q. -/
theorem index_le_of_fixed_index_le_two {G : Type*} [Group G]
    (D U K Q X Z : Subgroup G) [Finite D] [Finite K] [Finite X]
    [(Z.subgroupOf X).Normal] [IsMulCommutative (X ⧸ Z.subgroupOf X)]
    (hX : X = ⁅D,K⁆ ⊔ Z) (hUK : ⁅U,K⁆ ≤ Z) (hDQ : ⁅D,Q⁆ ≤ Z)
    (hDX : ⁅D,X⁆ ≤ Z) (hKX : ⁅K,X⁆ ≤ Z)
    (hi : U.relIndex D ≤ 2) : Z.relIndex X ≤ Q.relIndex K := by
  have hZX : Z ≤ X := hX ▸ le_sup_right
  have hDK : ⁅D,K⁆ ≤ X := hX ▸ le_sup_left
  by_cases hone : U.relIndex D = 1
  · have hDZ : ⁅D,K⁆ ≤ Z := (commutator_mono (relIndex_eq_one.mp hone) le_rfl).trans hUK
    have hXZ : X ≤ Z := hX ▸ sup_le hDZ le_rfl
    rw [relIndex_eq_one.mpr hXZ]
    exact Nat.one_le_iff_ne_zero.mpr index_ne_zero_of_finite
  have htwo : U.relIndex D = 2 := by
    have hpos : U.relIndex D ≠ 0 := index_ne_zero_of_finite
    omega
  obtain ⟨a, ha, _, hcosets⟩ := relIndex_eq_two_iff_exists_notMem_and.mp htwo
  obtain ⟨f, hf⟩ := exists_pairing D K X Z hZX hDK hDX hKX
  let aD : D := ⟨a,ha⟩
  let q := QuotientGroup.mk' (Z.subgroupOf X)
  have hU (d : D) (hd : (d:G) ∈ U) : f d = 1 := by
    ext k
    rw [hf]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hUK (commutator_mem_commutator hd k.property)
  have hr (d : D) (k : K) : f d k ∈ (f aD).range := by
    rcases hcosets d d.property with hda | hd
    · have hm : f d * f aD = 1 := (map_mul f d aD).symm.trans (hU (d*aD) hda)
      have he : f d k = (f aD k)⁻¹ := by
        have hh := congrArg (fun z : K →* (X ⧸ Z.subgroupOf X) => z k) hm
        exact mul_eq_one_iff_eq_inv.mp hh
      exact ⟨k⁻¹, (map_inv _ _).trans he.symm⟩
    · rw [hU d hd]
      exact one_mem _
  let C := ((f aD).range.comap q).map X.subtype
  have hXC : X ≤ C := by
    rw [hX]
    apply sup_le
    · apply commutator_le.mpr
      intro d hd k hk
      refine ⟨⟨_, hDK (commutator_mem_commutator hd hk)⟩, ?_, rfl⟩
      change q ⟨⁅d,k⁆, _⟩ ∈ (f aD).range
      rw [← hf ⟨d,hd⟩ ⟨k,hk⟩]
      exact hr ⟨d,hd⟩ ⟨k,hk⟩
    · intro z hz
      refine ⟨⟨z, hZX hz⟩, ?_, rfl⟩
      change q _ ∈ (f aD).range
      rw [show q ⟨z, hZX hz⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr hz]
      exact one_mem _
  have honto : Function.Surjective (f aD) := by
    intro w
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf X) w
    obtain ⟨y,hy,he⟩ := hXC x.property
    have hyx : y = x := Subtype.ext he
    subst y
    exact hy
  have hQ : Q.subgroupOf K ≤ (f aD).ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hf]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hDQ (commutator_mem_commutator ha hk)
  change Nat.card (X ⧸ Z.subgroupOf X) ≤ Q.relIndex K
  have hcard : (f aD).ker.index = Nat.card (X ⧸ Z.subgroupOf X) := by
    rw [index_ker, MonoidHom.range_eq_top.mpr honto, card_top]
  rw [← hcard]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Q.subgroupOf K).index_ne_zero_of_finite)
    (index_dvd_of_le hQ)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreIndex
