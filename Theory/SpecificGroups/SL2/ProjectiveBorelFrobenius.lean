module

public import BenderSuzuki.Converse.PSL2
public import FeitThompson.BGsection3.lemma_3_1
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius Borels in the projective two-dimensional matrix group

The upper unipotents survive the central quotient injectively. The projective
diagonal subgroup has order `(q - 1) / gcd (q - 1) 2`, since precisely the
units whose square is one become scalar. Diagonal conjugation multiplies the
unipotent parameter by the square of the diagonal entry, so its projective
action is fixed-point-free away from the identity.

The join of these two subgroups is the existing upper triangular projective
Borel. The kernel is normal in this Borel, the two subgroups are complements,
and a nontrivial complement makes this a Frobenius group. All declarations
use the actual SL2 quotient by its center, and work in either characteristic.
For the odd parameters 25, 49, 31 and 127 the complement orders are respectively
12, 24, 15 and 63, as used by Aschbacher--Smith, G.7.2(2), printed pp.347--348
(combined manuscript, 1 March 2004).
-/

@[expose] public section

open BenderSuzuki.Converse Matrix
open scoped MatrixGroups IsMulCommutative Pointwise
namespace Matrix.ProjectiveSpecialLinearGroup.OddBorel

variable (F : Type*) [Field F]
/-- The upper transvection map followed by the actual central quotient. -/
def unipotentHom : Multiplicative F →* PSL(2,F) := (pi F).comp (uniHom F)
/-- The determinant-one diagonal map followed by the central quotient. -/
def torusHom : Fˣ →* PSL(2,F) := (pi F).comp (torHom F)
/-- The unipotent kernel inside PSL2. -/
def kernel : Subgroup PSL(2,F) := (unipotentHom F).range
/-- The projective diagonal complement inside PSL2. -/
def complement : Subgroup PSL(2,F) := (torusHom F).range

theorem unipotentHom_injective : Function.Injective (unipotentHom F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  have hc : uni t.toAdd ∈ Subgroup.center (SL2 F) := (QuotientGroup.eq_one_iff _).mp ht
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  change t = 1
  exact (show t.toAdd = 0 by simpa [scalar_apply] using he.symm)

theorem card_kernel : Nat.card (kernel F) = Nat.card F := by
  exact Nat.card_congr (MonoidHom.ofInjective (unipotentHom_injective F)).toEquiv.symm

instance kernel_commutative : IsMulCommutative (kernel F) := by
  change IsMulCommutative (unipotentHom F).range
  exact ⟨⟨fun x y => (MonoidHom.ofInjective (unipotentHom_injective F)).symm.injective
    (by simp only [map_mul, mul_comm])⟩⟩

theorem torusHom_eq_one_iff (a : Fˣ) : torusHom F a = 1 ↔ a ^ 2 = 1 := by
  change (QuotientGroup.mk (tor a) : PSL(2,F)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, he⟩
    have he00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) he
    have ha : r = (a : F) := by simpa [scalar_apply] using he00
    apply Units.ext
    simpa [ha] using hr
  · intro ha
    have ha' : (a : F) ^ 2 = 1 := congrArg Units.val ha
    refine ⟨(a : F), by simpa using ha', ?_⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalar_apply, tor_val, hinv]

theorem card_complement [Finite F] :
    Nat.card (complement F) = (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
  have hker : (torusHom F).ker = (powMonoidHom 2 : Fˣ →* Fˣ).ker := by
    ext a
    exact torusHom_eq_one_iff F a
  change Nat.card (torusHom F).range = _
  rw [← Subgroup.index_ker, hker, IsCyclic.index_powMonoidHom_ker, Nat.card_units]

theorem torus_conj_unipotent (a : Fˣ) (t : F) :
    torusHom F a * unipotentHom F (Multiplicative.ofAdd t) * (torusHom F a)⁻¹ =
      unipotentHom F (Multiplicative.ofAdd ((a : F)^2 * t)) := by
  change pi F (tor a) * pi F (uni t) * (pi F (tor a))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  have ht : tor a ∈ Borel F := Torus_le_Borel (by rw [Torus_eq_range]; exact ⟨a, rfl⟩)
  rw [Borel_conj_uni ht]
  rfl

theorem complement_normalizes : complement F ≤ Subgroup.normalizer (kernel F : Set PSL(2,F)) := by
  rintro _ ⟨a, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd ((a : F)^2 * t.toAdd), (torus_conj_unipotent F a t.toAdd).symm⟩
  · intro hu
    obtain ⟨t, ht⟩ := hu
    refine ⟨Multiplicative.ofAdd (((a⁻¹ : Fˣ) : F)^2 * t.toAdd), ?_⟩
    rw [← torus_conj_unipotent]
    change torusHom F a⁻¹ * unipotentHom F t * (torusHom F a⁻¹)⁻¹ = u
    rw [ht, map_inv]
    group

/-- Nonidentity projective diagonal matrices fix only the identity unipotent. -/
theorem fixedPointFree (c : complement F) (hc : c ≠ 1) (k : kernel F)
    (hk : (c : PSL(2,F)) * k * (c : PSL(2,F))⁻¹ = k) : k = 1 := by
  obtain ⟨a, ha⟩ := c.property
  obtain ⟨t, ht⟩ := k.property
  have ha2 : (a : F)^2 ≠ 1 := by
    intro h
    apply hc
    apply Subtype.ext
    rw [← ha, (torusHom_eq_one_iff F a).mpr (Units.ext h)]
    rfl
  have he : (a : F)^2 * t.toAdd = t.toAdd := by
    have he' : unipotentHom F (Multiplicative.ofAdd ((a : F)^2 * t.toAdd)) =
        unipotentHom F t := by
      rw [← torus_conj_unipotent]
      change torusHom F a * unipotentHom F t * (torusHom F a)⁻¹ = unipotentHom F t
      rw [ha, ht]
      exact hk
    exact congrArg Multiplicative.toAdd (unipotentHom_injective F he')
  have ht0 : t.toAdd = 0 := by
    have : ((a : F)^2 - 1) * t.toAdd = 0 := by linear_combination he
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha2)
  apply Subtype.ext
  rw [← ht, show t = 1 from ht0, map_one]
  rfl

instance kernel_nontrivial : Nontrivial (kernel F) :=
  (MonoidHom.ofInjective (unipotentHom_injective F)).injective.nontrivial

theorem disjoint_kernel_complement : Disjoint (kernel F) (complement F) := by
  apply Subgroup.disjoint_def.mpr
  intro g hgK hgC
  by_contra hg
  obtain ⟨k, hk⟩ := exists_ne (1 : kernel F)
  have hc : (⟨g, hgC⟩ : complement F) ≠ 1 := fun h => hg (congrArg Subtype.val h)
  apply hk
  apply fixedPointFree F ⟨g, hgC⟩ hc k
  have hcomm := congrArg Subtype.val (mul_comm (⟨g, hgK⟩ : kernel F) k)
  change g * (k : PSL(2,F)) = (k : PSL(2,F)) * g at hcomm
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- The subgroup generated by the unipotents and the projective torus. -/
def borel : Subgroup PSL(2,F) := kernel F ⊔ complement F

/-- This construction is the existing projective upper triangular Borel. -/
theorem borel_eq_PBorel : borel F = PBorel F := by
  rw [PBorel_eq_map, borel, kernel, complement, unipotentHom, torusHom,
    MonoidHom.range_comp, MonoidHom.range_comp, ← Torus_eq_range,
    ← Subgroup.map_sup]
  exact congrArg (fun H : Subgroup (SL2 F) => H.map (pi F)) Unip_sup_Torus

instance kernel_normal_in_borel : ((kernel F).subgroupOf (borel F)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
  exact sup_le (kernel F).le_normalizer (complement_normalizes F)

theorem kernel_isComplement :
    ((kernel F).subgroupOf (borel F)).IsComplement' ((complement F).subgroupOf (borel F)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.mpr
    intro x hx hy
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp (disjoint_kernel_complement F) hx hy
  · rw [Set.eq_univ_iff_forall]
    intro x
    have hx : (x : PSL(2,F)) ∈ (kernel F : Set PSL(2,F)) * (complement F : Set PSL(2,F)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (complement_normalizes F)]
      exact x.property
    obtain ⟨k, hk, c, hc, he⟩ := hx
    exact ⟨⟨k, (le_sup_left : kernel F ≤ borel F) hk⟩, hk,
      ⟨c, (le_sup_right : complement F ≤ borel F) hc⟩, hc, Subtype.ext he⟩

theorem card_kernel_in_borel :
    Nat.card ((kernel F).subgroupOf (borel F)) = Nat.card F := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show kernel F ≤ borel F from le_sup_left)).toEquiv, card_kernel]

theorem card_complement_in_borel [Finite F] :
    Nat.card ((complement F).subgroupOf (borel F)) =
      (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show complement F ≤ borel F from le_sup_right)).toEquiv, card_complement]

/-- The actual projective Borel is Frobenius when its complement is nontrivial. -/
theorem frobenius [Finite F] (hlarge : 1 < (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) :
    IsFrobeniusGroupWithKernelComplement
      ((kernel F).subgroupOf (borel F)) ((complement F).subgroupOf (borel F)) := by
  have hK : (kernel F).subgroupOf (borel F) ≠ ⊥ := by
    have hc := card_kernel_in_borel F
    intro hb
    rw [hb, Subgroup.card_bot] at hc
    exact (ne_of_gt (Finite.one_lt_card (α := F))) hc.symm
  have hC : (complement F).subgroupOf (borel F) ≠ ⊥ := by
    have hc := card_complement_in_borel F
    intro hb
    rw [hb, Subgroup.card_bot] at hc
    omega
  apply (lemma_3_1 _ _ hK hC (kernel_normal_in_borel F) (kernel_isComplement F)).mpr
  intro c hc
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hk.2
  apply Subtype.ext
  have hc' : (⟨c.val.val, c.property⟩ : complement F) ≠ 1 := by
    intro he
    apply hc
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : complement F => (x : PSL(2,F))) he
  exact congrArg (fun x : kernel F => (x : PSL(2,F))) (fixedPointFree F ⟨c.val.val, c.property⟩ hc'
    ⟨k.val, hk.1⟩ (by
      have he := congrArg Subtype.val hcomm
      change k.val * c.val.val = c.val.val * k.val at he
      change c.val.val * k.val * c.val.val⁻¹ = k.val
      rw [← he, mul_assoc, mul_inv_cancel, mul_one]))

end Matrix.ProjectiveSpecialLinearGroup.OddBorel
