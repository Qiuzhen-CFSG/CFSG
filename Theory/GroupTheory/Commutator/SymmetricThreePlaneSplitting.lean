module
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.SpecificGroups.SymmetricThree.CubicSelection

/-!
# Splitting an abelian two-group under a symmetric-three action

Suppose normal subgroups K and Z have Z abelian of two-power order,
K/C_K(Z) is S3, and [Z,K] has order four and meets C_Z(K) trivially.
Then Z = [Z,K] C_Z(K). The image of O²(K) has order three, so coprime
action splits Z over its residual commutator. Its fixed subgroup meets
[Z,K] trivially: an intersection of order two would be K-fixed, while
an intersection of order four would kill the nontrivial cubic action.
The residual-fixed subgroup is therefore fixed by all of K.

This supplies the whole-center splitting in Aschbacher--Smith 14.3.25,
printed p.1001. Normality is in the stated ambient group; no ambient
simple-group or classification assumptions enter this lemma.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem commutator_plane_splitting_of_coprime_residual_image
    (Z K : Subgroup G) [Z.Normal] [K.Normal] [IsMulCommutative Z]
    (hZ : IsPGroup 2 Z) (hDcard : Nat.card (⁅Z,K⁆ : Subgroup G) = 4)
    (hdis : Disjoint (⁅Z,K⁆ : Subgroup G) (Z ⊓ centralizer (K : Set G)))
    (hcop : let R := (pResidual 2 K).map K.subtype
      Nat.Coprime (Nat.card (Z.normalizerMonoidHom.comp
        (inclusion (show R ≤ normalizer (Z : Set G) from le_normalizer_of_normal))).range)
        (Nat.card Z))
    (hne : ⁅Z,(pResidual 2 K).map K.subtype⁆ ≠ ⊥) :
    Z = ⁅Z,K⁆ ⊔ (Z ⊓ centralizer (K : Set G)) := by
  let R := (pResidual 2 K).map K.subtype
  let D := ⁅Z,K⁆
  let C := Z ⊓ centralizer (R : Set G)
  let E := D ⊓ C
  have hRK : R ≤ K := map_subtype_le _
  have hRC : ⁅Z,R⁆ ≤ D := commutator_mono le_rfl hRK
  have hEcard : Nat.card E ∣ 4 := hDcard ▸ card_dvd_of_le (show E ≤ D from inf_le_left)
  have hEbot : E = ⊥ := by
    have cases : Nat.card E = 1 ∨ Nat.card E = 2 ∨ Nat.card E = 4 := by
      obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
        (show Nat.card E ∣ 2 ^ 2 by simpa using hEcard)
      interval_cases n
      · exact Or.inl (by simpa only [pow_zero] using he)
      · exact Or.inr (Or.inl (by simpa only [pow_one] using he))
      · exact Or.inr (Or.inr he)
    rcases cases with he | he | he
    · exact E.eq_bot_of_card_eq he
    · have hcent : E ≤ centralizer (K : Set G) := by
        apply le_centralizer_iff.mp
        exact (show K ≤ normalizer (E : Set G) from le_normalizer_of_normal).trans
          (normalizer_le_centralizer_of_card_two E he)
      have heb : E = ⊥ := by
        apply bot_unique
        intro x hx
        exact hdis.le_bot ⟨hx.1,hx.2.1,hcent hx⟩
      have hc : Nat.card E = 1 := by rw [heb]; simp
      omega
    · have hED : E = D := eq_of_le_of_card_ge inf_le_left (by rw [he,hDcard])
      have hDR : D ≤ centralizer (R : Set G) := by
        rw [←hED]
        exact inf_le_right.trans inf_le_right
      apply (hne ?_).elim
      apply le_bot_iff.mp
      rw [← commutator_isPPerfect_idempotent R Z
        (isPPerfect_embedded_pResidual 2 K) hZ le_normalizer_of_normal]
      exact (commutator_mono hRC le_rfl).trans
        (commutator_eq_bot_iff_le_centralizer.mpr hDR).le
  have hCK : C ≤ centralizer (K : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←hEbot]
    exact le_inf (commutator_mono inf_le_left le_rfl) (commutator_le_left C K)
  have hCeq : C = Z ⊓ centralizer (K : Set G) :=
    le_antisymm (le_inf inf_le_left hCK) (inf_le_inf_left Z (centralizer_le hRK))
  have hs := (commutator_centralizer_decomposition_of_coprime_image Z R
    le_normalizer_of_normal hcop).1
  apply le_antisymm
  · exact hs.symm.le.trans (sup_le (hRC.trans le_sup_left) (hCeq.le.trans le_sup_right))
  · exact sup_le (commutator_le_left Z K) inf_le_left

/-- The symmetric-three action splits off its fixed subgroup when its moving
plane has order four and no nonidentity globally fixed point. -/
theorem commutator_plane_splitting_of_symmetricThree
    (Z K : Subgroup G) [Z.Normal] [K.Normal] [IsMulCommutative Z]
    (hZ : IsPGroup 2 Z) (hDcard : Nat.card (⁅Z,K⁆ : Subgroup G) = 4)
    (hdis : Disjoint (⁅Z,K⁆ : Subgroup G) (Z ⊓ centralizer (K : Set G)))
    (model : Nonempty ((K ⧸ (centralizer (Z : Set G)).comap K.subtype) ≃*
      Equiv.Perm (Fin 3))) :
    Z = ⁅Z,K⁆ ⊔ (Z ⊓ centralizer (K : Set G)) := by
  let ρ : G →* MulAut Z := MulAut.conjNormal
  let f := ρ.comp K.subtype
  let R := (pResidual 2 K).map K.subtype
  let s := Z.normalizerMonoidHom.comp
    (inclusion (show R ≤ normalizer (Z : Set G) from le_normalizer_of_normal))
  have hk : f.ker = (centralizer (Z : Set G)).comap K.subtype := by
    ext k
    constructor
    · intro hk z hz
      have hh := congrArg (fun a : MulAut Z => (a ⟨z,hz⟩ : G)) hk
      change (k:G) * z * (k:G)⁻¹ = z at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hk
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      change (k:G) * (z:G) * (k:G)⁻¹ = (z:G)
      have hh : (k:G) * (z:G) = (z:G) * (k:G) := (hk z z.property).symm
      rw [hh,mul_inv_cancel_right]
  obtain ⟨e₀⟩ := model
  let e : f.range ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans e₀)
  have hs : s.range = (pResidual 2 f.range).map f.range.subtype := by
    have hsρ : s = ρ.comp R.subtype := by
      ext a z
      rfl
    rw [hsρ,MonoidHom.range_comp,range_subtype]
    change ((pResidual 2 K).map K.subtype).map ρ = _
    rw [map_map]
    change (pResidual 2 K).map (f.range.subtype.comp f.rangeRestrict) = _
    rw [←map_map,map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]
  have hc : Nat.card s.range = 3 := by
    rw [hs,card_map_of_injective f.range.subtype_injective]
    have hh := congrArg (fun A : Subgroup (Equiv.Perm (Fin 3)) => Nat.card A) (map_pResidual 2 e)
    rw [card_map_of_injective e.injective] at hh
    exact hh.trans Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card
  apply commutator_plane_splitting_of_coprime_residual_image Z K hZ hDcard hdis
  · change Nat.Coprime (Nat.card s.range) (Nat.card Z)
    obtain ⟨n,hn⟩ := hZ.exists_card_eq
    rw [hc,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  · intro hbot
    have hcentral := commutator_eq_bot_iff_le_centralizer.mp hbot
    have htriv : s = 1 := by
      ext a z
      change (a : G) * (z : G) * (a : G)⁻¹ = (z : G)
      rw [hcentral z.property a a.property,mul_inv_cancel_right]
    have hcard : Nat.card s.range = 1 := by rw [htriv]; simp
    omega
end Subgroup
