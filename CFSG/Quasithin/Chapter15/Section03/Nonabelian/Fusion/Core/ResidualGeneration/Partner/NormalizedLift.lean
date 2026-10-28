module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Placement
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Lifting the normalized product XU

In the proof of 15.3.56, J = ⟨U,Uʸ⟩ is normal in N_G(V₀) and
O₂(J) = FX. Consequently XU = O₂(J)U is normalized by N_H(V₀).
This is enough for the commutator-image lift in 15.3.59; normalization
of X itself is unnecessary. The restricted actor kernel in XU is U,
using X ∩ Q_H = E ≤ U. A commutator identity for the actor image then
places XU, and hence X, in K.

The actor identity is an explicit premise of the final conditional lemma.
This module proves the group-theoretic lift, not that marked identity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.56 and 15.3.59, printed pp.1147 and 1150.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core

variable {G : Type*} [Group G]

/-- The normalizer is relative to the actual H = C_G(Z). -/
def markedNormalizer (Z V₀ : Subgroup G) : Subgroup G :=
  centralizerH Z ⊓ normalizer (V₀ : Set G)

/-- The embedded two-residual of the relative marked normalizer. -/
def normalizerResidual (Z V₀ : Subgroup G) : Subgroup G :=
  (pResidual 2 (markedNormalizer Z V₀)).map (markedNormalizer Z V₀).subtype

/-- The normalizer information about J in 15.3.56 normalizes XU. -/
theorem markedNormalizer_normalizes_partner_sup_closure
    (Z ZS V₀ : Subgroup G) (y : G)
    (hJ : normalizer (V₀ : Set G) ≤ normalizer (pairI Z ZS y : Set G))
    (hcore : pairP Z ZS y = intersectionF Z ZS y ⊔ partnerX Z ZS y) :
    markedNormalizer Z V₀ ≤
      normalizer ((partnerX Z ZS y ⊔ closureU Z ZS : Subgroup G) : Set G) := by
  have he : pairP Z ZS y ⊔ closureU Z ZS = partnerX Z ZS y ⊔ closureU Z ZS := by
    rw [hcore]
    apply le_antisymm
    · exact sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left) le_sup_right
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  rw [← he]
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_inf
  · exact (inf_le_right.trans hJ).trans
      (normalizer_le_normalizer_characteristic_image (pairI Z ZS y)
        (pCore 2 (pairI Z ZS y)))
  · exact inf_le_left.trans (H_normalizes_closureU Z ZS)

/-- Taking the two-residual of a subgroup of H places it in O²(H). -/
theorem normalizerResidual_le_residual [Finite G] (Z V₀ : Subgroup G) :
    normalizerResidual Z V₀ ≤ residualK Z := by
  rw [show residualK Z = (pResidual 2 (centralizerH Z)).map (centralizerH Z).subtype from
    twoResidualAmbient_eq_pResidual _]
  let i := inclusion (show markedNormalizer Z V₀ ≤ centralizerH Z from inf_le_left)
  have hi := map_mono (f := (centralizerH Z).subtype) (map_pResidual_le 2 i)
  rw [map_map] at hi
  exact hi

/-- The actual actor image respects joins of subgroups lying in H. -/
theorem actorImage_sup (Z A B : Subgroup G)
    (hAH : A ≤ centralizerH Z) (hBH : B ≤ centralizerH Z) :
    actorImage Z (A ⊔ B) = actorImage Z A ⊔ actorImage Z B := by
  unfold actorImage
  rw [subgroupOf_sup hAH hBH, Subgroup.map_sup]

/-- Adding a subgroup of the actor kernel does not change the actor image. -/
theorem actorImage_sup_of_le_core (Z A B : Subgroup G)
    (hAH : A ≤ centralizerH Z) (hBH : B ≤ centralizerH Z) (hBQ : B ≤ coreQ Z) :
    actorImage Z (A ⊔ B) = actorImage Z A := by
  rw [actorImage_sup Z A B hAH hBH]
  have hb : actorImage Z B = ⊥ := by
    apply ((B.subgroupOf (centralizerH Z)).map_eq_bot_iff).mpr
    intro b hb
    exact (actorProjection_eq_one_iff Z b).mpr (hBQ hb)
  rw [hb, sup_bot_eq]

open scoped Pointwise in
/-- The source intersection determines the whole kernel in the normalized product. -/
theorem partner_sup_closure_inf_core (Z ZS : Subgroup G) (y : G)
    (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hXQ : partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y) :
    (partnerX Z ZS y ⊔ closureU Z ZS) ⊓ coreQ Z = closureU Z ZS := by
  apply le_antisymm
  · intro a ha
    have hp : a ∈ (partnerX Z ZS y : Set G) * (closureU Z ZS : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _
        (hXH.trans (H_normalizes_closureU Z ZS))]
      exact ha.1
    obtain ⟨x, hx, u, hu, rfl⟩ := hp
    have hxQ : x ∈ coreQ Z := by
      have h := (coreQ Z).mul_mem ha.2 ((coreQ Z).inv_mem (hUQ hu))
      simpa only [mul_inv_cancel_right] using h
    have hxE : x ∈ intersectionE Z ZS y := hXQ ▸ ⟨hx, hxQ⟩
    exact (closureU Z ZS).mul_mem hxE.1.1 hu
  · exact le_inf le_sup_right hUQ

/-- The marked commutator identity lifts through XU using the genuine
J-normalizer information. No normalizer hypothesis about X is assumed. -/
theorem partnerX_le_residual_of_normalizer_actor_commutator [Finite G]
    (Z ZS V₀ : Subgroup G) (y : G)
    (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hUK : closureU Z ZS ≤ residualK Z) (hUQ : closureU Z ZS ≤ coreQ Z)
    (hXQ : partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y)
    (hJ : normalizer (V₀ : Set G) ≤ normalizer (pairI Z ZS y : Set G))
    (hcore : pairP Z ZS y = intersectionF Z ZS y ⊔ partnerX Z ZS y)
    (himage : actorImage Z (partnerX Z ZS y) =
      ⁅actorImage Z (partnerX Z ZS y), actorImage Z (normalizerResidual Z V₀)⁆) :
    partnerX Z ZS y ≤ residualK Z := by
  let H := centralizerH Z
  let A := (partnerX Z ZS y ⊔ closureU Z ZS).subgroupOf H
  let B := (normalizerResidual Z V₀).subgroupOf H
  let K := (residualK Z).subgroupOf H
  let : K.Normal := residual_normal_in_H Z
  have hUH := hUK.trans (residual_le_H Z)
  have hBK : B ≤ K := fun _ hb => normalizerResidual_le_residual Z V₀ hb
  have hBN : normalizerResidual Z V₀ ≤ markedNormalizer Z V₀ := map_subtype_le _
  have hBA : B ≤ normalizer (A : Set H) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp
      (markedNormalizer_normalizes_partner_sup_closure Z ZS V₀ y hJ hcore (hBN hb)) (x : G)
  have hker : A ⊓ (actorProjection Z).ker ≤ K := by
    intro a ha
    apply hUK
    rw [← partner_sup_closure_inf_core Z ZS y hXH hUQ hXQ]
    exact ⟨ha.1, (actorProjection_eq_one_iff Z a).mp ha.2⟩
  have hAi : A.map (actorProjection Z) = actorImage Z (partnerX Z ZS y) :=
    actorImage_sup_of_le_core Z _ _ hXH hUH hUQ
  have hcomm : A.map (actorProjection Z) =
      ⁅A.map (actorProjection Z), B.map (actorProjection Z)⁆ := by
    rw [hAi]
    exact himage
  have hAK := le_of_commutator_image_of_normalized (actorProjection Z) A B K
    hBK hBA hcomm hker
  intro x hx
  exact hAK (show (⟨x, hXH hx⟩ : H) ∈ A from
    (le_sup_left : partnerX Z ZS y ≤ partnerX Z ZS y ⊔ closureU Z ZS) hx)

/-- Once the partner is lifted, the order-eight conclusion of 15.3.56(6)
exhausts the supplied order-eight residual Sylow actor image. -/
theorem residualSylow_actor_generated [Finite G]
    (T Z ZS : Subgroup G) (y t : G)
    (hTH : T ≤ centralizerH Z) (ht : t ∈ T)
    (hXT : partnerX Z ZS y ≤ T) (hXK : partnerX Z ZS y ≤ residualK Z)
    (hRcard : Nat.card (actorImage Z (residualSylow T Z)) = 8)
    (hXXcard : Nat.card (actorImage Z
      (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t)) = 8) :
    actorImage Z (residualSylow T Z) ≤ actorImage Z
      (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) := by
  have hX : partnerX Z ZS y ≤ residualSylow T Z := le_inf hXT hXK
  have hXt := conjugate_le_residualSylow T Z (partnerX Z ZS y) t ht hTH hX
  have hi : actorImage Z (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) ≤
      actorImage Z (residualSylow T Z) :=
    map_mono (fun _ hx => sup_le hX hXt hx)
  exact (eq_of_le_of_card_ge hi (by rw [hRcard, hXXcard])).ge

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
