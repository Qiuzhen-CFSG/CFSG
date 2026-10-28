module
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Removing a central quotient kernel from a fixed preimage

A finite two-perfect actor acts idempotently on every two-subgroup it
normalizes. Consequently adjoining an actor-centralized normal subgroup to
the denominator does not enlarge its fixed preimage. This proves exact
transport of the fixed preimage through a quotient with actor-central kernel.

In MS93 (4.6.8)(3), printed p.906, this accounts for passage from the
stabilizer to its quotient by D_alpha; D_alpha centralizes the tilded actors.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {G H : Type*} [Group G] [Group H]

/-- The pointwise and commutator definitions of a fixed preimage agree. -/
theorem centralizerModulo_eq_commutatorPreimage (A E Z : Subgroup G) [Z.Normal] :
    centralizerModulo A E Z = commutatorPreimage A E Z := by
  rw [commutatorPreimage_eq_inf_comap_centralizer]
  rfl

/-- A two-perfect actor acquires no new fixed vectors by killing an actor-central kernel. -/
theorem remove_central_kernel [Finite G] (A E Z D : Subgroup G)
    [Z.Normal] [D.Normal] (hE : IsPPerfect 2 E) (hA : IsPGroup 2 A)
    (hEA : E ≤ normalizer A) (hD : D ≤ centralizer (E : Set G)) :
    commutatorPreimage A E (Z ⊔ D) = commutatorPreimage A E Z := by
  let C := commutatorPreimage A E (Z ⊔ D)
  have hEC : E ≤ normalizer C :=
    commutatorPreimage_normalized _ _ _ _ le_normalizer_of_normal
      hEA E.le_normalizer le_normalizer_of_normal
  have hDE : ⁅Z ⊔ D, E⁆ ≤ Z := by
    have hh : Z ⊔ D ≤ commutatorPreimage ⊤ E Z := by
      refine sup_le (le_commutatorPreimage le_top (commutator_le_left Z E)) ?_
      exact le_commutatorPreimage le_top
        ((commutator_eq_bot_iff_le_centralizer.mpr hD).le.trans bot_le)
    exact (commutator_mono hh le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  apply le_antisymm
  · apply le_commutatorPreimage (commutatorPreimage_le _ _ _)
    have hi := commutator_isPPerfect_idempotent E C hE
      (hA.to_le (commutatorPreimage_le _ _ _)) hEC
    rw [← hi]
    exact (commutator_mono
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal) le_rfl).trans hDE
  · exact le_commutatorPreimage (commutatorPreimage_le _ _ _)
      ((commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal).trans le_sup_left)

/-- Exact fixed-preimage transport, including the reverse lifting implication. -/
theorem map_commutatorPreimage [Finite G] (f : G →* H) (hf : Function.Surjective f)
    (A E Z : Subgroup G) [Z.Normal] (hE : IsPPerfect 2 E) (hA : IsPGroup 2 A)
    (hEA : E ≤ normalizer A) (hD : f.ker ≤ centralizer (E : Set G)) :
    (commutatorPreimage A E Z).map f =
      commutatorPreimage (A.map f) (E.map f) (Z.map f) := by
  let : (Z.map f).Normal := Normal.map inferInstance f hf
  apply le_antisymm
  · apply le_commutatorPreimage (map_mono (commutatorPreimage_le _ _ _))
    rw [← map_commutator]
    exact map_mono (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  · let C := A ⊓ (commutatorPreimage (A.map f) (E.map f) (Z.map f)).comap f
    have hC : C ≤ commutatorPreimage A E (Z ⊔ f.ker) := by
      apply le_commutatorPreimage inf_le_left
      rw [← comap_map_eq]
      apply map_le_iff_le_comap.mp
      rw [map_commutator]
      exact (commutator_mono (map_le_iff_le_comap.mpr inf_le_right) le_rfl).trans
        (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
    rw [remove_central_kernel A E Z f.ker hE hA hEA hD] at hC
    intro y hy
    obtain ⟨x, hx, rfl⟩ := commutatorPreimage_le _ _ _ hy
    exact ⟨x, hC ⟨hx, hy⟩, rfl⟩
/-- Images preserve an intersection when the quotient kernel in a common
containing subgroup is already in its first member. -/
theorem map_inf_of_kernel (f : G →* H) (A B T : Subgroup G)
    (hAT : A ≤ T) (hBT : B ≤ T) (hker : T ⊓ f.ker ≤ A) :
    (A ⊓ B).map f = A.map f ⊓ B.map f := by
  apply le_antisymm (map_inf_le A B f)
  rintro y ⟨⟨a, ha, hay⟩, b, hb, hby⟩
  have hdiff : b * a⁻¹ ∈ A := by
    apply hker
    refine ⟨T.mul_mem (hBT hb) (T.inv_mem (hAT ha)), ?_⟩
    change f (b * a⁻¹) = 1
    rw [map_mul, map_inv, hay, hby, mul_inv_cancel]
  have hbA : b ∈ A := by
    simpa only [inv_mul_cancel_right] using A.mul_mem hdiff ha
  exact ⟨b, ⟨hbA, hb⟩, hby⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
