module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Kernel

/-!
# Faithful source coordinates and the possible outer twist

The natural action has precisely the centralizer kernel used in the source
bars. Its first-isomorphism-theorem comparison therefore identifies the
actual barred L-image with A₆. Given the independent parabolic conclusion
L/O₂(L) ≅ A₆, its two-core equals this kernel: the kernel is a normal
two-group, and equality follows by comparing indices. Comparing the two
quotient markings produces an arbitrary automorphism of A₆; no claim that
it is inner is made. The resulting conjugation formula preserves this twist.

Conversely, coordinates for the faithful quotient give the surjective
L-action needed by `FiveSeed.V_generated_by_flag`. The dimension-one flag
in the original V has order two by finite-vector-space cardinality.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.2.5(2), p.796; Notations 13.2.1 and 13.3.3, pp.877,885;
13.5.2(3) and Remark 13.5.3, pp.915–916; 13.8.6(6), p.948.
These are transport results. Applying the earlier natural-module theorem
to the genuine standing setup remains a source assembly obligation.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open BinaryPermutation
variable {G : Type*} [Group G]

/-- The natural action kernel is the two-core when their quotient orders agree. -/
theorem action_kernel_eq_core [Finite G] (L : Subgroup G) (α : L →* alternatingGroup (Fin 6))
    (hα : Function.Surjective α) (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    α.ker = pCore 2 L := by
  have hle : α.ker ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, kernel_isTwoGroup_of_quotientCore L α hα e⟩
  have hi : α.ker.index = (pCore 2 L).index := by
    change Nat.card (L ⧸ α.ker) = Nat.card (L ⧸ pCore 2 L)
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv).trans
      (Nat.card_congr e.toEquiv).symm
  have hc : Nat.card α.ker = Nat.card (pCore 2 L) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (pCore 2 L).index from Nat.card_pos)
    rw [← hi, α.ker.card_mul_index, hi, (pCore 2 L).card_mul_index]
  exact eq_of_le_of_card_ge hle hc.ge

/-- Comparison with a supplied quotient marking, allowing an outer automorphism. -/
noncomputable def actionTwist [Finite G] (L : Subgroup G)
    (α : L →* alternatingGroup (Fin 6)) (hα : Function.Surjective α)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) :=
  e.symm.trans ((QuotientGroup.quotientMulEquivOfEq
    (action_kernel_eq_core L α hα e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα))

/-- The comparison intertwines the actual projection of each element of L. -/
theorem actionTwist_apply [Finite G] (L : Subgroup G)
    (α : L →* alternatingGroup (Fin 6)) (hα : Function.Surjective α)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) (l : L) :
    actionTwist L α hα e (e (QuotientGroup.mk' (pCore 2 L) l)) = α l := by
  simp only [actionTwist, MulEquiv.trans_apply, e.symm_apply_apply]
  rfl

/-- The kernel of the specified natural action is the literal relative centralizer. -/
theorem NaturalCoordinates.kernel (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (c : NaturalCoordinates L V hn) :
    c.action.ker = actorKernel L V := by
  rw [← conjugationRepresentation_kernel L V hn]
  ext l
  have he (v : Additive V) :
      c.equiv (conjugationRepresentation L V hn l v) =
        alternatingNaturalRepresentation (Fin 6) (c.action l) (c.equiv v) :=
    c.conjugation l v.toMul
  constructor
  · intro hl
    apply LinearMap.ext
    intro v
    apply c.equiv.injective
    rw [he, show c.action l = 1 from hl, map_one]
    rfl
  · intro hl
    apply ComponentSieve.SixAndG2.NaturalSix.alternatingAction_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := c.equiv.surjective w
    rw [← he, show conjugationRepresentation L V hn l = 1 from hl, map_one]
    rfl

/-- The actual barred L-quotient in the original natural coordinates. -/
noncomputable def NaturalCoordinates.barEquiv (L V : Subgroup G)
    [IsElementaryAbelian 2 V] (hn : L ≤ normalizer (V : Set G))
    (c : NaturalCoordinates L V hn) :
    letI := actorKernel_normal L V hn
    (L ⧸ actorKernel L V) ≃* alternatingGroup (Fin 6) := by
  letI := actorKernel_normal L V hn
  exact (QuotientGroup.quotientMulEquivOfEq (c.kernel L V hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.action c.surjective)

/-- The barred comparison preserves the original quotient map. -/
theorem NaturalCoordinates.barEquiv_mk (L V : Subgroup G)
    [IsElementaryAbelian 2 V] (hn : L ≤ normalizer (V : Set G))
    (c : NaturalCoordinates L V hn) (l : L) :
    letI := actorKernel_normal L V hn
    c.barEquiv L V hn (QuotientGroup.mk' (actorKernel L V) l) = c.action l := by
  rfl

/-- The centralizer equals the two-core here as a proved consequence of the action. -/
theorem NaturalCoordinates.actorKernel_eq_core [Finite G]
    (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (c : NaturalCoordinates L V hn)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    actorKernel L V = pCore 2 L :=
  (c.kernel L V hn).symm.trans (action_kernel_eq_core L c.action c.surjective e)

/-- Conjugation in the original V retains the automorphism of the quotient marking. -/
theorem NaturalCoordinates.conjugation_twist [Finite G]
    (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (c : NaturalCoordinates L V hn)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) (l : L) (v : Additive V) :
    c.equiv (conjugationRepresentation L V hn l v) =
      alternatingNaturalRepresentation (Fin 6)
        (actionTwist L c.action c.surjective e (e (QuotientGroup.mk' (pCore 2 L) l)))
        (c.equiv v) := by
  rw [actionTwist_apply]
  exact c.conjugation l v.toMul

/-- Pull back faithful quotient coordinates to the actual surjective L-action. -/
noncomputable def coordinatesOfBar (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 6)) :
    letI := actorKernel_normal L V hn
    (β : (L ⧸ actorKernel L V) ≃* alternatingGroup (Fin 6)) →
    (∀ (l : L) (v : V),
      e (Additive.ofMul ⟨(l : G) * v * (l : G)⁻¹,
        (mem_normalizer_iff.mp (hn l.property) v).mp v.property⟩) =
      alternatingNaturalRepresentation (Fin 6) (β (QuotientGroup.mk' _ l))
        (e (Additive.ofMul v))) → NaturalCoordinates L V hn := by
  letI := actorKernel_normal L V hn
  intro β he
  exact {
    action := β.toMonoidHom.comp (QuotientGroup.mk' (actorKernel L V))
    surjective := β.surjective.comp (QuotientGroup.mk'_surjective _)
    equiv := e
    conjugation := he }

/-- The source dimension-one flag is an order-two subgroup of the original V. -/
theorem flag_card_of_dimension [Finite G]
    (V A : Subgroup G) [IsElementaryAbelian 2 V] (hAV : A ≤ V)
    (hdim : Module.finrank (ZMod 2) (AddSubgroup.toZModSubmodule 2
      (A.subgroupOf V).toAddSubgroup) = 1) :
    Nat.card A = 2 := by
  calc
    Nat.card A = Nat.card (A.subgroupOf V) :=
      Nat.card_congr (subgroupOfEquivOfLe hAV).symm.toEquiv
    _ = Nat.card (AddSubgroup.toZModSubmodule 2
        (A.subgroupOf V).toAddSubgroup) := rfl
    _ = 2 := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim, pow_one]

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking

end
