module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Basic

/-!
# The actual edge action for the MS93 index calculations

Conjugation by Q_beta acts on Z_alpha through its normalization in the local
vertex stabilizer. The common centralizer equality identifies its kernel as
Q_alpha. The edge omega-center is exactly C_{Z_alpha}(Q_beta), since all
Z_alpha elements are involutions in Q_beta. Thus both groups occurring in the
edge index statements have genuine action and quotient interpretations.

This file constructs the faithful quotient action and identifies its fixed
subgroup; it does not assert the numerical conclusions of (4.6.5)--(4.6.6).
Source: Meierfrankenfeld--Stellmacher (1993), definitions on p.855,
(4.1) on p.881 and the edge calculations on pp.902--903.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common

omit common in
/-- The edge omega-center is one of the generators of the adjacent Z-layer. -/
theorem edge_Z_le (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    Z R b ≤ Z R a := by
  have hb : color R b ≠ false := fun hb => (adjacent_color_ne R hab) (ha.trans hb.symm)
  rw [Z, if_neg hb, Z, if_pos ha]
  exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)

/-- The source edge layer is exactly the fixed subgroup of the edge kernel
on the adjacent Z-layer. This gives the fixed subgroup used by the Z-index. -/
theorem edge_Z_eq_fixed (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) :
    Z R b = Z R a ⊓ centralizer (Q R b : Set (FreeAmalgam R)) := by
  have hb : color R b ≠ false := fun hb => (adjacent_color_ne R hab) (ha.trans hb.symm)
  apply le_antisymm
  · refine le_inf (edge_Z_le a b ha hab) ?_
    rw [Z, if_neg hb]
    intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  · rintro x ⟨hx, hxc⟩
    rw [Z, if_neg hb]
    apply mem_omegaCenter_iff.mpr
    have hZa : Z R a ≤ Q R b := by
      apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
      rw [geometry.distance_constant a ha,
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)]
      exact lt_trans (by decide : 1 < 2) common.large_distance
    have hxω : x ∈ omegaCenter (Q R a) := by
      change x ∈ X R a
      rwa [common.X_eq_Z a ha]
    exact ⟨hZa hx, (mem_omegaCenter_iff.mp hxω).2.1, hxc⟩

omit common in
/-- The literal conjugation action of the edge kernel on the adjacent Z-layer. -/
noncomputable def edgeAction (a b : Vertex R) (hab : Adjacent R a b) : Q R b →* MulAut (Z R a) :=
  (Z R a).normalizerMonoidHom.comp
    (inclusion ((show Q R b ≤ stabilizer R a from
      fun _ hx => hx.2 a (adjacent_symm R hab)).trans (Z_normalized R a)))

omit common in
/-- The action agrees with multiplication in the original free amalgam. -/
theorem edgeAction_apply (a b : Vertex R) (hab : Adjacent R a b)
    (g : Q R b) (z : Z R a) :
    (edgeAction a b hab g z : FreeAmalgam R) = g * z * g⁻¹ := rfl

/-- The common edge centralizer identity identifies the action kernel with Q_a. -/
theorem edgeAction_kernel (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) :
    (edgeAction a b hab).ker = (Q R a).subgroupOf (Q R b) := by
  ext g
  change edgeAction a b hab g = 1 ↔ (g : FreeAmalgam R) ∈ Q R a
  rw [← common.centralizer a b ha hab]
  constructor
  · intro hg
    refine ⟨g.property, ?_⟩
    intro z hz
    have hh := congrArg (fun f : MulAut (Z R a) => (f ⟨z, hz⟩ : FreeAmalgam R)) hg
    change (g : FreeAmalgam R) * z * (g : FreeAmalgam R)⁻¹ = z at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (g : FreeAmalgam R) * z * (g : FreeAmalgam R)⁻¹ = z
    rw [← hg.2 z z.property, mul_inv_cancel_right]

/-- Fixed points of the actual edge action are precisely the elements of Z_b. -/
theorem edgeAction_fixed_iff (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (z : Z R a) :
    (∀ g : Q R b, edgeAction a b hab g z = z) ↔ (z : FreeAmalgam R) ∈ Z R b := by
  rw [edge_Z_eq_fixed common a b ha hab]
  constructor
  · intro hz
    refine ⟨z.property, ?_⟩
    intro g hg
    have hh := congrArg Subtype.val (hz ⟨g, hg⟩)
    change g * (z : FreeAmalgam R) * g⁻¹ = z at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro hz g
    apply Subtype.ext
    change (g : FreeAmalgam R) * (z : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ = z
    rw [hz.2 g g.property, mul_inv_cancel_right]

omit common in
/-- The faithful action of the genuine quotient by the conjugation kernel.
The theorem edgeAction_kernel identifies this kernel with Q_a inside Q_b. -/
noncomputable def edgeQuotientAction (a b : Vertex R) (hab : Adjacent R a b) :
    Q R b ⧸ (edgeAction a b hab).ker →* MulAut (Z R a) :=
  QuotientGroup.kerLift (edgeAction a b hab)

omit common in
/-- Factoring out the computed action kernel gives a faithful action. -/
theorem edgeQuotientAction_injective (a b : Vertex R) (hab : Adjacent R a b) :
    Function.Injective (edgeQuotientAction a b hab) :=
  QuotientGroup.kerLift_injective _

omit common in
/-- The quotient action retains the original ambient conjugation formula. -/
theorem edgeQuotientAction_mk_apply (a b : Vertex R) (hab : Adjacent R a b)
    (g : Q R b) (z : Z R a) :
    (edgeQuotientAction a b hab (QuotientGroup.mk' (edgeAction a b hab).ker g) z :
      FreeAmalgam R) = g * z * g⁻¹ := rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
