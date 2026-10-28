module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant.Quotient

/-!
# Recognizing a small subgroup invariant under the line residual

Work first in the actual quotient G_alpha/D_alpha. Residual cocycle
localization puts K's image in the natural Z-image. The line residual has
no fixed natural vector, so its action on K is nontrivial. Since K has
order at most four and the residual is two-perfect, K equals its residual
commutator. The quotient kernel is fixed, and Z has the same quotient image
as U, so this commutator lies in U already before taking the quotient.

This proves only the stated conditional recognition: normalization by the
actual ordered residual remains an input. Source: Meierfrankenfeld--Stellmacher,
Pushing up weak BN-pairs of rank two (1993), (4.3.2)(3), printed p.884.
-/
public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
open SmallInvariant Orientation.QuotientApplication
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- A small elementary subgroup of B, nonzero modulo the fixed core and
normalized by Q and the actual marked line residual, lies in U. -/
theorem small_invariant_le_U (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) (o : MovingOrientationAt a)
    (flag : SL) (K : Subgroup (FreeAmalgam R))
    (hKB : K ≤ B R a (geometry.Z_normal a))
    (hKe : IsElementaryAbelian 2 K) (hcard : Nat.card K ≤ 4)
    (hQK : Q R a ≤ normalizer (K : Set (FreeAmalgam R)))
    (hnot : ¬ K ≤ fixedCore R a)
    (hTK : lineResidual o flag ≤
      normalizer (K.subgroupOf (stabilizer R a) : Set (stabilizer R a))) :
    K ≤ U R a := by
  let S := stabilizer R a
  let K₀ := K.subgroupOf S
  let U₀ := (U R a).subgroupOf S
  let T := lineResidual o flag
  let q := quotientMap a
  let := finite_stabilizer R a
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (U_normalized a)
  have hKQ : K ≤ Q R a :=
    hKB.trans ((EdgeTransfer.B_le_radius hb a ha).trans (geometry.V_le_Q hb a ha))
  have hKS : K ≤ S := hKQ.trans (fun _ hx => hx.1)
  have himage : quotientImage a K ≤ quotientImage a (Z R a) :=
    quotient_small_invariant_le_Z source hb modules ha o flag K hKB hKe hcard hQK hTK
  have hKU : K₀ ≤ U₀ := by
    apply small_le_of_image_le q K₀ U₀ T
      ((Q_isPGroup R source.two_group source.core_le a ha).comap_subtype.to_le
        (show K₀ ≤ (Q R a).subgroupOf S from fun _ hx => hKQ hx))
      (lineResidual_isPPerfect source ha o flag) hTK
    · rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv]
      exact hcard
    · exact himage.trans_eq (quotientImage_Z_eq_U modules a ha)
    · change (quotientMap a).ker ≤ centralizer (T : Set S)
      rw [quotientMap, QuotientGroup.ker_mk', denominator_eq]
      exact inf_le_right.trans (centralizer_le
        (lineResidual_le_localResidual source ha o flag))
    · intro hc
      apply hnot
      apply (quotientImage_eq_bot_iff a K hKS).mp
      apply le_bot_iff.mp
      rw [← quotient_line_fixed_eq_bot modules ha o flag]
      exact le_inf himage hc
  intro k hk
  exact hKU (show (⟨k,hKS hk⟩ : S) ∈ K₀ from hk)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne
