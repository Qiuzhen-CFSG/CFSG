module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicOverlapSource
public import Theory.SpecificGroups.AlternatingSix.PGLNineOuterCentralizer

/-!
# Cubic centralizers of original involutory inverters

An involution inverting the literal field cubic has outer image in the
actual PGL₂(9) quotient. That image has centralizer order twenty. A cubic
commuting with the inverter cannot vanish in the full cubic kernel,
because the inverter acts there by inversion. Thus it would yield an
impossible cubic in the projective involution centralizer.

Source: Baumeister, A geometry for groups of J₃-type (2007), Lemma 2.4,
the cubic nonfusion argument on pp.495–496.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen
open Janko23.J3Recognition.Ambient

set_option maxHeartbeats 800000 in
/-- No original involutory inverter of the field cubic centralizes a cubic
in that same full normalizer. No splitting over the cubic kernel is assumed. -/
theorem literal_cubic_inverter_not_commute_three
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j)
    (r x : normalizer (zpowers (j cubic) : Set G))
    (hr : orderOf r = 2) (hi : (r : G) * j cubic * (r : G)⁻¹ = (j cubic)⁻¹)
    (hx : orderOf x = 3) : ¬ Commute r x := by
  intro hcomm
  let s := j cubic
  let N := normalizer (zpowers s : Set G)
  let Q := N ⧸ cubicNormalizerKernel s
  let q := QuotientGroup.mk' (cubicNormalizerKernel s)
  have hs : orderOf s = 3 := (orderOf_injective j hj.1 cubic).trans cubic_order
  obtain ⟨⟨eA⟩, ⟨e⟩⟩ := literal_field_cubic_projective P hc A C a j hj
  have hrq1 : q r ≠ 1 := by
    intro h
    have hrK := (QuotientGroup.eq_one_iff r).mp h
    have hd := (cubicNormalizerKernel s).orderOf_dvd_natCard hrK
    rw [hr, cubicNormalizerKernel_card s hs] at hd
    norm_num at hd
  have hrq : orderOf (q r) = 2 := orderOf_eq_prime
    (by rw [← map_pow, show r ^ 2 = 1 by simpa only [hr] using pow_orderOf_eq_one r,
      map_one]) hrq1
  have hrout : q r ∉ _root_.commutator Q := by
    rw [cubic_normalizer_quotient_commutator D.localType hc s hs eA,
      cubicQuotientInclusion_preimage]
    intro h
    have he : s = s⁻¹ := by
      change (r : G) * s * (r : G)⁻¹ = s⁻¹ at hi
      rw [mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right] at hi
      exact hi
    have htwo : s ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [he]
      exact inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one htwo
    norm_num [hs] at hd
  have hxq1 : q x ≠ 1 := by
    intro h
    have hxK := (QuotientGroup.eq_one_iff x).mp h
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hxK
    have hinv : (r : G) * (x : G) * (r : G)⁻¹ = (x : G)⁻¹ := by
      change s ^ n = (x : G) at hn
      rw [← hn]
      change (MulAut.conj (r : G)) (s ^ n) = (s ^ n)⁻¹
      rw [map_zpow]
      change ((r : G) * s * (r : G)⁻¹) ^ n = (s ^ n)⁻¹
      rw [hi, inv_zpow]
    have hfix : (r : G) * (x : G) * (r : G)⁻¹ = (x : G) := by
      have hmul : (r : G) * (x : G) = (x : G) * (r : G) :=
        congrArg (fun y : N => (y : G)) hcomm.eq
      rw [hmul, mul_inv_cancel_right]
    have htwo : (x : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hfix.symm.trans hinv]
      exact inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one htwo
    rw [orderOf_coe, hx] at hd
    norm_num at hd
  have hxq : orderOf (q x) = 3 := orderOf_eq_prime
    (by rw [← map_pow, show x ^ 3 = 1 by simpa only [hx] using pow_orderOf_eq_one x,
      map_one]) hxq1
  have hderived : (_root_.commutator Q).map e.toMonoidHom =
      _root_.commutator (GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  have heout : e (q r) ∉ _root_.commutator
      (GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
    rw [← hderived, mem_map_equiv]
    simpa only [e.symm_apply_apply] using hrout
  exact AlternatingSix.PGLNineOuterCentralizer.outer_involution_not_commute_cubic
    (e (q r)) (e (q x)) ((e.orderOf_eq _).trans hrq) heout
    ((e.orderOf_eq _).trans hxq) ((hcomm.map q).map e.toMonoidHom)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
