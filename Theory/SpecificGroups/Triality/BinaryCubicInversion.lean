module
public import Theory.GroupTheory.CubicSylowInversion
public import Theory.SpecificGroups.Triality.BinarySolvableCubic
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Inverting the original cubic through the binary-triality two-kernel

A cubic in the central parabolic lies in its normal local factor: the
factor has index dividing seven. Pull back that local factor through the
supplied surjection with two-group kernel. Its quotient by a two-group
is the actual PSL₂(2), hence S₃. The specified Sylow maps to the full
positive unipotent group, which lies in this factor. The cubic Sylow
inversion theorem now supplies an inverter upstairs, for the original
cubic and Sylow, without assuming a split extension or an involutory lift.

The local Cartan consumer keeps the literal Y/O₂(Y), containing component
and original left Cartan. Source: Aschbacher--Smith 5.1.13, printed p.636;
GLS3 §§2.3--2.6 for the genuine triality parabolics.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinarySolvableEscape
open Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

private theorem cubic_le_central_local (D : Subgroup M)
    (hD : Nat.card D = 3) (hDP : D ≤ parabolic P .central) :
    D ≤ localFactor P .central := by
  let N := (localFactor P .central).subgroupOf (parabolic P .central)
  let E := D.subgroupOf (parabolic P .central)
  have hc : Nat.card E = 3 := Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv |>.trans hD
  have hidx : N.index ∣ 7 := localFactor_relIndex_dvd_seven P rfl .central
  have hle : E ≤ N := by
    rw [←relIndex_eq_one]
    exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 7 3)
      ((N.relIndex_dvd_index_of_normal E).trans hidx)
      (hc ▸ N.relIndex_dvd_card E)
  intro d hd
  exact hle (show (⟨d,hDP hd⟩ : parabolic P .central) ∈ E from hd)

/-- A cubic in the central parabolic lifts to an actual cubic inverted
from the specified Sylow, with no splitting assumption on the two-kernel. -/
theorem cubic_inverted_of_two_kernel {G : Type*} [Group G] [Finite G]
    (f : G →* M) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 G) (hS : (S : Subgroup G).map f = unipotent P)
    (D : Subgroup G) (hD : Nat.card D = 3)
    (hDP : D.map f ≤ parabolic P .central) :
    ∃ t ∈ (S : Subgroup G), ∀ d ∈ D, t*d*t⁻¹=d⁻¹ := by
  have hi : Function.Injective (f.comp D.subtype) := by
    apply (f.comp D.subtype).ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hd : Disjoint D f.ker := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := hk.exists_card_eq
      rw [hD,hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    exact Subtype.ext (disjoint_def.mp hd x.property hx)
  have hDc : Nat.card (D.map f) = 3 := by
    rw [←range_subtype D,←MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hD
  let N := localFactor P .central
  let J := N.comap f
  have hDJ : D ≤ J := map_le_iff_le_comap.mp (cubic_le_central_local _ hDc hDP)
  have hSJ : (S : Subgroup G) ≤ J := by
    apply map_le_iff_le_comap.mp
    rw [hS]
    exact sylow_le_localFactor P .central (unipotentSylow P rfl)
      ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
  let r : J →* N := f.subgroupComap N
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨y,hy⟩ := hf x
    exact ⟨⟨y,by change f y ∈ N; rw [hy]; exact x.property⟩,Subtype.ext hy⟩
  have hrk : IsPGroup 2 r.ker := by
    have he : r.ker = f.ker.subgroupOf J := by ext x; exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
    (show Nat.card (GaloisField (P).prime (P).exponent) = 2 by
      exact GaloisField.card 2 1 (by decide))
  let e := (localFactorCentralQuotientEquivPSL2 P rfl).trans a
  let q := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 N)).comp r)
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp hr)
  have hqk : IsPGroup 2 q.ker := by
    have he : q.ker = (pCore 2 N).comap r := by
      ext x
      exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
    rw [he]
    exact pCore_isPGroup.comap_of_ker_isPGroup r hrk
  obtain ⟨t,ht,hinv⟩ := cubic_inverted_in_sylow_of_two_kernel q hq hqk
    (D.subgroupOf J) (by rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv,hD])
    (S.subtype hSJ)
  refine ⟨t,ht,?_⟩
  intro d hd
  exact congrArg Subtype.val (hinv ⟨d,hDJ hd⟩ hd)

end Triality.Standard.BinarySolvableEscape
