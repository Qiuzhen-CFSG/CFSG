module
public import Theory.SpecificGroups.Triality.SolvableFixedRank
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import GorensteinWalter.PSL2Cardinality
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The central triality Borel detects a highest-root fixer

The central local factor meets the Borel in the product of the positive
subgroup and the central coroot torus. Its order is q¹²(q − 1): this follows
from the actual PSL₂ quotient, radical order and parabolic Borel index.
The explicit central torus attains this order and acts on the highest root
by its base-field coordinate. Fixation of a nonzero highest-root point
therefore removes this entire torus, leaving the positive subgroup.

The central local-factor hypothesis is essential; highest-root fixation in
the whole Borel only places an element in the arms local factor. The source
consumer transports this kernel through both compatible parabolic maps.
Source: Aschbacher–Smith F.4.29(2,7), pp.289–290, F.4.35, p.292, and
5.3.3, p.659 (`refs/quasithin.pdf`); the genuine triality root construction
and coordinate conventions follow GLS3 §§2.4,2.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCenterComparison
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers

private def centralTorus (P : Parameters) (hp : P.prime = 2) : (fixedField P)ˣ →* Carrier P :=
  ((torus P).subtype.comp (torusMulEquiv P hp).toMonoidHom).comp
    (MonoidHom.inr (ExtensionField P)ˣ (fixedField P)ˣ)

private theorem centralTorus_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (centralTorus P hp) := by
  intro x y h
  have hxy : (1,x) = ((1,y) : OrbitParameters P) :=
    (torusMulEquiv P hp).injective (Subtype.ext h)
  exact congrArg Prod.snd hxy

private theorem centralTorus_mem_local (P : Parameters) (hp : P.prime = 2)
    (y : (fixedField P)ˣ) : centralTorus P hp y ∈ localFactor P .central := by
  have hone : foldedTorusElementary P hp .arms 1 = 1 := by
    apply LeviCommutators.elementaryInclusion_injective P
    apply (inclusion_foldedTorus_arms P hp 1).trans
    apply Eq.trans ?_ (map_one (elementaryInclusion P)).symm
    have hf := map_one (frobenius P)
    have hff := (congrArg (frobenius P) hf).trans hf
    have h0 := torusWord_one P hp 0
    have h2 := (congrArg (torusWord P 2) hf).trans (torusWord_one P hp 2)
    have h3 := (congrArg (torusWord P 3) hff).trans (torusWord_one P hp 3)
    exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h2) h3).trans (by simp only [one_mul])
  change (torusMulEquiv P hp (1,y)).val ∈ localFactor P .central
  rw [torusMulEquiv_val]
  change toCarrier P (foldedTorusElementary P hp .arms 1 *
    foldedTorusElementary P hp .central y) ∈ _
  simp only [hone, one_mul]
  exact levi_le_localFactor P hp .central (LeviCommutators.torusActor_mem_levi P hp .central y)

private theorem central_borel_card (m : ℕ) (hm : 0 < m) :
    let P := binaryParameters m hm
    Nat.card (localFactor P .central ⊓ borel P : Subgroup (Carrier P)) =
      P.q ^ 12 * (P.q - 1) := by
  let P := binaryParameters m hm
  let F := GaloisField 2 m
  have hcF : Nat.card F = P.q := GaloisField.card 2 m (Nat.ne_of_gt hm)
  let e := (localFactorCentralQuotientEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv F).symm
  have hL : Nat.card (localFactor P .central) = P.q^12 * (P.q-1) * (P.q+1) := by
    have hc := (pCore 2 (localFactor P .central)).card_mul_index
    rw [index_eq_card, Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula,
      hcF, localFactor_central_twoCore_card P rfl] at hc
    have hq : 1 ≤ P.q := by have := P.q_ge_two; omega
    have hs : P.q^2-1 = (P.q-1)*(P.q+1) := by
      have hh : P.q^2 = (P.q-1)*(P.q+1)+1 := by nlinarith [Nat.sub_add_cancel hq]
      omega
    rw [←hc,hs]
    ring
  have hn : borel P ≤ normalizer (localFactor P .central : Set (Carrier P)) :=
    (borel_le_parabolic P .central).trans
      ((normal_subgroupOf_iff_le_normalizer (localFactor_le_parabolic P .central)).mp
        (localFactor_normal P .central))
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (localFactor P .central) (borel P) hn
  rw [localFactor_sup_borel_binary P rfl .central] at hh
  have hc := ((borel P).subgroupOf (parabolic P .central)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (borel_le_parabolic P .central)).toEquiv] at hc
  change Nat.card (borel P) * (borel P).relIndex (parabolic P .central) = _ at hc
  rw [Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hc
  change Nat.card (borel P) * (P.q+1) = Nat.card (parabolic P .central) at hc
  have hh' : Nat.card (localFactor P .central) =
      Nat.card (localFactor P .central ⊓ borel P : Subgroup (Carrier P)) * (P.q+1) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := borel P))
    rw [hh,←hc]
    ac_rfl
  rw [hL] at hh'
  exact (Nat.eq_of_mul_eq_mul_right (by omega : 0 < P.q+1) hh').symm

private theorem central_borel_product (m : ℕ) (hm : 0 < m) :
    let P := binaryParameters m hm
    localFactor P .central ⊓ borel P = unipotent P ⊔ (centralTorus P rfl).range := by
  let P := binaryParameters m hm
  let C := (centralTorus P rfl).range
  have hCT : C ≤ torus P := by rintro _ ⟨x,rfl⟩; exact (torusMulEquiv P rfl (1,x)).property
  have hCL : C ≤ localFactor P .central := by
    rintro _ ⟨x,rfl⟩; exact centralTorus_mem_local P rfl x
  have hCB := hCT.trans (torus_le_borel P)
  have hUL : unipotent P ≤ localFactor P .central :=
    unipotent_le_localFactor P .central (unipotent_isPGroup_binary P rfl)
  have hle : unipotent P ⊔ C ≤ localFactor P .central ⊓ borel P :=
    sup_le (le_inf hUL (unipotent_le_borel P)) (le_inf hCL hCB)
  have hcc : Nat.card C = P.q - 1 := by
    rw [Nat.card_congr (MonoidHom.ofInjective (centralTorus_injective P rfl)).toEquiv.symm,
      Nat.card_units,card_fixedField]
  have hc : Nat.card (unipotent P ⊔ C : Subgroup (Carrier P)) = P.q^12*(P.q-1) := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hCB.trans (borel_le_normalizer_unipotent P rfl))
      ((disjoint_unipotent_torus P rfl).mono_right hCT),card_unipotent_binary P rfl,hcc]
  exact (eq_of_le_of_card_ge hle (by rw [hc,central_borel_card])).symm

theorem central_borel_point_kernel (m : ℕ) (hm : 0 < m)
    (g : Carrier (binaryParameters m hm))
    (hgL : g ∈ localFactor (binaryParameters m hm) .central)
    (hgB : g ∈ borel (binaryParameters m hm))
    (hgC : Commute g (highestHom (binaryParameters m hm) rfl (Multiplicative.ofAdd 1))) :
    g ∈ unipotent (binaryParameters m hm) := by
  let P := binaryParameters m hm
  let C := (centralTorus P rfl).range
  have hCB : C ≤ borel P := by
    rintro _ ⟨x,rfl⟩
    exact torus_le_borel P (torusMulEquiv P rfl (1,x)).property
  have hg : g ∈ (unipotent P : Set (Carrier P)) * (C : Set (Carrier P)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _
      (hCB.trans (borel_le_normalizer_unipotent P rfl)),←central_borel_product m hm]
    exact ⟨hgL,hgB⟩
  obtain ⟨u,hu,v,⟨y,rfl⟩,rfl⟩ := hg
  have huc : Commute u (highestHom P rfl (Multiplicative.ofAdd 1)) := by
    have hz : highestHom P rfl (Multiplicative.ofAdd 1) ∈ highestRoot P := by
      rw [←highestHom_range P rfl]; exact ⟨_,rfl⟩
    obtain ⟨z,hz,he⟩ := highestRoot_le_center_unipotent P rfl hz
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨u,hu⟩)
  have hyc : Commute (centralTorus P rfl y) (highestHom P rfl (Multiplicative.ofAdd 1)) := by
    simpa only [inv_mul_cancel_left] using huc.inv_left.mul_left hgC
  have hh := NormalizedRootCentralizers.torus_conjugate_highestHom P rfl (1,y) 1
  have he : centralTorus P rfl y * highestHom P rfl (Multiplicative.ofAdd 1) *
      (centralTorus P rfl y)⁻¹ = highestHom P rfl (Multiplicative.ofAdd 1) :=
    mul_inv_eq_iff_eq_mul.mpr hyc.eq
  have hy : y = 1 := by
    apply Units.ext
    have hh' := congrArg Multiplicative.toAdd (highestHom_injective P rfl (hh.symm.trans he))
    change y.val * 1 = (1 : fixedField P) at hh'
    simpa only [mul_one,Units.val_one] using hh'
  change u * centralTorus P rfl y ∈ unipotent P
  rw [hy,map_one,mul_one]
  exact hu
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityCenterComparison
