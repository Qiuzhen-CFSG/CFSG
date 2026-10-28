module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Intersection
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Excluding nonbinary fields in the original linear-three branch

The rank-two residual meets the actual C_X(ZS) in a subgroup with order
divisible by three. On the other hand, H is solvable by its wreath quotient,
and H ∩ X contains a Sylow two-subgroup of X. For field size greater than
two, the image of H ∩ X in PSL₃ lies in a Borel. In odd field degree that
Borel has order prime to three, contradicting the intersection calculation.
The previously proved scalar-center argument excludes even degree.

Thus n = 1 follows from the literal Branch, the original preceding source
hypotheses, and the actual escaping I. This uses intrinsic solvable Sylow
overgroups to supply the printed field-parity step; it needs no additional
opposite-parabolic identification or capture hypothesis. The binary block
and distinguished-factor argument is still required for branch exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

private theorem source_local_solvable : Group.IsSolvable H := by
  obtain ⟨e⟩ := d.geometry.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])

private theorem component_sylow_in_local
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ H.subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro x ⟨y,hy,rfl⟩
  have hyR : (y : I) ∈ R := by
    change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
    rwa [← hQ]
  have hyS : ((y : I) : G) ∈ planeSylow T ZS := hR ▸ mem_map_of_mem I.subtype hyR
  exact (inf_le_left.trans d.geometry.outside.1.1.2) hyS

/-- The actual H ∩ X has order prime to three when the field degree is odd and greater than one. -/
theorem Branch.local_intersection_threePrime_of_large_odd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ZS I)
    (hn : 1 < n) (ho : Odd n) : ¬ 3 ∣ Nat.card (H.subgroupOf X) := by
  obtain ⟨e⟩ := b.ms.1.model
  have hZ : center SL(3,F) = ⊥ := by
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr
    rw [b.field_card,Nat.BinaryTorusParity.two_pow_mod_three,
      if_neg (by simpa only [Nat.even_iff] using (Nat.not_even_iff_odd.mpr ho))]
    decide
  let e' := e.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F hZ)
  let f := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨P,hP⟩ := component_sylow_in_local d hI b.input.component
  let Q := P.mapSurjective hf
  let J := H.subgroupOf X
  let : Group.IsSolvable H := source_local_solvable d
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) h
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  have hN : J.map f ≤ normalizer (Q : Set PSL(3,F)) :=
    Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
      F (by omega) b.field_card Q (J.map f) inferInstance (map_mono hP)
  have hnot := Matrix.PSL3.LinearThree.BorelStructure.three_not_dvd_card_sylowNormalizer_of_odd
    F ho b.field_card Q
  have hr : primeRank 3 (J.map f) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (fun hd => hnot (hd.trans (card_dvd_of_le hN)))
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk] at hr
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hr

/-- The original C.2.7(g) branch must be binary; no opposite-parabolic
or scalar-capture premise is added to the source hypotheses. -/
theorem Branch.degree_eq_one
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ZS I) : n = 1 := by
  by_contra hne
  have hn : 1 < n := by have hp := b.positive; omega
  have ho : Odd n := Nat.not_even_iff_odd.mp (b.not_even d hI)
  have hd := b.residual_centralizer_intersection_three_dvd d hI
  have hle : (pResidual 2 H).map H.subtype ⊓ (X ⊓ centralizer (ZS : Set G)) ≤ H ⊓ X :=
    le_inf (inf_le_left.trans (map_subtype_le _)) (inf_le_right.trans inf_le_left)
  have hd' : 3 ∣ Nat.card (H ⊓ X : Subgroup G) := hd.trans (card_dvd_of_le hle)
  have he : Nat.card (H.subgroupOf X) = Nat.card (H ⊓ X : Subgroup G) := by
    rw [← card_map_of_injective (K := H.subgroupOf X) X.subtype_injective, subgroupOf_map_subtype]
  exact b.local_intersection_threePrime_of_large_odd d hI hn ho (he.symm ▸ hd')

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
