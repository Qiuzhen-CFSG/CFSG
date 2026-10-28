module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeldCertificate
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation
public import Theory.Representation.PSL3Two.NaturalDualRank
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Excluding the Held placed component for the binary doubled orbit

The checked involution certificate places every elementary subgroup of order 64
in one of the two literal rank-six rows of a Held Sylow subgroup. This proves the
needed placement without assuming relative normality. Their fixed sextets give
full ambient normalizer order 138240. Since this order is prime to seven, such a
subgroup cannot admit the actual natural--dual SL₃(2) covering action.

The Chapter12 companion transports the entire original orbit through the full
component center and applies this exclusion to the literal residual quotient.
Source: the concluding local inspection in Aschbacher--Smith 4.4.3, printed
pp.622--623, used by 7.3.4 and 7.6.1, printed pp.699,702, refs/quasithin.pdf.
The reused ATLAS Held carrier, permutation tables and certificates retain their
attribution and license in Theory/SpecificGroups/Held and LICENSES/ATLAS.txt.
-/

open Subgroup
open scoped IsMulCommutative
open Held Held.LocalPairs.SylowGeometry.Calculations
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration ExtensionChecks
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeld
private theorem small_word_not_mem (E : Subgroup representative)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 64) (k : Fin 7) :
    normalForm (reps k) ∉ E := by
  classical
  intro hk
  have hc (x : E) : ∃ n ∈ centralMembers k, normalForm n = x.val :=
    centralizer_cover k x.val
      (elemPow_eq_one_of_isElementaryAbelian _ x.property)
      (setLike_mul_comm x.property hk)
  choose n hn he using hc
  let f : E → (centralMembers k).toFinset := fun x => ⟨n x,List.mem_toFinset.mpr (hn x)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (he x).symm.trans ((congrArg normalForm (congrArg Subtype.val h)).trans (he y))
  have hh := Nat.card_le_card_of_injective f hf
  rw [hE, Nat.card_eq_fintype_card, Fintype.card_coe] at hh
  exact (Nat.not_le_of_lt (centralMembers_card k)) hh

/-- Every elementary order-64 subgroup of the literal Held Sylow is one of
its two known rank-six subgroups. No relative normality is assumed. -/
public theorem representative_sixtyFour (E : Subgroup representative)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 64) :
    E = entry 20 ∨ E = entry 21 := by
  have hmem (x : representative) (hx : x ∈ E) : x ∈ entry 20 ∨ x ∈ entry 21 := by
    obtain ⟨n,rfl⟩ := normalForm_surjective x
    rcases normalForm_cases n (elemPow_eq_one_of_isElementaryAbelian _ hx) with h | h | ⟨k,s,hs⟩
    · exact Or.inl h
    · exact Or.inr h
    · let a := MulAut.conj s⁻¹
      let U := E.map a.toMonoidHom
      let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
      have hU : Nat.card U = 64 := (card_map_of_injective a.injective).trans hE
      have hr : normalForm (reps k) ∈ U := by
        refine ⟨normalForm n,hx,?_⟩
        change s⁻¹ * normalForm n * (s⁻¹)⁻¹ = normalForm (reps k)
        rw [inv_inv, mul_assoc, hs, ←mul_assoc, inv_mul_cancel, one_mul]
      exact (small_word_not_mem U hU k hr).elim
  have hle : E ≤ entry 20 ∨ E ≤ entry 21 := by
    by_cases h : E ≤ entry 20
    · exact Or.inl h
    · obtain ⟨x,hx,hx20⟩ := SetLike.not_le_iff_exists.mp h
      have hx21 := (hmem x hx).resolve_left hx20
      apply Or.inr
      intro y hy
      rcases hmem y hy with hy20 | hy21
      · rcases hmem (x*y) (E.mul_mem hx hy) with hxy | hxy
        · exact (hx20 (by simpa only [mul_inv_cancel_right] using
            (entry 20).mul_mem hxy ((entry 20).inv_mem hy20))).elim
        · simpa only [inv_mul_cancel_left] using
            (entry 21).mul_mem ((entry 21).inv_mem hx21) hxy
      · exact hy21
  have hc (j : Fin 22) (hj : j = 20 ∨ j = 21) : Nat.card (entry j) = 64 :=
    ((Held.AutomorphismLocalPair.representative_normal_elementary_order64_iff (entry j)).mpr
      (hj.elim (fun h => Or.inl (congrArg entry h)) (fun h => Or.inr (congrArg entry h)))).2.2
  exact hle.elim
    (fun h => Or.inl (eq_of_le_of_card_ge h (by rw [hE,hc 20 (Or.inl rfl)])))
    (fun h => Or.inr (eq_of_le_of_card_ge h (by rw [hE,hc 21 (Or.inr rfl)])))

private theorem row_normalizer_card (k : Fin 2) :
    Nat.card (normalizer (ambient (RankSixCertificate.row k) : Set He)) = 138240 := by
  have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  apply Nat.le_antisymm
  · exact (Nat.card_le_card_of_injective
      (inclusion (RankSixCertificate.normalizer_le_sextetStabilizer k))
      (inclusion_injective _)).trans (RankSixCertificate.sextetStabilizer_card_le hg k)
  · exact (RankSixCertificate.candidateGroup_card_ge representative_isPGroup k).trans
      (Nat.card_le_card_of_injective (inclusion (RankSixCertificate.candidateGroup_le_normalizer k))
        (inclusion_injective _))

/-- The full ambient normalizer of every elementary order-64 subgroup of Held
has order 138240. This supplies Sylow placement through the actual subgroup
calculation rather than assuming normality in a Sylow subgroup. -/
public theorem sixtyFour_normalizer_card (E : Subgroup He) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 64) : Nat.card (normalizer (E : Set He)) = 138240 := by
  obtain ⟨S,hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨P,hP⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq He S P
  let a := MulAut.conj g
  let U := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map a.toMonoidHom
  have hUP : U ≤ representative := by
    have hh := map_mono (f := a.toMonoidHom) hES
    change U ≤ (g • S : Sylow 2 He) at hh
    rwa [hg,hP] at hh
  let R := U.subgroupOf representative
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hUP
  have hR : Nat.card R = 64 := (Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv).trans
    ((card_map_of_injective a.injective).trans hE)
  have hu : U = ambient 20 ∨ U = ambient 21 := by
    rcases representative_sixtyFour R hR with he | he
    · apply Or.inl
      change U = (entry 20).map representative.subtype
      rw [←he]
      exact (map_subgroupOf_eq_of_le hUP).symm
    · apply Or.inr
      change U = (entry 21).map representative.subtype
      rw [←he]
      exact (map_subgroupOf_eq_of_le hUP).symm
  have hh : Nat.card (normalizer (U : Set He)) = 138240 := by
    rcases hu with he | he
    · rw [he]; exact row_normalizer_card 0
    · rw [he]; exact row_normalizer_card 1
  rw [←map_equiv_normalizer_eq E a,card_map_of_injective a.injective] at hh
  exact hh

/-- The whole natural--dual six-space and its actual SL₃(2) covering actor
cannot occur in Held: its normalizer order is prime to seven. -/
public theorem no_held_natural_dual
    {R : Type*} [Group R] [Finite R]
    (f : R →* He) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative BinaryLinearThree.NaturalDual.Space →* He)
    (hu : Function.Injective u)
    (ha : ∀ r v, f r * u (Multiplicative.ofAdd v) * (f r)⁻¹ =
      u (Multiplicative.ofAdd (BinaryLinearThree.NaturalDual.action (q r) v))) : False := by
  let E := u.range
  let : IsElementaryAbelian 2 (Multiplicative BinaryLinearThree.NaturalDual.Space) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective
    u.rangeRestrict u.rangeRestrict_surjective
  have hE : Nat.card E = 64 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hu).toEquiv]
    change Nat.card BinaryLinearThree.NaturalDual.Space = 64
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2)]
    norm_num [BinaryLinearThree.NaturalDual.Space,Module.finrank_prod]
  have hnorm : f.range ≤ normalizer (E : Set He) := by
    apply le_set_normalizer_iff.mpr
    rintro _ ⟨r,rfl⟩ _ ⟨v,rfl⟩
    exact ⟨Multiplicative.ofAdd (BinaryLinearThree.NaturalDual.action (q r) v.toAdd),
      (ha r v.toAdd).symm⟩
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro r hr
    have hfr : f r = 1 := congrArg Subtype.val hr
    apply BinaryLinearThree.NaturalDual.action_injective
    apply LinearMap.ext
    intro v
    have he := ha r v
    rw [hfr,one_mul,inv_one,mul_one] at he
    have hh := congrArg Multiplicative.toAdd (hu he)
    change v = BinaryLinearThree.NaturalDual.action (q r) v at hh
    simpa only [map_one,Module.End.one_apply] using hh.symm
  let qB : f.range →* BinaryLinearThree.Group :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q,hk⟩
  have hqB : Function.Surjective qB := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨f.rangeRestrict r,by simp [qB]⟩
  have hseven : 7 ∣ Nat.card f.range := by
    have hh := card_dvd_of_surjective qB hqB
    rw [Matrix.PSL3Two.card_SL] at hh
    exact (by decide : 7 ∣ 168).trans hh
  have hd := hseven.trans (card_dvd_of_le hnorm)
  rw [sixtyFour_normalizer_card E hE] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedHeld
