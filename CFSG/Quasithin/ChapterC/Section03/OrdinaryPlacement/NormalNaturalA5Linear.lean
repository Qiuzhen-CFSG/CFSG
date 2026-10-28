module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Local
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The degree-three ordinary row with a central source point

The actual A₅ source supplies five in the order of the ordinary component's
central quotient. This rules out the binary field. At all other fields except
four, the proved scalar covering bounds the center by three. The original
C.2.8 odd-core conclusion makes this center a two-group, so its nontriviality
forces the field of order four.

This is the linear row of the ordinary-component inspection in
Aschbacher--Smith 12.7.5, printed p.840. No multiplier table is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

private theorem a5_five_dvd_ordinary_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) : 5 ∣ Nat.card (K ⧸ center K) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hL : 0 < primeRank 5 L := by
    have hh := primeRank_quotient_le_of_isTwoGroup 5 (by decide)
      (pCore 2 L) pCore_isPGroup
    rw [primeRank_congr 5 a,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 5 (by decide) (by decide)] at hh
    omega
  have hspan : 0 < primeRank 5 (conjugateSpanBy L M) :=
    lt_of_lt_of_le hL (Theory.GroupTheory.primeRank_le_of_injective 5
      (inclusion (le_conjugateSpanBy L M)) (inclusion_injective _))
  obtain ⟨_,_,_,_,hr⟩ := h.ordinary_quotient_local_data K hK
  have himage := Theory.GroupTheory.primeRank_le_of_injective 5
    (((((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
      (QuotientGroup.mk' (center K))).subtype)
    (Subgroup.subtype_injective _)
  rw [hr 5 (by decide) (by decide)] at himage
  by_contra hn
  rw [PrimeRank.eq_zero_iff_not_dvd_card.mpr hn] at himage
  omega

/-- The actual linear ordinary quotient containing the A₅ source has field
order four whenever its center contains the original nonidentity point. -/
theorem ordinary_a5_psl3_field_card_four
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) (hz : center K ≠ ⊥)
    {F : Type*} [Field F] [Finite F]
    (e : K ⧸ center K ≃* PSL(3,F)) : Nat.card F = 4 := by
  let := hK.2
  have h2 : Nat.card F ≠ 2 := by
    intro hF
    have hd := h.a5_five_dvd_ordinary_quotient a K hK
    rw [Nat.card_congr e.toEquiv] at hd
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF, Fin.prod_univ_succ] at hc
    rw [hc] at hd
    norm_num at hd
  by_contra h4
  have hd := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd h2 h4 e
  have hz2 : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hp : IsPGroup 2 (center K) := hz2 ▸ pCore_isPGroup
  rcases hp.card_eq_or_dvd with hc | hc
  · exact hz (Subgroup.card_eq_one.mp hc)
  · have hh := hc.trans (hd.trans (Nat.gcd_dvd_left 3 (Nat.card F - 1)))
    norm_num at hh

/-- The literal Theorem C degree-three model is the field-four model. -/
theorem ordinary_a5_isPSL3_four
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K) (hz : center K ≠ ⊥)
    {q : ℕ} (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 q) :
    q = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 3 4 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have h4 := h.ordinary_a5_psl3_field_card_four a K hK hz e
  exact ⟨hF.symm.trans h4, ⟨F,inferInstance,inferInstance,h4,⟨e⟩⟩⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
