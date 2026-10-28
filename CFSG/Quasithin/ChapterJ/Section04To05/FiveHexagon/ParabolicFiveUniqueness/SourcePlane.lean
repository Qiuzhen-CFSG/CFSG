module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Centralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Mathlib.GroupTheory.IndexNormal

/-!
# The original common five-plane in J.4.10

Every five-subgroup in C_G(B₅) lies in the already constructed extraspecial
five-core P. A Sylow five-subgroup S containing B₅ and a noncommuting second
five-subgroup has center of order five, disjoint from B₅. Thus B₅ Z(S) is an
elementary plane. It lies in P and has index five in both P and S, so the
original two five-subgroups normalize it. The earlier J.3.6 centralizer
calculation makes this very plane self-centralizing.
Source: Aschbacher--Smith J.4.10, printed p.444.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFiveUniqueness
open Subgroup Centralizers Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

include c in
/-- A five-subgroup of the actual five-centralizer lies in its original odd core. -/
theorem five_le_original_core {A:Subgroup G} (hA:IsPGroup 5 A) (ha:A≤G5 B5) :
    A≤fiveOddPart B5 := by
  let N:=pPrimeCore 2 (G5 B5)
  let f:A→*(G5 B5)⧸N := (QuotientGroup.mk' N).comp (inclusion ha)
  have hNc:Nat.card N=125 := by
    have hh:=SourceCompletion.five_oddPart_card c B5
    rw [card_map_of_injective (G5 B5).subtype_injective] at hh
    exact hh
  have hGc:Nat.card (G5 B5)=1000 := by
    obtain ⟨q⟩:=c.fiveQuaternionData_source B5
    rw [G5_card c B5 d.card_Z q,SourceCompletion.five_oddPart_card c B5]
  have hQc:Nat.card ((G5 B5)⧸N)=8 := by
    have hh:=card_eq_card_quotient_mul_card_subgroup N
    rw [hNc,hGc] at hh
    omega
  have hR5:IsPGroup 5 f.range:=hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hR2:IsPGroup 2 f.range:=IsPGroup.of_card_dvd_pow (n:=3)
    (by simpa only [hQc,show 2^3=8 by rfl] using f.range.card_subgroup_dvd_card)
  have hcop:=IsPGroup.coprime_card_of_ne 5 2 (by decide)
    (⊤:Subgroup f.range) (⊤:Subgroup f.range) (hR5.to_subgroup ⊤) (hR2.to_subgroup ⊤)
  have hc:Nat.card f.range=1 := by
    simpa only [card_top,Nat.coprime_self] using hcop
  have hb:f.range=⊥:=card_eq_one.mp hc
  intro x hx
  have he:f ⟨x,hx⟩=1:=mem_bot.mp (hb ▸ (show f ⟨x,hx⟩∈f.range from ⟨⟨x,hx⟩,rfl⟩))
  exact mem_map_of_mem (G5 B5).subtype ((QuotientGroup.eq_one_iff _).mp he)

include c B5 in
/-- J.3.6 transfers its genuine extraspecial structure to every ambient Sylow five-group. -/
theorem sylow_five_structure (S:Sylow 5 G) : Nat.card S=125 ∧ IsExtraspecial 5 S := by
  obtain ⟨T,_,hT,hEx⟩:=Section03.five_oddPart_sylow c B5 (Section03.order_source c)
  let e:=T.equiv S
  exact ⟨(Nat.card_congr e.toEquiv).symm.trans hT,IsExtraspecial.of_mulEquiv e hEx⟩

omit [Finite G] in
private theorem normalizes_twentyfive {W P:Subgroup G}
    (hWP:W≤P) (hW:Nat.card W=25) (hP:Nat.card P=125) : P≤normalizer (W:Set G) := by
  have hc:Nat.card (W.subgroupOf P)=25 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv).trans hW
  have hi:(W.subgroupOf P).index=5 := by
    have hh:=(W.subgroupOf P).index_mul_card
    rw [hc,hP] at hh
    omega
  have hn:(W.subgroupOf P).Normal:=normal_of_index_eq_minFac_card (by rw [hi,hP]; norm_num)
  exact (normal_subgroupOf_iff_le_normalizer hWP).mp hn

omit [Finite G] in
private theorem elementary_five (A:Subgroup G) (hA:Nat.card A=5) : IsElementaryAbelian 5 A := by
  let : IsCyclic A:=isCyclic_of_prime_card hA
  refine {exponent_dvd_p:=Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_}
  intro a
  simpa only [hA] using pow_card_eq_one' (x:=a)

include c in
/-- The common self-centralizing five-plane is constructed from the actual
original five-core and an ambient Sylow group containing the second actor. -/
theorem exists_common_five_plane (A1 A2:Subgroup G)
    (hA1:Nat.card A1=5)
    (hc:B5Image B5≤centralizer (A1:Set G))
    (h5:IsPGroup 5 (B5Image B5⊔A2:Subgroup G))
    (hnc:¬B5Image B5≤centralizer (A2:Set G)) :
    ∃ W:Subgroup G, B5Image B5≤W ∧ W≤fiveOddPart B5 ∧ Nat.card W=25 ∧
      IsElementaryAbelian 5 W ∧ centralizer (W:Set G)=W ∧
      A1⊔A2≤normalizer (W:Set G) := by
  have hA1P:A1≤fiveOddPart B5:=five_le_original_core c B5
    (IsPGroup.of_card (n:=1) hA1) (le_centralizer_iff.mp hc)
  obtain ⟨S,hS⟩:=h5.exists_le_sylow
  obtain ⟨hSc,hEx⟩:=sylow_five_structure c B5 S
  let : IsExtraspecial 5 S:=hEx
  let ZS:Subgroup G:=(center S).map (S:Subgroup G).subtype
  have hZc:Nat.card ZS=5:=
    (card_map_of_injective (S:Subgroup G).subtype_injective).trans (IsExtraspecial.center_order_p 5 S)
  have hBS:B5Image B5≤(S:Subgroup G):=le_sup_left.trans hS
  have hAS:A2≤(S:Subgroup G):=le_sup_right.trans hS
  have hZS:ZS≤(S:Subgroup G):=map_subtype_le _
  have hZcentral:ZS≤centralizer (S:Set G) := by
    rintro z ⟨a,ha,rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hx⟩)
  have hBZ:B5Image B5≤centralizer (ZS:Set G):=
    le_centralizer_iff.mpr (hZcentral.trans (centralizer_le hBS))
  have hnot:¬B5Image B5≤ZS := by
    intro hh
    exact hnc ((hh.trans hZcentral).trans (centralizer_le hAS))
  have hdis:Disjoint (B5Image B5) ZS := by
    have hd:Nat.card (B5Image B5⊓ZS:Subgroup G)∣5 := by
      simpa only [B5Image_card d.card_Z B5] using card_dvd_of_le (inf_le_left (a:=B5Image B5) (b:=ZS))
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hh|hh
    · exact disjoint_iff.mpr (card_eq_one.mp hh)
    · have he:B5Image B5⊓ZS=B5Image B5:=eq_of_le_of_card_ge inf_le_left
        (by rw [hh,B5Image_card d.card_Z B5])
      exact (hnot (he ▸ inf_le_right)).elim
  have hZP:ZS≤fiveOddPart B5:=five_le_original_core c B5
    (IsPGroup.of_card (n:=1) hZc) (hZcentral.trans (centralizer_le hBS))
  let W:Subgroup G:=B5Image B5⊔ZS
  have hWP:W≤fiveOddPart B5:=sup_le (B5Image_le_fiveOddPart d.card_Z B5) hZP
  have hWS:W≤(S:Subgroup G):=sup_le hBS hZS
  have hWc:Nat.card W=25 := by
    change Nat.card (B5Image B5⊔ZS:Subgroup G)=25
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp hBZ).trans (Subgroup.centralizer_le_normalizer _)) hdis,
      B5Image_card d.card_Z B5,hZc]
  have hWe:IsElementaryAbelian 5 W := by
    let :=elementary_five (B5Image B5) (B5Image_card d.card_Z B5)
    let :=elementary_five ZS hZc
    exact IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hBZ)
  refine ⟨W,le_sup_left,hWP,hWc,hWe,
    centralizer_eq_of_card_twentyfive c B5 le_sup_left hWP hWc,?_⟩
  exact sup_le (hA1P.trans (normalizes_twentyfive hWP hWc
    (SourceCompletion.five_oddPart_card c B5)))
    (hAS.trans (normalizes_twentyfive hWS hWc hSc))

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFiveUniqueness
