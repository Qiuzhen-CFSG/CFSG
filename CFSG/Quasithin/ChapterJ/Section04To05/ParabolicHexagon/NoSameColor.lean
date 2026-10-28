module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Membership
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Distinct parabolics on the same central involution are nonadjacent

Every original five-subgroup injects into the Ru2 quotient, whose kernel
is the two-group Q. If the five lies in a canonical parabolic, its image
lies in the normalizer of the parabolic's pentagon and hence is precisely
that Sylow five. Two commuting original fives have commuting images;
a five-subgroup of S5 is self-centralizing, so those labels coincide.
The canonical correspondence then identifies the original parabolics.

The final consumer retains arbitrary original H-conjugates of F1 and
arbitrary commuting five-subgroups inside them. This excludes edges
within one color of the repaired parabolic hexagon in J.4.10, printed p.444.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)

private theorem five_subgroupOf_card (A:Subgroup G) (hAH:A≤d.toTypeRuSetup.H)
    (hA:Nat.card A=5) : Nat.card (A.subgroupOf d.toTypeRuSetup.H)=5 :=
  (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA

/-- The actual Ru2 quotient preserves every original five-subgroup order. -/
theorem five_quotient_image_card (A:Subgroup G) (hAH:A≤d.toTypeRuSetup.H)
    (hA:Nat.card A=5) : Nat.card ((A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap)=5 := by
  let AH:=A.subgroupOf d.toTypeRuSetup.H
  have hcAH:Nat.card AH=5 := five_subgroupOf_card A hAH hA
  have hp:IsPGroup 5 AH := IsPGroup.of_card (n:=1) (by simpa using hcAH)
  have hk:Nat.Coprime 5 (Nat.card d.ru2.quotientMap.ker) := by
    rw [d.ru2.quotient_kernel,Nat.card_congr (subgroupOfEquivOfLe
      (show d.toTypeRuSetup.Q≤d.toTypeRuSetup.H from pCoreIn_le 2 _)).toEquiv,
      d.ru2.card_Q d.card_Z]
    decide
  have hinj:=injective_comp_subtype_of_coprime_ker d.ru2.quotientMap hk AH hp
  have he : (d.ru2.quotientMap.comp AH.subtype).range=AH.map d.ru2.quotientMap := by
    rw [MonoidHom.range_comp,AH.range_subtype]
  rw [←he]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hcAH

include s hi in
/-- Every five inside an original canonical parabolic has its pentagon label. -/
theorem five_image_eq_label (P:Sylow 5 S5) (A:Subgroup G)
    (hAE:A≤parabolicFor p B5 P) (hA:Nat.card A=5) :
    (A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap=(P:Subgroup S5) := by
  have hAH:=hAE.trans (parabolicFor_le_H p B5 P)
  have hp:IsPGroup 5 (A.subgroupOf d.toTypeRuSetup.H) :=
    IsPGroup.of_card (n:=1) (by simpa using five_subgroupOf_card A hAH hA)
  have hn:(A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap≤
      normalizer ((P:Subgroup S5):Set S5) := by
    rw [←parabolicFor_image p s B5 hi P]
    exact map_mono (fun _ hx=>hAE hx)
  have hle:(A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap≤(P:Subgroup S5) :=
    ((hp.map d.ru2.quotientMap).sylow_mem_fixedPoints_iff).mp
      (Subgroup.sylow_mem_fixedPoints_iff _ |>.mpr hn)
  apply eq_of_le_of_card_ge hle
  rw [five_quotient_image_card A hAH hA,
    Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow P]

include s hi in
/-- Commuting fives force equality of their canonical original parabolics. -/
theorem parabolics_eq_of_commuting_fives (P Q:Sylow 5 S5) (A B:Subgroup G)
    (hAP:A≤parabolicFor p B5 P) (hBQ:B≤parabolicFor p B5 Q)
    (hA:Nat.card A=5) (hB:Nat.card B=5) (hc:A≤centralizer (B:Set G)) :
    parabolicFor p B5 P=parabolicFor p B5 Q := by
  have hAI:=five_image_eq_label p s B5 hi P A hAP hA
  have hBI:=five_image_eq_label p s B5 hi Q B hBQ hB
  have him:(A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap≤
      centralizer ((B.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap:Set S5) := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    have hh:a*b=b*a := Subtype.ext (hc ha b hb).symm
    simpa only [map_mul] using congrArg d.ru2.quotientMap hh.symm
  rw [hAI,hBI,Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.centralizer_eq Q] at him
  have hPQ:(P:Subgroup S5)=(Q:Subgroup S5) := eq_of_le_of_card_ge him (by
    rw [Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow P,
      Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow Q])
  exact congrArg (parabolicFor p B5) (SetLike.coe_injective
    (congrArg (fun S:Subgroup S5 => (S:Set S5)) hPQ))

include s hi in
/-- Distinct original H-conjugate parabolics cannot contain commuting fives. -/
theorem conjugate_parabolics_eq_of_commuting_fives (E F:Subgroup G)
    (hE:E∈conjugateFamily p B5) (hF:F∈conjugateFamily p B5)
    (A B:Subgroup G) (hAE:A≤E) (hBF:B≤F)
    (hA:Nat.card A=5) (hB:Nat.card B=5) (hc:A≤centralizer (B:Set G)) : E=F := by
  obtain ⟨P,hP⟩:=(conjugateEquiv p s B5 hi).surjective ⟨E,hE⟩
  obtain ⟨Q,hQ⟩:=(conjugateEquiv p s B5 hi).surjective ⟨F,hF⟩
  have hp:parabolicFor p B5 P=E:=congrArg Subtype.val hP
  have hq:parabolicFor p B5 Q=F:=congrArg Subtype.val hQ
  rw [←hp,←hq]
  exact parabolics_eq_of_commuting_fives p s B5 hi P Q A B (hp ▸ hAE) (hq ▸ hBF) hA hB hc

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
