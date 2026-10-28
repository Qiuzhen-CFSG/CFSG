module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceOppositeFive

/-!
# The constructed opposite five has the other quotient pentagon

The literal Ru2 quotient has central kernel of order two on the constructed
SL2(5) factor. Two distinct five-subgroups in that factor therefore have
distinct quotient images, by the unique coprime central lifting theorem.
Applying this to the original completion constructs its opposite five
with a different S5 pentagon while retaining the same factor and all
original conjugation maps.

This is the parabolic-level replacement needed before J.4.8, printed
p.443: two different opposite fives elsewhere in G may still determine
the same quotient pentagon and hence the same original parabolic.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter DiagonalCentralizer
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

private theorem subgroup_image (K A:Subgroup G) (hKH:K≤d.toTypeRuSetup.H) (hAK:A≤K) :
    (A.subgroupOf K).map (componentMap K hKH)=
      (A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact mem_map.mpr ⟨inclusion hKH x,hx,rfl⟩
  · rintro y ⟨x,hx,rfl⟩
    exact mem_map.mpr ⟨⟨x,hAK hx⟩,hx,rfl⟩

/-- Distinct original fives in the actual SL2 factor have distinct images. -/
theorem five_images_ne_of_component (K:Subgroup G) (hKH:K≤d.toTypeRuSetup.H)
    (hBK:B5Image B5≤K) (eK:K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (A B:Subgroup G) (hAK:A≤K) (hB'K:B≤K) (hA:Nat.card A=5) (hB:Nat.card B=5)
    (hne:A≠B) :
    (A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap≠
      (B.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap := by
  intro he
  let f:=componentMap K hKH
  have hk: f.ker=center K := (componentMap_structure B5 K hKH hBK eK).1
  have hcop:(Nat.card f.ker).Coprime 5 := by
    rw [hk,Theory.SpecificGroups.SL2.PermutationFiveImage.card_center eK]
    decide
  have he' : (A.subgroupOf K).map f=(B.subgroupOf K).map f := by
    rw [subgroup_image K A hKH hAK,subgroup_image K B hKH hB'K]
    exact he
  have hh:=Theory.SpecificGroups.SymmetricFive.CentralLiftPentagons.five_eq_of_image_eq f
    hk.le hcop (A.subgroupOf K) (B.subgroupOf K)
    ((Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hA)
    ((Nat.card_congr (subgroupOfEquivOfLe hB'K).toEquiv).trans hB) he'
  apply hne
  have hm:=congrArg (Subgroup.map K.subtype) hh
  rwa [map_subgroupOf_eq_of_le hAK,map_subgroupOf_eq_of_le hB'K] at hm

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer

namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Subgroup Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer DiagonalCentralizer

/-- The original Completion constructs the opposite five on the other pentagon. -/
theorem source_opposite_pentagon {D : Type*} [Group D] (q : Completion D)
    {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
    (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    {F : Subgroup G} (e : first ≃* F) (f : D →* G)
    (hleft : ∀ a : first, f (q.left a) = (e a : G)) (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ K B' : Subgroup G, B5Image B5 ≤ K ∧ sourceI e ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (sourceIz e : Set G) ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nat.card B' = 5 ∧ B' ≠ B5Image B5 ∧ sourceI e ≤ normalizer (B' : Set G) ∧
      K = B5Image B5 ⊔ B' ∧
      (B'.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap ≠
        ((B5Image B5).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap ∧
      ∀ C : Subgroup G, C ≤ K → Nat.card C = 5 → sourceI e ≤ normalizer (C : Set G) →
        C = B5Image B5 ∨ C = B' := by
  obtain ⟨K,B',hBK,hIK,hKC,⟨eK⟩,hB',hne,hIB',hgen,hu⟩ :=
    source_opposite_five q c B5 e f hleft hz hfive
  refine ⟨K,B',hBK,hIK,hKC,⟨eK⟩,hB',hne,hIB',hgen,?_,hu⟩
  exact five_images_ne_of_component B5 K (hKC.trans (centralizer_le_H c e hz)) hBK eK
    B' (B5Image B5) (hgen.symm ▸ le_sup_right) hBK hB'
    (B5Image_card d.card_Z B5) hne

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
