module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedNormalizer

/-!
# Choosing the original J.3 complement compatibly with the marked I

Extend the actual transported I to a Sylow two-subgroup of H∩N_G(B₅).
The original quaternion CQ is normal there and therefore belongs to that
Sylow subgroup. The completed J.3 action embeds this same subgroup faithfully
in GL₂(5), identifying it with C₄ wr C₂. The original extraspecial P and the
normalizer's order give N_G(B₅)=P R, while H=C_G(z) puts the original z in
Z(R). Thus the complement is produced with I≤R; no abstract compatibility
premise or ambient fusion assumption is added. Source: J.3.6 and the
paragraph preceding J.4.8, printed pp.439 and442--443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Subgroup
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Section03
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- The J.3.6 complement can be selected to contain the literal marked I,
retaining all original B₅, P, H, CQ, and z. -/
theorem exists_source_complement
    (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ R : Subgroup G, sourceI e ≤ R ∧ R ≤ d.toTypeRuSetup.H ∧
      R ≤ normalizer (B5Image B5 : Set G) ∧ Nat.card R = 32 ∧ CQ B5 ≤ R ∧
      Disjoint (fiveOddPart B5) R ∧
      normalizer (B5Image B5 : Set G) = fiveOddPart B5 ⊔ R ∧
      Nonempty (R ≃* RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
      c.z ∈ (center R).map R.subtype := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  let N := d.toTypeRuSetup.H ⊓ normalizer (B5Image B5 : Set G)
  have hIN : sourceI e ≤ N := le_inf (sourceI_le_H c e hz) (sourceI_le_normalizer B5 e hfive)
  have hIp : IsPGroup 2 (sourceI e) := IsPGroup.of_card (n:=4) (sourceI_card e)
  obtain ⟨S,hS⟩ := (hIp.comap_subtype (K:=N)).exists_le_sylow
  let R := (S : Subgroup N).map N.subtype
  have hIR : sourceI e ≤ R := by
    have hh := map_mono (f:=N.subtype) hS
    change ((sourceI e).subgroupOf N).map N.subtype ≤ R at hh
    rwa [map_subgroupOf_eq_of_le hIN] at hh
  have hR : R ≤ N := map_subtype_le _
  have hR32 : Nat.card R = 32 := by
    rw [card_map_of_injective N.subtype_injective,S.card_eq_multiplicity,
      local_five_normalizer_card c B5]
    decide +kernel
  have hQN : CQ B5 ≤ N := le_inf (q.le_HC.trans inf_le_left)
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hNQ : N ≤ normalizer (CQ B5 : Set G) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf (inf_le_left.trans d.ru2.six.normalized)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer _))
  let : ((CQ B5).subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hQN).mpr hNQ
  have hQp : IsPGroup 2 (CQ B5) := IsPGroup.of_card (n:=3) (CQ_card B5 q)
  have hQS : (CQ B5).subgroupOf N ≤ (S : Subgroup N) :=
    (hQp.comap_subtype (K:=N)).le_sylow_of_normal (N:=(CQ B5).subgroupOf N) S
  have hQR : CQ B5 ≤ R := by
    have hh := map_mono (f:=N.subtype) hQS
    rwa [map_subgroupOf_eq_of_le hQN] at hh
  have hRH := hR.trans inf_le_left
  have hRN := hR.trans inf_le_right
  have hP := SourceCompletion.five_oddPart_card c B5
  have hd : Disjoint (fiveOddPart B5) R := disjoint_of_coprime_natCard (by rw [hP,hR32]; decide)
  have hn : R ≤ normalizer (fiveOddPart B5 : Set G) :=
    hRN.trans (normalizer_B5Image_le_normalizer_fiveOddPart B5)
  have he : fiveOddPart B5 ⊔ R = normalizer (B5Image B5 : Set G) :=
    eq_of_le_of_card_ge (sup_le ((fiveOddPart_le_G5 B5).trans
      (Subgroup.centralizer_le_normalizer _)) hRN) (by
        rw [five_normalizer_card c B5,
          card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,hP,hR32])
  obtain ⟨f,hf⟩ := exists_five_local_two_linear_action c B5 (order_source c) R hRH hRN hR32 hQR
  have hzR := hIR (source_marks_mem c e hz).1
  have hzc : (⟨c.z,hzR⟩ : R) ∈ center R := by
    apply mem_center_iff.mpr
    intro r
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hRH r.property))
  exact ⟨R,hIR,hRH,hRN,hR32,hQR,hd,he.symm,
    Matrix.GeneralLinearGroup.FiveWreathSylow.wreath_equiv_of_injective_card32 f hf hR32,
    ⟨⟨c.z,hzR⟩,hzc,rfl⟩⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
