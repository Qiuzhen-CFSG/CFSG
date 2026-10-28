module

public import Theory.GroupTheory.CubicSupSylow
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.GeneralizedFitting
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.Canonical

/-!
# The original Sylow-three product

The actual canonical V and D have intersection27. The original complement48
then determines the normalizer order, while C_G(D)=W identifies the product
center. The characteristic-center argument promotes V D to a Sylow subgroup
of G. The input D structure is exactly the preceding moved-line source output;
all binary-local data for V are produced from the same IsType hypothesis.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),printed p246.
-/

public section

open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_line_sylow (P:Sylow 3 (centralizer z)) (W K:Subgroup G)
    (hW:Nat.card W=3) (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hK:Nat.card K=48) (hKN:K≤normalizer (W:Set G))
    (hgen:normalizer (W:Set G)=CubicLine.oddKernel W⊔K)
    (hdis:Disjoint (CubicLine.oddKernel W) K)
    (hD:Nat.card (CubicLine.oddKernel W)=243)
    (hCD:Subgroup.centralizer (CubicLine.oddKernel W:Set G)=W) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let Q:=V⊔CubicLine.oddKernel W
    Nat.card Q=729 ∧ (center Q).map Q.subtype=W ∧ ∃S:Sylow 3 G,(S:Subgroup G)=Q := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  have hX:=h.cubic_sylow_image_card P
  have hXH:X≤centralizer z:=map_subtype_le _
  have hXV:X≤V:=CubicNormalizer.le_oddKernel X hX (h.toCentralizerHypothesis.cubic_centralizer X hX hXH)
  obtain ⟨hV,hVc⟩:=h.original_cubic_kernel_eighty_one P
  have hVW:V≤Subgroup.centralizer (W:Set G):=(map_subtype_le _).trans (centralizer_le hWX)
  have hVN:V≤normalizer (W:Set G):=hVW.trans (centralizer_le_normalizer _)
  have hcap:Nat.card (V⊓CubicLine.oddKernel W:Subgroup G)=27:=
    (h.cubic_line_kernel_intersection X W hX hXH hW hWX hfixed hsplit hV hVc).2
  have hN:Nat.card (normalizer (W:Set G))=11664:=by
    rw [hgen,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (hKN.trans (CubicLine.normalizer_normalizes_oddKernel W)) hdis,hD,hK]
  exact cubic_sup_sylow_of_line_normalizer V (CubicLine.oddKernel W) W hVc hD hcap
    (hVN.trans (CubicLine.normalizer_normalizes_oddKernel W)) (hWX.trans hXV) hVW hCD hN


include h in
theorem original_cubic_sylow_of_moved_line (P:Sylow 3 (centralizer z))
    (W F K:Subgroup G) (hW:Nat.card W=3)
    (hWX:W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hfixed:Nonempty ((core z⊓Subgroup.centralizer (W:Set G):Subgroup G)≃*QuaternionGroup 2))
    (hsplit:normalizer (W:Set G)=CubicLine.oddKernel W⊔(normalizer (W:Set G)⊓centralizer z))
    (hS:∃S:Sylow 2 (normalizer (W:Set G)),Nonempty (S≃*QuaternionGroup 4))
    (hF:Nat.card F=3)
    (hFV:F≤CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hFD:F≤CubicLine.oddKernel W)
    (hVN:normalizer (F:Set G)≤normalizer
      (CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype):Set G))
    (hindex:(CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)).relIndex
      (normalizer (F:Set G))=24)
    (hK:Nat.card K=48) (hKN:K≤normalizer (W:Set G))
    (hgen:normalizer (W:Set G)=CubicLine.oddKernel W⊔K)
    (hdis:Disjoint (CubicLine.oddKernel W) K) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    let Q:=V⊔CubicLine.oddKernel W
    Nat.card Q=729 ∧ (center Q).map Q.subtype=W ∧ ∃S:Sylow 3 G,(S:Subgroup G)=Q := by
  obtain ⟨_,hD,hCD,_,_⟩:=h.original_cubic_line_fitting_of_moved_line P W F hW hWX hfixed
    hsplit hS hF hFV hFD hVN hindex
  exact h.cubic_line_sylow P W K hW hWX hfixed hsplit hK hKN hgen hdis hD hCD
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
