module

public import Theory.GroupTheory.NormalFourCentralizerSeparation
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual order729 Sylow product

An abelian order81 subgroup and the order243 odd kernel intersect in order27.
Their product has center the marked cubic line because that line is the entire
ambient centralizer of the odd kernel. Its normalizer therefore preserves the
line, and the local normalizer index16 promotes the product to a Sylow subgroup
of the original group. All products and center maps retain their ambient images.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),printed p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem cubic_sup_sylow_of_line_normalizer (V D W:Subgroup G)
    (hV:Nat.card V=81) (hD:Nat.card D=243)
    (hcap:Nat.card (V⊓D:Subgroup G)=27)
    (hVD:V≤normalizer (D:Set G)) (hWV:W≤V)
    (hCW:V≤centralizer (W:Set G)) (hCD:centralizer (D:Set G)=W)
    (hN:Nat.card (normalizer (W:Set G))=11664) :
    Nat.card (V⊔D:Subgroup G)=729 ∧
    (center (V⊔D:Subgroup G)).map (V⊔D:Subgroup G).subtype=W ∧
    ∃P:Sylow 3 G,(P:Subgroup G)=V⊔D := by
  let Q:=V⊔D
  have hc:Nat.card Q=729:=by
    have hh:=card_mul_eq_card_inf_mul_card_sup_of_normalizes D V hVD
    rw [inf_comm D V,sup_comm D V,hV,hD,hcap] at hh
    change 243*81=27*Nat.card Q at hh
    omega
  have hWQ:W≤Q:=hWV.trans le_sup_left
  have hQC:Q≤centralizer (W:Set G):=by
    apply sup_le hCW
    rw [le_centralizer_iff,hCD]
  have hcenter:(center Q).map Q.subtype=W:=by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      rw [←hCD]
      intro d hd
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨d,(le_sup_right: D≤Q) hd⟩)
    · intro w hw
      refine ⟨⟨w,hWQ hw⟩,mem_center_iff.mpr ?_,rfl⟩
      intro q
      apply Subtype.ext
      exact (hQC q.property w hw).symm
  have hQN:Q≤normalizer (W:Set G):=hQC.trans (centralizer_le_normalizer _)
  have hlocal:¬3∣Q.relIndex (normalizer (W:Set G)):=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) Q (normalizer (W:Set G)) bot_le hQN
    simp only [relIndex_bot_left,hc,hN] at hh
    have he:Q.relIndex (normalizer (W:Set G))=16:=by omega
    rw [he];decide
  have hcontrol:normalizer (Q:Set G)≤normalizer (W:Set G):=by
    rw [←hcenter]
    exact normalizer_le_normalizer_characteristic_image Q (center Q)
  have hp:IsPGroup 3 Q:=IsPGroup.of_card (n:=6) hc
  have hg:=not_dvd_relIndex_of_normalizer_inf_le Q (normalizer (W:Set G)) ⊤ hp le_top hlocal
    (inf_le_left.trans hcontrol)
  have hi:¬3∣Q.index:=by simpa only [relIndex_top_right] using hg
  exact ⟨hc,hcenter,hp.toSylow hi,rfl⟩
end Subgroup
