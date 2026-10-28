module

public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicGeneration.CoreObstruction
public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator.Closure
public import Theory.GroupTheory.PCoreRestriction

/-!
# Vanishing of the core in the generated source pair

The selected escaping involution lies in S₂. Thus the generation contradiction
only needs N∩S₂≤Q, rather than N≤Q. For N=O₂(F₁∨F₂), restriction to F₁ supplies
this condition once S₂≤F₁ and O₂(F₁)≤Q. The order-five actor and F₂ normalize N.
Its centralizer of Q₅ is trivial, so conjugation orbit counting for the two-group
Q₅ forces N=1. This proves the actual joined-core conclusion from the preceding
local subgroup construction, without assuming a Sylow subgroup of the join.

Source: Aschbacher–Smith, J.4.5(1), printed p.442.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

/-- The original escaping involution is already in the actual S₂. -/
theorem SourceChoice.v_mem_S₂ (s : SourceChoice p) : s.v ∈ p.S₂ := by
  obtain ⟨u,hu,he⟩ := s.v_mem
  rw [← he]
  exact mem_normalizer_iff.mp (p.S₂_normalized (p.L₂_le_parabolic s.in_residual)) u |>.mp
    (p.U_le_S₂ hu)

/-- The source contradiction needs containment only on the original S₂. -/
theorem SourceChoice.not_point_le_of_intersection_normalized (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (J N : Subgroup G)
    (hJS : J ⊔ d.toTypeRuSetup.S = p.parabolic)
    (hNQ : N ⊓ p.S₂ ≤ d.toTypeRuSetup.Q) (hJ : J ≤ normalizer (N : Set G))
    (hB : Centralizers.Choices.B5Image B5 ≤ normalizer (N : Set G)) :
    ¬ d.toTypeRuSetup.Z ≤ N := by
  intro hZ
  have hp := s.plane_le_of_supplement_normalized J N hJS hZ hJ
  have hU := p.U_le_of_five_normalized B5 N hp hB
  exact s.v_not_Q (hNQ
    ⟨s.conjugate_U_le_of_supplement_normalized J N hJS hU hJ s.v_mem,s.v_mem_S₂⟩)

/-- The two source parabolics have trivial core in their literal generated subgroup. -/
theorem SourceChoice.joined_core_eq_bot (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (F₁ F₂ : Subgroup G)
    (hB : Centralizers.Choices.B5Image B5 ≤ F₁) (hfive : Q₅ d B5 ≤ F₁)
    (hS₂ : p.S₂ ≤ F₁) (hgen : F₂ ⊔ d.toTypeRuSetup.S = p.parabolic)
    (hcore : F₁.pCoreIn 2 ≤ d.toTypeRuSetup.Q) :
    pCore 2 (F₁ ⊔ F₂ : Subgroup G) = ⊥ := by
  let F := F₁ ⊔ F₂
  let N := F.pCoreIn 2
  have hn : F ≤ normalizer (N : Set G) := by
    have h := (pCore 2 F).le_normalizer_map F.subtype
    simpa only [N,pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using h
  have hcap : N ⊓ p.S₂ ≤ d.toTypeRuSetup.Q := by
    apply le_trans ?_ hcore
    apply le_trans ?_ (inf_pCoreIn_le_of_le 2 (show F₁ ≤ F from le_sup_left))
    exact le_inf (inf_le_right.trans hS₂) inf_le_left
  have hfix : N ⊓ centralizer (Q₅ d B5 : Set G) = ⊥ := by
    by_contra he
    exact s.not_point_le_of_intersection_normalized B5 F₂ N hgen hcap
      (le_sup_right.trans hn) ((hB.trans le_sup_left).trans hn)
      (Z_le_of_nontrivial_centralizer d B5 le_rfl he)
  have hc := card_modEq_card_inf_centralizer (Q₅ d B5) N
    ((isPGroup_pCoreIn 2 d.toTypeRuSetup.H).to_le (Q₅_le_Q d B5))
    ((hfive.trans le_sup_left).trans hn)
  rw [hfix,Subgroup.card_bot] at hc
  obtain ⟨n,he⟩ := (isPGroup_pCoreIn 2 F).exists_card_eq
  have hNcard : Nat.card N = 1 := by
    change Nat.card N % 2 = 1 % 2 at hc
    change Nat.card N = 2 ^ n at he
    cases n with
    | zero => simpa using he
    | succ n => rw [he,pow_succ,Nat.mul_mod] at hc; norm_num at hc
  have hN : N = ⊥ := card_eq_one.mp hNcard
  exact (map_eq_bot_iff_of_injective (pCore 2 F) F.subtype_injective).mp hN

end CFSG.Quasithin.ChapterJ.RuSubgroup
