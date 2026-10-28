module

public import CFSG.Quasithin.ChapterJ.Section04To05.SourceOpening
public import CFSG.Quasithin.ChapterJ.Section04To05.Span.Order
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Products

/-!
# The original J.4.2–3 and the exact identity W=S₂

The source span lies in the original six-dimensional Steinberg preimage,
and both have order 512. Hence they are equal. All three clauses of J.4.2
and both clauses of J.4.3 follow for the same plane, source conjugator and
inverting involution, with an actual inverted Sylow five-subgroup.

Source: Aschbacher–Smith, J.4.2–3, printed pp.440–441.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- J.4.3(2): equality of the original source subgroup and Steinberg preimage. -/
theorem Plane.W_eq_S₂ : p.W = p.S₂ :=
  eq_of_le_of_card_ge p.W_le_S₂ (by rw [p.card_W,p.card_S₂])

/-- Both conclusions of J.4.3, with the original Ru1 representation. -/
theorem Plane.source_lemma_J_4_3 :
    Module.finrank (ZMod 2)
      (subspaceCommutator (BinaryLinearThree.S.comp d.ru1.quotientMap) ⊤
        (p.R₂.subgroupOf d.L)) = 6 ∧ p.S₂ = p.W :=
  ⟨p.finrank_R₂_commutator,p.W_eq_S₂.symm⟩

/-- The complete source J.4.2, with one actual B₅ inverted by the selected v. -/
theorem SourceChoice.source_lemma_J_4_2 {p : Plane d} (s : SourceChoice p) :
    ∃ B5 : Sylow 5 d.toTypeRuSetup.H,
      (∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) ∧
      (d.T : Subgroup G) = p.R₂ ⊔ d.toTypeRuSetup.Q ∧
      (IsElementaryAbelian 2 (hat d p.W) ∧ Nat.card (hat d p.W)=16 ∧ Nat.card p.W=512) ∧
      (IsElementaryAbelian 2 (p.fiveSpanQuotient B5) ∧ Nat.card (p.fiveSpanQuotient B5)=4) := by
  obtain ⟨B5,hi,he,hcard,hW,_,hq,hqc⟩ := s.source_span
  exact ⟨B5,hi,p.R₂_sup_Q.symm,⟨he,hcard,hW⟩,hq,hqc⟩

/-- The full original setup supplies J.4.2–3 without extra local premises. -/
theorem source_core_of_typeRu (h : IsTypeRu G) :
    ∃ (d : LocalSetup G) (p : Plane d) (s : SourceChoice p)
      (B5 : Sylow 5 d.toTypeRuSetup.H),
      (∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) ∧
      (d.T : Subgroup G) = p.R₂ ⊔ d.toTypeRuSetup.Q ∧
      IsElementaryAbelian 2 (hat d p.W) ∧ Nat.card (hat d p.W)=16 ∧
      Nat.card p.W=512 ∧ IsElementaryAbelian 2 (p.fiveSpanQuotient B5) ∧
      Nat.card (p.fiveSpanQuotient B5)=4 ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator (BinaryLinearThree.S.comp d.ru1.quotientMap) ⊤
          (p.R₂.subgroupOf d.L)) = 6 ∧ p.S₂=p.W := by
  obtain ⟨d,p,⟨s⟩⟩ := source_J4_choice h
  obtain ⟨B5,hi,hT,⟨he,hc,hW⟩,hq,hqc⟩ := s.source_lemma_J_4_2
  exact ⟨d,p,s,B5,hi,hT,he,hc,hW,hq,hqc,p.finrank_R₂_commutator,p.W_eq_S₂.symm⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
