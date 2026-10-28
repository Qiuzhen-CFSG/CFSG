module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.HexEvenExtension
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import Theory.HexEvenExtension.Locals.Quotient
public import Theory.HexEvenExtension.Locals.MixedObstruction

/-!
# The original local vertices in the hatted symmetric-six source case

The actual HexEven residual and original split Sylow produce the full
hatted S₆ extension. Its literal quotient has cubic kernel. Each original
vertex has order 48; its common Sylow has order 16 and embeds in the
quotient. Generation forces both vertex restrictions to be injective.
The S₆ duad/syntheme theorem then identifies both original vertices with
C₂ × S₄. Thus mixed local vertices are excluded by the source generation
hypothesis, without assuming local characteristic two.

Source: Aschbacher–Smith, F.6.18(8), printed p.310, using F.6.1 and I.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.HexEvenExtension
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] {G₁ G₂ : Subgroup G}

/-- The literal symmetric quotient on the source group. -/
def hexLocalQuotient (r : TripleSymmetricExtension G) : G →* Equiv.Perm (Fin 6) :=
  r.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' r.kernel)

theorem hexLocalQuotient_surjective (r : TripleSymmetricExtension G) :
    Function.Surjective (hexLocalQuotient r) :=
  r.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem hexLocalQuotient_ker (r : TripleSymmetricExtension G) :
    (hexLocalQuotient r).ker = r.kernel := by
  rw [hexLocalQuotient, MonoidHom.ker_comp_of_injective _ _ r.quotientEquiv.injective,
    QuotientGroup.ker_mk']

private theorem hexLocalQuotient_coprime (r : TripleSymmetricExtension G) :
    Nat.Coprime 2 (Nat.card (hexLocalQuotient r).ker) := by
  rw [hexLocalQuotient_ker, Nat.card_congr r.kernelEquiv.toEquiv]
  norm_num

variable [Finite G]

private theorem local_source_cards
    (h : IsGoldschmidtTriple G₁ G₂)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :
    Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16 ∧ Nat.card G₁ = 48 ∧ Nat.card G₂ = 48 := by
  have ht : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num
  exact ⟨ht, by rw [h.local_card_eq_three_mul_intersection, ht],
    by rw [h.symm.local_card_eq_three_mul_intersection, inf_comm G₂ G₁, ht]⟩

/-- The original vertex inclusions followed by the actual hatted quotient
are faithful, and induce equivalences with their literal images. -/
theorem source_hex_even_quotient_bijective
    (h : IsGoldschmidtTriple G₁ G₂)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (r : TripleSymmetricExtension G) :
    Function.Bijective ((hexLocalQuotient r).subgroupMap G₁) ∧
      Function.Bijective ((hexLocalQuotient r).subgroupMap G₂) := by
  obtain ⟨ht,ha,hb⟩ := local_source_cards h eT
  obtain ⟨T,hT⟩ := h.intersection_sylow
  have hc : Nat.card T = 16 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hT.symm).toEquiv).trans ht
  exact Locals.vertex_quotient_bijective (hexLocalQuotient r)
    (hexLocalQuotient_surjective r) (hexLocalQuotient_coprime r) T hc G₁ G₂
    (hT.symm.le.trans inf_le_left) (hT.symm.le.trans inf_le_right) ha hb h.generated

/-- Both literal vertices are C₂ × S₄ in the actual HexEven source branch. -/
theorem source_hex_even_vertices
    (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    Nonempty (G₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (G₂ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  obtain ⟨r⟩ := source_triple_symmetric_six_extension h hFstar eT hm
  obtain ⟨ht,ha,hb⟩ := local_source_cards h eT
  obtain ⟨T,hT⟩ := h.intersection_sylow
  have hc : Nat.card T = 16 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hT.symm).toEquiv).trans ht
  exact Locals.vertices_equiv (hexLocalQuotient r) (hexLocalQuotient_surjective r)
    (hexLocalQuotient_coprime r) T hc G₁ G₂
    (hT.symm.le.trans inf_le_left) (hT.symm.le.trans inf_le_right) ha hb h.generated

/-- Neither original source vertex can be the mixed S₃ × D₈ model. -/
theorem source_hex_even_no_mixed_vertices
    (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    ¬ Nonempty (G₁ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4) ∧
      ¬ Nonempty (G₂ ≃* Equiv.Perm (Fin 3) × DihedralGroup 4) := by
  obtain ⟨⟨a⟩,⟨b⟩⟩ := source_hex_even_vertices h hFstar eT hm
  exact ⟨fun ⟨j⟩ => Locals.not_c2_symmetric_four_equiv_mixed ⟨a.symm.trans j⟩,
    fun ⟨j⟩ => Locals.not_c2_symmetric_four_equiv_mixed ⟨b.symm.trans j⟩⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
