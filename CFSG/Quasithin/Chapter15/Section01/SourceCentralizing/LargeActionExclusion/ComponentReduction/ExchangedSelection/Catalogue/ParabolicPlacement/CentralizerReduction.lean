module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.Definitions
public import Theory.GroupTheory.NormalizerAction.OmegaCenterCentralizer

/-!
# The faithful-image step of original 15.1.22(**)

The actual N_S(L) normalizes O^{3′}(M ∩ L), hence normalizes its
centralizer in S. In the literal plus quotient an order-two omega center
detects every nontrivial normal subgroup. Thus movement of this center
kills the image of the residual centralizer.

Normalization of L by that centralizer and movement in the plus quotient
are explicit earlier obligations here. They are not consequences of merely
knowing that S is a two-group, and this reduction does not assert (**).
Source: Aschbacher--Smith, printed p.1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem localThreeResidual_le_component (d : CaseIComponentData T M Mc V) :
    d.localThreeResidual ≤ d.L := (map_subtype_le _).trans inf_le_right

/-- N_S(L), not S, preserves the original local residual. -/
theorem sylowNormalizer_normalizes_localThreeResidual
    (d : CaseIComponentData T M Mc V) (hTM : (T : Subgroup G) ≤ M) :
    d.sylowNormalizer ≤ normalizer (d.localThreeResidual : Set G) := by
  have hn : d.sylowNormalizer ≤ normalizer (M ⊓ d.L : Set G) :=
    (le_inf ((inf_le_left.trans (d.S_le_T.trans hTM)).trans M.le_normalizer)
      inf_le_right).trans inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (M ⊓ d.L) (primeToResidual 3 (M ⊓ d.L : Subgroup G)))

/-- The quotient kills precisely the centralizer of L on any subgroup
known to lie in the actual normalizer G_L. -/
theorem plus_eq_bot_iff (d : CaseIComponentData T M Mc V)
    (A : Subgroup G) (hA : A ≤ d.componentNormalizer) :
    d.plus A = ⊥ ↔ A ≤ centralizer (d.L : Set G) := by
  rw [plus, Subgroup.map_eq_bot_iff]
  constructor
  · intro hh x hx
    have he := hh (show (⟨x,hA hx⟩ : d.componentNormalizer) ∈
      A.subgroupOf d.componentNormalizer from hx)
    exact (QuotientGroup.eq_one_iff (N := d.componentKernel)
      (⟨x,hA hx⟩ : d.componentNormalizer)).mp he
  · intro hh x hx
    exact (QuotientGroup.eq_one_iff (N := d.componentKernel) x).mpr (hh hx)

theorem plus_normalizes (d : CaseIComponentData T M Mc V)
    (A B : Subgroup G) (hn : A ≤ normalizer (B : Set G)) :
    d.plus A ≤ normalizer (d.plus B : Set d.ComponentPlus) := by
  exact (map_mono ((comap_mono hn).trans
    (le_normalizer_comap d.componentNormalizer.subtype))).trans (le_normalizer_map _)

theorem plus_centralizes (d : CaseIComponentData T M Mc V)
    (A B : Subgroup G) (hc : A ≤ centralizer (B : Set G)) :
    d.plus A ≤ centralizer (d.plus B : Set d.ComponentPlus) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
  exact congrArg d.plusMap (Subtype.ext (hc ha b hb))

/-- The normalizer part of the residual centralizer always dies in the
plus quotient once the order-two center is moved. -/
theorem localThreeResidual_centralizer_in_normalizer
    (d : CaseIComponentData T M Mc V) (hTM : (T : Subgroup G) ≤ M)
    (hcard : Nat.card d.plusOmega = 2)
    (hmove : ¬ d.plusOmega ≤ centralizer (d.plus d.localThreeResidual : Set d.ComponentPlus)) :
    d.sylowNormalizer ⊓ centralizer (d.localThreeResidual : Set G) =
      d.S ⊓ centralizer (d.L : Set G) := by
  let A := d.plus d.sylowNormalizer
  have hp : IsPGroup 2 A :=
    ((T.isPGroup'.to_le ((inf_le_left : d.sylowNormalizer ≤ d.S).trans
      d.S_le_T)).comap_subtype).map d.plusMap
  have hc : Nat.card (omega₁ (center A) (p := 2)) = 2 := by
    change Nat.card (((omega₁ (center A) (p := 2)).map
      (center A).subtype).map A.subtype) = 2 at hcard
    rwa [card_map_of_injective A.subtype_injective,
      card_map_of_injective (center A).subtype_injective] at hcard
  have hbot := inf_centralizer_eq_bot_of_omega_center_escape A
    (d.plus d.localThreeResidual) hp
    (d.plus_normalizes _ _ (d.sylowNormalizer_normalizes_localThreeResidual hTM)) hc hmove
  have hk : d.plus (d.sylowNormalizer ⊓ centralizer (d.localThreeResidual : Set G)) = ⊥ := by
    apply bot_unique
    apply le_trans _ hbot.le
    exact le_inf (map_mono (comap_mono inf_le_left))
      (d.plus_centralizes _ _ inf_le_right)
  have hC := (d.plus_eq_bot_iff _
    (inf_le_left.trans d.sylowNormalizer_le_componentNormalizer)).mp hk
  apply le_antisymm (le_inf (inf_le_left.trans inf_le_left) hC)
  rintro x ⟨hx,hc⟩
  exact ⟨⟨hx,Subgroup.centralizer_le_normalizer _ hc⟩,
    centralizer_le d.localThreeResidual_le_component hc⟩

/-- The exact remaining normalizer obligation promotes the faithful-image
calculation to the full source centralizer in S. -/
theorem localThreeResidual_centralizer_of_plus_movement
    (d : CaseIComponentData T M Mc V) (hTM : (T : Subgroup G) ≤ M)
    (hcard : Nat.card d.plusOmega = 2)
    (hmove : ¬ d.plusOmega ≤ centralizer (d.plus d.localThreeResidual : Set d.ComponentPlus))
    (hn : d.S ⊓ centralizer (d.localThreeResidual : Set G) ≤ normalizer (d.L : Set G)) :
    d.S ⊓ centralizer (d.localThreeResidual : Set G) =
      d.S ⊓ centralizer (d.L : Set G) := by
  rw [←d.localThreeResidual_centralizer_in_normalizer hTM hcard hmove]
  exact le_antisymm (fun x hx => ⟨⟨hx.1,hn hx⟩,hx.2⟩)
    (fun x hx => ⟨hx.1.1,hx.2⟩)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
