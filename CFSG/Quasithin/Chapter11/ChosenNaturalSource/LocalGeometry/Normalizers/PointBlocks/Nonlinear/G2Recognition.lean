module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Orders
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# The natural exceptional layer in the original point pair

The complete B.5.1 FF classification, combined with the actual G₂ quotient
order, leaves exactly the exceptional natural row. This preserves the degree
of the original field and transports its marked action from the offender
generated subgroup to the original moved/fixed section.

The fixed part is retained. No field-four restriction, splitting, or whole-core
recognition is assumed. The point application in G2Initial supplies every
hypothesis from its literal nonbinary MS pair.
Source: Aschbacher--Smith B.4.2, B.5.1 and 11.1.5; MS93 (3.2).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
open ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- The complete B.4.2 list has only the natural G₂ row at the order of the
supplied nonbinary exceptional quotient. -/
theorem irreducible_card_g2_natural
    (ρ : Representation (ZMod 2) G V) (L H : Subgroup G)
    (F : BinaryField) (hn : 1 < F.degree)
    (hc : Nat.card L = Nat.card (Atlas.G2.Model F.Carrier))
    (hs : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    ∃ E : BinaryField, E.degree = F.degree ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (binaryG2 E)) := by
  cases hs with
  | linearTwo E _ e _ _ =>
    exact (card_g2_ne_sl_two F.Carrier F.card_eq (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | linearThree E _ e _ =>
    exact (card_g2_ne_sl_three F.Carrier F.card_eq (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | symplectic E _ _ e _ =>
    exact (ChapterC.RankTwo.NonbinarySymplectic.card_symplectic_ne_g2
      E.Carrier E.card_eq E.degree_pos F)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc) |>.elim
  | symplecticTwo e _ =>
    have hh := (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hh
    have hlo := card_g2_ge F.Carrier F.card_eq hn
    rw [←hc] at hlo
    norm_num at hh
    omega
  | g2 E _ _ e _ _ =>
    exact ⟨E, degree_eq_of_card_g2 F.Carrier F.card_eq F.degree_pos E
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm, ⟨e⟩⟩
  | g2Two e _ _ =>
    have hh := (commutator (Atlas.G2.Model (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv, Atlas.G2.card_Model] at hh
    norm_num at hh
    have hlo := card_g2_ge F.Carrier F.card_eq hn
    rw [←hc] at hlo
    omega
  | symmetric d hd e _ _ =>
    exact (card_g2_ne_alternating F.Carrier F.card_eq hn
      (by rcases hd with h|h <;> simp [h]))
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | alternatingSix _ e _ _ =>
    exact (card_g2_ne_alternating F.Carrier F.card_eq hn (by simp))
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (card_g2_ne_alternating F.Carrier F.card_eq hn (by simp))
      ((Nat.card_congr e.toEquiv).symm.trans hc).symm |>.elim
  | tripleSix _ a _ =>
    have hq := Nat.card_congr a.quotientEquiv.toEquiv
    have hz := Nat.card_congr a.centerEquiv.toEquiv
    have hh := card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hq, hz, nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    have hlo := card_g2_ge F.Carrier F.card_eq hn
    rw [←hc] at hlo
    omega
  | binaryLinear d hd _ e _ =>
    exact (card_g2_ne_binary_higher F.Carrier F.card_eq hn hd)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | orthogonalSix _ _ e _ _ =>
    exact (card_g2_ne_alternating F.Carrier F.card_eq hn (by simp))
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | symmetricEight _ e _ =>
    exact (card_g2_ne_alternating F.Carrier F.card_eq hn (by simp))
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | exteriorFive _ _ e _ _ _ =>
    exact (card_g2_ne_binary_higher F.Carrier F.card_eq hn (by simp))
      ((Nat.card_congr e.toEquiv).symm.trans hc).symm |>.elim

variable [Module.Finite (ZMod 2) V]

/-- The full FF classification recognizes the moved quotient for arbitrary
nonbinary exceptional order; the canonical section retains its actual action. -/
theorem ff_card_g2_moved_natural
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (F : BinaryField) (hn : 1 < F.degree)
    (hc : Nat.card L = Nat.card (Atlas.G2.Model F.Carrier))
    (hC : centralizer (L : Set G) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L) ∧
      ∃ E : BinaryField, E.degree = F.degree ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ L).action.comp L.subtype)
          (binaryG2 E)) := by
  obtain ⟨hLJ,⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ L hC hsq hf hff
  have hc' : Nat.card (L.subgroupOf (offenderSubgroup ρ)) =
      Nat.card (Atlas.G2.Model F.Carrier) :=
    (Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv).trans hc
  cases c.clause_one with
  | irreducible hi _ _ hs _ =>
    have hi' := hi
    rw [c.sectionData.space_eq] at hi'
    change IsIrrPlus _ _ (subspaceCommutator (ρ.comp (offenderSubgroup ρ).subtype) ⊤
      (L.subgroupOf (offenderSubgroup ρ))) at hi'
    change IsIrrPlus _ _ (moved (ρ.comp (offenderSubgroup ρ).subtype)
      (L.subgroupOf (offenderSubgroup ρ))) at hi'
    rw [moved_comp_map, map_subgroupOf_eq_of_le hLJ] at hi'
    have hi'' := (IsIrrPlus.subgroupOf_iff ρ L (offenderSubgroup ρ) hLJ _).mp hi'
    obtain ⟨E, hdegree, ⟨A⟩⟩ :=
      irreducible_card_g2_natural _ _ _ F hn hc' hs
    let D := L.subgroupOf (offenderSubgroup ρ)
    let φ : L ≃* D := (subgroupOfEquivOfLe hLJ).symm
    have hm : (moved ρ L).map (LinearMap.id : V →ₗ[ZMod 2] V) =
        moved (ρ.comp (offenderSubgroup ρ).subtype) D := by
      rw [Submodule.map_id, moved_comp_map, map_subgroupOf_eq_of_le hLJ]
    let T := c.sectionData.componentEmbeddingEquiv (MovedSection.ofNormal ρ L) φ
      (LinearMap.id : V →ₗ[ZMod 2] V) (fun _ _ h => h) (fun _ _ => rfl) hm
    refine ⟨hi'', E, hdegree, ⟨?_⟩⟩
    exact ⟨T.groupEquiv.trans A.groupEquiv, T.linearEquiv.trans A.linearEquiv,
      fun g v => by
        change A.linearEquiv (T.linearEquiv (_)) = _
        rw [T.intertwines, A.intertwines]
        rfl⟩
  | doubleThree E _ e _ _ =>
    exact (card_g2_ne_sl_three F.Carrier F.card_eq (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc').symm |>.elim
  | naturalDual d hd _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (card_g2_ne_binary_higher F.Carrier F.card_eq hn hd)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc').symm |>.elim
  | repeatedNatural d r hd _ _ _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (card_g2_ne_binary_higher F.Carrier F.card_eq hn hd)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc').symm |>.elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
