module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OrderRecognition
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# The initial natural layer for arbitrary nonbinary Sp₄

The complete B.5.1 FF classification reduces to its irreducible row by the
classical group orders. In B.4.2 the only remaining action is the natural
symplectic module, and its field degree equals the original quotient degree.
Transport through the offender-generated subgroup identifies the canonical
moved section modulo its fixed part for the original ambient action.

No restriction to the field of order four or splitting of the fixed layer is
assumed. These initial-layer results precede the whole-core pushing-up proof.
Source: Aschbacher--Smith B.4.2, B.5.1 and C.1.32; MS93 (3.2)(vi).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite G] in
/-- The complete B.4.2 list has only the natural Sp₄ row at the order of the
supplied nonbinary symplectic quotient. -/
theorem irreducible_card_sp_natural
    (ρ : Representation (ZMod 2) G V) (L H : Subgroup G)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hfield : Nat.card F = 2^n) (hn : 1 < n)
    (hc : Nat.card L = Nat.card (Matrix.symplecticGroup (Fin 2) F))
    (hs : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    ∃ E : BinaryField, E.degree = n ∧
      Nonempty (ActionEquiv (ρ.comp L.subtype) (binarySymplectic E)) := by
  cases hs with
  | linearTwo E _ e _ _ =>
    exact (card_symplectic_ne_sl_two F hfield (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | linearThree E _ e _ =>
    exact (card_symplectic_ne_sl_three F hfield (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | symplectic E _ _ e _ =>
    exact ⟨E, degree_eq_of_card_symplectic F hfield (by omega) E
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm, ⟨e⟩⟩
  | symplecticTwo e _ =>
    have hh := (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hh
    have hlo := card_symplectic_ge F hfield hn
    rw [←hc] at hlo
    norm_num at hh
    omega
  | g2 E _ _ e _ _ =>
    exact (card_symplectic_ne_g2 F hfield (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | g2Two e _ _ =>
    have hh := (commutator (Atlas.G2.Model (ZMod 2))).card_le_card_group
    rw [← Nat.card_congr e.subgroupEquiv.toEquiv, Atlas.G2.card_Model] at hh
    norm_num at hh
    have hlo := card_symplectic_ge F hfield hn
    rw [←hc] at hlo
    omega
  | symmetric d hd e _ _ =>
    exact (card_symplectic_ne_alternating F hfield hn
      (by rcases hd with h|h <;> simp [h]))
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | alternatingSix _ e _ _ =>
    exact (card_symplectic_ne_alternating F hfield hn (by simp))
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (card_symplectic_ne_alternating F hfield hn (by simp))
      ((Nat.card_congr e.toEquiv).symm.trans hc).symm |>.elim
  | tripleSix _ a _ =>
    have hq := Nat.card_congr a.quotientEquiv.toEquiv
    have hz := Nat.card_congr a.centerEquiv.toEquiv
    have hh := card_eq_card_quotient_mul_card_subgroup (center L)
    rw [hq, hz, nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    have hlo := card_symplectic_ge F hfield hn
    rw [←hc] at hlo
    omega
  | binaryLinear d hd _ e _ =>
    exact (card_symplectic_ne_binary_higher F hfield (by omega) hd)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | orthogonalSix _ _ e _ _ =>
    exact (card_symplectic_ne_alternating F hfield hn (by simp))
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | symmetricEight _ e _ =>
    exact (card_symplectic_ne_alternating F hfield hn (by simp))
      ((Nat.card_congr e.subgroupEquiv.toEquiv).symm.trans hc).symm |>.elim
  | exteriorFive _ _ e _ _ _ =>
    exact (card_symplectic_ne_binary_higher F hfield (by omega) (by simp))
      ((Nat.card_congr e.toEquiv).symm.trans hc).symm |>.elim

variable [Module.Finite (ZMod 2) V]

/-- The full FF classification recognizes the moved quotient for arbitrary
nonbinary symplectic order; the canonical section retains its actual action. -/
theorem ff_card_sp_moved_natural
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsSimpleGroup L] [IsQuasisimple L]
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hfield : Nat.card F = 2^n) (hn : 1 < n)
    (hc : Nat.card L = Nat.card (Matrix.symplecticGroup (Fin 2) F))
    (hC : centralizer (L : Set G) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple L)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L) ∧
      ∃ E : BinaryField, E.degree = n ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ L).action.comp L.subtype)
          (binarySymplectic E)) := by
  obtain ⟨hLJ,⟨c⟩⟩ := SourceCompletion.ff_socle_source_conclusion ρ L hC hsq hf hff
  have hc' : Nat.card (L.subgroupOf (offenderSubgroup ρ)) =
      Nat.card (Matrix.symplecticGroup (Fin 2) F) :=
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
      irreducible_card_sp_natural _ _ _ F hfield hn hc' hs
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
    exact (card_symplectic_ne_sl_three F hfield (by omega) E)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc').symm |>.elim
  | naturalDual d hd _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (card_symplectic_ne_binary_higher F hfield (by omega) hd)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc').symm |>.elim
  | repeatedNatural d r hd _ _ _ hn' =>
    obtain ⟨e⟩ := hn'
    exact (card_symplectic_ne_binary_higher F hfield (by omega) hd)
      ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hc').symm |>.elim

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
