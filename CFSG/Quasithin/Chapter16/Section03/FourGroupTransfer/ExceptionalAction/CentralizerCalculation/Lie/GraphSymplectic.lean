module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import Theory.SpecificGroups.SymplecticFour.SuzukiFixer

/-!
# The Sp₄–Suzuki pair obstruction from the full automorphism fixer

The actual embedded subgroup L is transported through the supplied PSp₄
isomorphism and the proved characteristic-two comparison PSp₄ ≃ Sp₄. Its
full automorphism fixer embeds in the model fixer, whose order is not
divisible by four by `SymplecticFour.SuzukiFixer`. The given faithful
order-four actor lies in this same fixer, giving the required contradiction
for every m ≥ 1, including the Sz(8) endpoint.

The universal diagram-preserving semilinear classification remains an
explicit premise. Its independent owner must discharge that premise before
the unconditional `LieBounds.graph_field_symplectic` assembly is complete.
The intrinsic obstruction holds for every actual Suzuki embedding, so no
unproved embedding classification or graph-field normal form is used here.

Source: Aschbacher–Smith, 16.1.4(7), 16.1.7(3d), and 16.3.5, combined
manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {G : Type*} [Group G] {E L I : Subgroup G} {t i : G}

/-- Transport of the full-fixer divisibility obstruction to the actual
embedded pair. Semilinear coverage remains an explicit earlier input. -/
theorem pairFixer_four_not_dvd_graph_symplectic_of_semilinear
    (hLI : L ≤ I) (m : ℕ) (hm : 1 ≤ m)
    (hlarge : ClassicalGroup.IsPSp I 2 (2 ^ (2 * m + 1)))
    (hsmall : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (hclass : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∀ a : MulAut (Sp F), PreservesDiagram a →
        ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ) :
    ¬ 4 ∣ Nat.card (pairFixer L I) := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e₀⟩⟩ := hlarge
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let e : I ≃* Sp F := e₀.trans EvenProjective.equiv.symm
  let S : Subgroup (Sp F) := (L.subgroupOf I).map e.toMonoidHom
  obtain ⟨es⟩ := hsmall
  have hS : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    ⟨(e.subgroupMap (L.subgroupOf I)).symm.trans
      ((subgroupOfEquivOfLe hLI).trans es)⟩
  let ψ : pairFixer L I →* fixingSubgroup (MulAut (Sp F)) (S : Set (Sp F)) :=
    ((MulAut.congr e).toMonoidHom.comp (pairFixer L I).subtype).codRestrict _ (by
      intro a
      rw [mem_fixingSubgroup_iff]
      rintro y ⟨x, hx, rfl⟩
      change e (a.val (e.symm (e x))) = e x
      rw [e.symm_apply_apply]
      exact congrArg e (a.property ⟨x, hx⟩))
  have hψ : Function.Injective ψ := fun a b hab =>
    Subtype.ext ((MulAut.congr e).injective (congrArg Subtype.val hab))
  exact fun hd => SuzukiFixer.four_not_dvd_suzuki_fixer m hm hF (hclass F) S hS
    (hd.trans (card_dvd_of_injective ψ hψ))

/-- The graph-field symplectic branch needed by `LieBounds`, conditional
only on the independently owned semilinear classification. The faithful
order-four actor contradicts the actual full-fixer divisibility obstruction. -/
theorem pairFixer_card_lt_four_graph_symplectic_of_semilinear
    (h : PairContext E L I t i) (m : ℕ) (hm : 1 ≤ m)
    (hlarge : ClassicalGroup.IsPSp I 2 (2 ^ (2 * m + 1)))
    (hsmall : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (hclass : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      ∀ a : MulAut (Sp F), PreservesDiagram a →
        ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ) :
    Nat.card (pairFixer L I) < 4 := by
  let f : E →* pairFixer L I := (inducedAction E I h.normalizes).codRestrict _ (by
    intro e
    rw [pairFixer, mem_fixingSubgroup_iff]
    intro x hx
    apply Subtype.ext
    change (e : G) * (x : G) * (e : G)⁻¹ = (x : G)
    rw [← mem_centralizer_iff.mp (h.centralizes e.property) x hx]
    group)
  have hf : Function.Injective f := fun a b hab =>
    h.faithful (congrArg Subtype.val hab)
  have hd : 4 ∣ Nat.card (pairFixer L I) := by
    rw [← h.card]
    exact card_dvd_of_injective f hf
  exact (pairFixer_four_not_dvd_graph_symplectic_of_semilinear
    h.proper.le m hm hlarge hsmall hclass hd).elim

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
