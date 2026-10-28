module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.Cardinality
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.InvariantLine.Frattini
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The elementary-core argument from hyperplane supports

The preceding D.2.13 hyperplane conclusions bound each invariant central
order-three line's moved support by dimension four. The actual three-group
image on that support is elementary abelian, so the Frattini subgroup fixes
the support and cannot contain the line. A nontrivial Frattini subgroup
would contain just such an invariant central line. Thus the Frattini subgroup
is trivial and the core is elementary abelian. The hyperplane centralizer
orders and faithful four-group action give order nine or 27; a vector-space
basis constructs the actual product equivalence. Coprime decomposition gives
the full commutator conclusion.

Source: Aschbacher--Smith, D.2.14(2), printed p.186. This completes the
conditional elementary-core argument. The earlier-source owner
`qt-d-02-fitting-offenders` must supply `HyperplaneSupport`, the faithful
four-group action, and the trivial common centralizer. Normalization by A
suffices here; the source's normality of P is not needed separately.
-/

public section
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The order and commutator parts of the conditional core contract, on the
given subgroups, without an elementarity assumption. -/
theorem order_and_commutator_of_hyperplaneSupport
    (P A : Subgroup G) (hP : IsPGroup 3 P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hn : A ≤ normalizer (P : Set G))
    (hf : A ⊓ centralizer (P : Set G) = ⊥)
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ P A) :
    (∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card P = 3 ^ s) ∧ ⁅P, A⁆ = P := by
  exact ⟨exists_card_exponent P A hP hA hn hf (fun B hBA hr hD =>
    (hs B hBA hr hD).1), commutator_eq P A hP hA hn hfix⟩

/-- The fixed-space support supplied by D.2.13 applies to the literal
invariant order-three line, with its actual actor centralizer. -/
theorem line_fixed_support (P A Z : Subgroup G) (hA : Nat.card A = 4)
    (hZP : Z ≤ P) (hZ : Nat.card Z = 3)
    (hnZ : A ≤ normalizer (Z : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ P A) :
    let B := A ⊓ centralizer (Z : Set G)
    Nat.card B = 2 ∧ rank B = 1 ∧ P ⊓ centralizer (B : Set G) = Z ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) Z) = 2 := by
  dsimp only
  obtain ⟨hr, he⟩ := line_eq_hyperplane_centralizer P A Z hA hZP hZ hnZ hfix
    (fun B hBA hr hD => (hs B hBA hr hD).1)
  refine ⟨line_centralizer_card P A Z hA hZP hZ hnZ hfix, hr, he, ?_⟩
  have hZne : Z ≠ ⊥ := by
    intro hb
    have hZ1 : Nat.card Z = 1 := card_eq_one.mpr hb
    omega
  have hd := (hs (A ⊓ centralizer (Z : Set G)) inf_le_left hr
    (fun hb => hZne (he.symm.trans hb))).2
  have hdim := congrArg (fun D : Subgroup G => Module.finrank (ZMod 2)
    (subspaceCommutator ρ (fixedSpace ρ (A ⊓ centralizer (Z : Set G))) D)) he
  exact hdim.symm.trans hd

variable [FiniteDimensional (ZMod 2) V]

/-- Hyperplane supports exclude every invariant central line from Φ(P),
discharging the line-exclusion premise and proving elementarity. -/
theorem frattini_eq_bot_and_isElementaryAbelian_of_hyperplaneSupport
    (hρ : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hn : A ≤ normalizer (P : Set G))
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ P A) :
    frattini P = ⊥ ∧ IsElementaryAbelian 3 P := by
  apply frattini_eq_bot_and_isElementaryAbelian_of_line_exclusion P A hP hA hn
  intro Z hcentral hZ hnZ
  exact central_line_not_le_frattini ρ hρ P A Z hP hA hcentral hZ hnZ hfix hs

/-- The full conditional elementary-core conclusion of D.2.14(2), including
an actual equivalence to two or three cyclic groups of order three.
No invariant-line, Frattini, or restricted-image premise remains. -/
theorem elementary_structure_of_hyperplaneSupport (hρ : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) (hn : A ≤ normalizer (P : Set G))
    (hf : A ⊓ centralizer (P : Set G) = ⊥)
    (hfix : P ⊓ centralizer (A : Set G) = ⊥)
    (hs : HyperplaneSupport ρ P A) :
    IsElementaryAbelian 3 P ∧
      (∃ s : ℕ, (s = 2 ∨ s = 3) ∧ Nat.card P = 3 ^ s ∧
        Nonempty (P ≃* (Fin s → Multiplicative (ZMod 3)))) ∧ ⁅P, A⁆ = P := by
  have hElem := (frattini_eq_bot_and_isElementaryAbelian_of_hyperplaneSupport
    ρ hρ P A hP hA hn hfix hs).2
  let : IsElementaryAbelian 3 P := hElem
  obtain ⟨⟨s, hs, hcard⟩, hcomm⟩ :=
    order_and_commutator_of_hyperplaneSupport ρ P A hP hA hn hf hfix hs
  refine ⟨hElem, ⟨s, hs, hcard, ?_⟩, hcomm⟩
  have hdim : Module.finrank (ZMod 3) (Additive P) = s := by
    apply Nat.pow_right_injective (by decide : 1 < 3)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive P)
    change Nat.card P = _ at hc
    simpa only [Nat.card_zmod] using hc.symm.trans hcard
  let b := Module.finBasisOfFinrankEq (ZMod 3) (Additive P) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight.trans
    (MulEquiv.piMultiplicative fun _ : Fin s => ZMod 3)⟩

end CFSG.Quasithin.ChapterD.ElementaryCore
