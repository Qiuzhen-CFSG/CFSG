module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Marked
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Counting
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Coordinates

/-!
# Natural multiplicity and the exact upper-layer orders

The two complementary marked subspaces are related by the original
conjugation action, so they have the same binary dimension. A genuine
NaturalLayer with multiplicity s has total dimension 4s; hence its
literal W-image has order 2^(2s). The denominator count then gives
|U|=2^(2s+5)[S₂:V_L], for that same s, including s=0.

The quotient action and complement are constructed from the preceding
structural conclusions. NaturalLayer remains an output to be constructed
by the projective recognition branch, not a source hypothesis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(6–7), printed pp.334–335.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G]

private theorem imageSpace_card {H S E : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) H M}
    (c : Representation.BinaryConjugationSection H S E ρ)
    (B : Subgroup G) (hBS : B ≤ S) :
    Nat.card (c.imageSpace B) = E.relIndex B := by
  change Nat.card ((B.subgroupOf S).map c.coordinates) = _
  rw [← relIndex_ker, c.kernel_eq]
  exact relIndex_subgroupOf hBS

namespace Hypothesis
variable [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The conjugate complementary summands have equal dimensions. Hence s
natural planes give a marked image of order 2^(2s), including s=0. -/
theorem upper_mark_index (hLI : D.L ≤ D.I g)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : Representation (ZMod 2) (D.I g) M)
    (c : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g) ρ)
    {F : Type*} [Field F] (hF : Nat.card F = 4)
    (s : ℕ) (e : M ≃ (Fin s → Fin 2 → F)) :
    (S₂ D g).relIndex (D.W g) = 2 ^ (2 * s) := by
  have : Finite F := Nat.finite_of_card_ne_zero (hF ▸ (by decide : 4 ≠ 0))
  obtain ⟨hc, hconj⟩ := d.upper_marked_complement hLI hsplit hVV ρ c
  have hdim : Module.finrank (ZMod 2) (c.imageSpace (conjugate (D.W g) g)) =
      Module.finrank (ZMod 2) (c.imageSpace (D.W g)) := by
    rw [hconj]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      (ρ.asGroupHom (⟨g, hLI d.g_mem⟩ : D.I g)⁻¹)).finrank_map_eq _
  have htotal := Submodule.finrank_add_eq_of_isCompl hc
  have he : Nat.card M = 2 ^ (4 * s) := by
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, hF,
      show (4 : ℕ) ^ 2 = 2 ^ 4 from rfl, ← pow_mul]
  have hdimM : Module.finrank (ZMod 2) M = 4 * s := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    change 2 ^ Module.finrank (ZMod 2) M = 2 ^ (4 * s)
    rw [← he, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  have hmult : Module.finrank (ZMod 2) (c.imageSpace (D.W g)) = 2 * s := by
    rw [hdim, hdimM] at htotal
    omega
  rw [← imageSpace_card c (D.W g) inf_le_right,
    Module.natCard_eq_pow_finrank (K := ZMod 2), hmult]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- Complementarity of the literal subgroup images under the original
quotient map, independently of natural-module recognition. -/
theorem upperImages_complement
    (hI : D.I g = D.L ⊔ D.U) (hUL : D.star D.U ≤ D.star D.L)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    [((S₂ D g).subgroupOf (D.S g)).Normal] :
    IsCompl (upperImage D g (D.W g)) (upperImage D g (conjugate (D.W g) g)) := by
  have hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  let := d.upper_elementary hLI hcore hsplit
  obtain ⟨σ, c, hq⟩ := d.upper_action hLI hcore hsplit
    (d.upper_actor_le hI) (d.upper_actor_star hI hUL)
  have hc := (d.upper_marked_complement hLI hsplit hVV _ c).1
  rw [upper_imageSpace_eq _ _ σ c hq, upper_imageSpace_eq _ _ σ c hq] at hc
  let f : Subgroup (UpperQuotient D g) ≃o
      Submodule (ZMod 2) (Additive (UpperQuotient D g)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  exact f.symm.isCompl hc

/-- The shared NaturalLayer witness supplies exactly the marked cardinality
needed in clause (7); no independently chosen multiplicity occurs. -/
theorem upperImage_card_of_naturalLayer
    (hI : D.I g = D.L ⊔ D.U) (hUL : D.star D.U ≤ D.star D.L)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    [((S₂ D g).subgroupOf (D.S g)).Normal]
    {F : Type*} [Field F] {s : ℕ}
    (c : NaturalLayer D g F s (le_sup_left.trans hI.ge)) :
    Nat.card (upperImage D g (D.W g)) = 2 ^ (2 * s) := by
  have hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  let := d.upper_elementary hLI hcore hsplit
  obtain ⟨σ, b, _⟩ := d.upper_action hLI hcore hsplit
    (d.upper_actor_le hI) (d.upper_actor_star hI hUL)
  rw [card_upperImage_W]
  exact d.upper_mark_index hLI hsplit hVV _ b c.field_card s
    (Additive.toMul.trans (c.coordinates.toEquiv.trans Multiplicative.toAdd))

/-- The complete counting conclusion from the same NaturalLayer output. -/
theorem order_of_naturalLayer
    (hI : D.I g = D.L ⊔ D.U) (hUL : D.star D.U ≤ D.star D.L)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    (hVU : D.VL ⊓ D.U = D.V) (hV : Nat.card D.V = 8)
    (hUW : (D.W g).relIndex D.U = 4)
    [((S₂ D g).subgroupOf (D.S g)).Normal]
    {F : Type*} [Field F] {s : ℕ}
    (c : NaturalLayer D g F s (le_sup_left.trans hI.ge)) :
    Nat.card D.U = 2 ^ (2 * s + 5) * D.VL.relIndex (S₂ D g) :=
  d.order_of_upper_image (le_sup_left.trans hI.ge) hVU hV hUW s
    (d.upperImage_card_of_naturalLayer hI hUL hcore hsplit hVV c)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
