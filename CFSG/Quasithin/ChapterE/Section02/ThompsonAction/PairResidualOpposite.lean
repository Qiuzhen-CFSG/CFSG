module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualCentralizers
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualControl

/-!
# A commuting conjugate occupies the opposite marked alternating axis

The original paired residuals are permuted by every ambient conjugator.
Their alternating images are nonabelian, so two commuting conjugates
cannot occupy the same axis. This keeps the prescribed conjugator and
the original marking, rather than selecting a replacement exchanger.

Source: Aschbacher–Smith 10.2.1, pp.742–743, with the E.2.3 pair.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private theorem left_axis_noncommutative :
    ⁅(A5).prod (⊥ : Subgroup S5),(A5).prod (⊥ : Subgroup S5)⁆ ≠ ⊥ := by
  intro h
  have hh := commutator_eq_bot_iff_le_centralizer.mp h
  rw [Theory.SymmetricFiveProduct.centralizer_left_alternating_axis] at hh
  have hz : (A5) = ⊥ := bot_unique (fun a ha =>
    (hh (show (a,1) ∈ (A5).prod (⊥ : Subgroup S5) from ⟨ha,one_mem _⟩)).1)
  have hcard := congrArg (fun K : Subgroup S5 => Nat.card K) hz
  rw [nat_card_alternatingGroup,card_bot] at hcard
  norm_num [Nat.factorial] at hcard

private theorem right_axis_noncommutative :
    ⁅(⊥ : Subgroup S5).prod (A5),(⊥ : Subgroup S5).prod (A5)⁆ ≠ ⊥ := by
  intro h
  have hh := commutator_eq_bot_iff_le_centralizer.mp h
  rw [Theory.SymmetricFiveProduct.centralizer_right_alternating_axis] at hh
  have hz : (A5) = ⊥ := bot_unique (fun a ha =>
    (hh (show (1,a) ∈ (⊥ : Subgroup S5).prod (A5) from ⟨one_mem _,ha⟩)).2)
  have hcard := congrArg (fun K : Subgroup S5 => Nat.card K) hz
  rw [nat_card_alternatingGroup,card_bot] at hcard
  norm_num [Nat.factorial] at hcard

private theorem conjugate_images_eq {G H : Type*} [Group G] [Group H]
    (q : G →* H) (A B : Subgroup G) (t : G) (h : A.map q = B.map q) :
    (A.map (MulAut.conj t).toMonoidHom).map q =
      (B.map (MulAut.conj t).toMonoidHom).map q := by
  have he : q.comp (MulAut.conj t).toMonoidHom =
      (MulAut.conj (q t)).toMonoidHom.comp q := by
    ext x
    change q (t * x * t⁻¹) = q t * q x * (q t)⁻¹
    rw [map_mul,map_mul,map_inv]
  rw [map_map,map_map,he,←map_map,←map_map,h]

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- Any prescribed commuting conjugate occupies the other residual axis. -/
theorem paired_symmetric_commuting_conjugate_opposite
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (A : Subgroup G) (t : G)
    (hc : ⁅A,A.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (him : let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
      A.map q = (factorResidual q Y d.first).map q ∨
        A.map q = (factorResidual q Y d.second).map q) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    let B := A.map (MulAut.conj t).toMonoidHom
    (A.map q = (factorResidual q Y d.first).map q ∧
      B.map q = (factorResidual q Y d.second).map q) ∨
    (A.map q = (factorResidual q Y d.second).map q ∧
      B.map q = (factorResidual q Y d.first).map q) := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup ρ
  let K₁ := factorResidual q Y d.first
  let K₂ := factorResidual q Y d.second
  let B := A.map (MulAut.conj t).toMonoidHom
  let f := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp c.action.groupEquiv.symm.injective
  have hn₁ : ⁅K₁.map q,K₁.map q⁆ ≠ ⊥ := by
    rw [paired_symmetric_first_residual_image ρ q hq d c,←map_commutator]
    exact fun h => left_axis_noncommutative
      ((map_eq_bot_iff_of_injective _ hf).mp h)
  have hn₂ : ⁅K₂.map q,K₂.map q⁆ ≠ ⊥ := by
    rw [paired_symmetric_second_residual_image ρ q hq d c,←map_commutator]
    exact fun h => right_axis_noncommutative
      ((map_eq_bot_iff_of_injective _ hf).mp h)
  have hcomm : ⁅A.map q,B.map q⁆ = ⊥ := by rw [←map_commutator,hc,Subgroup.map_bot]
  have hp := paired_residual_factors_permuted U hU q hq hk d t
  rcases him with h | h
  · have hm := conjugate_images_eq q A K₁ t h
    rcases hp with hp | hp
    · have he : B.map q = K₁.map q := hm.trans (congrArg (map q) hp.1)
      exact False.elim (hn₁ (by simpa only [h,he] using hcomm))
    · exact Or.inl ⟨h,hm.trans (congrArg (map q) hp.1)⟩
  · have hm := conjugate_images_eq q A K₂ t h
    rcases hp with hp | hp
    · have he : B.map q = K₂.map q := hm.trans (congrArg (map q) hp.2)
      exact False.elim (hn₂ (by simpa only [h,he] using hcomm))
    · exact Or.inr ⟨h,hm.trans (congrArg (map q) hp.2)⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
