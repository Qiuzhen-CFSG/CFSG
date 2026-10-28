module
public import Theory.Representation.SymplecticNaturalNormalizer.MovedPlane
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.ComponentBounds
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import Theory.Representation.Quotient
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.SourceBound
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Excluding whole nonbinary symplectic components

The original component degree bound supplies the proved natural-recognition
window. Its genuine group and module equivalences transport the entire ambient
action to the normalizer of the natural Sp4 module. Every rank-two involution
there has a transitive moved-plane stabilizer, contrary to the strict marking.
The actual projective carrier is identified with the full derived matrix group
in characteristic two; the original actor and representation are retained.

`StrictWholePair` applies the exclusion to the original strict quotient.
Source: Aschbacher--Smith G.9.3(9), G.11.7 and 6.2.19,
printed pp.354,367,691.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair.Ambient

open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholeSymplectic
open Section09.DefiningCharacteristic.SymplecticFourRecognition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X} {C : GroupClass}
  {F : Type*} [Field F] [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

set_option backward.isDefEq.respectTransparency false in
/-- Natural recognition excludes the whole nonbinary symplectic component
using the original nontransitive moved plane. -/
theorem not_nonbinary
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) F))
    {n : ℕ} (hn : 2≤n) (hF : Nat.card F=2^n)
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) : False := by
  let := h9.normal_H
  have hd := component_degree_window_of_automorphism_rank h9 e
    (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_automorphism_rank_le hF hn)
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  obtain ⟨b,f,hf⟩ := quasiequivalent_of_comp_equiv e
    (Nonbinary.small_quasiequivalent hn hF hf hd.2)
  let τ : Representation (ZMod 2) G (Theory.SpecificGroups.SymplecticFour.Vector F) :=
    f.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : G) (u : V) : f (ρ g u)=τ g (f u) := by
    change f (ρ g u)=f (ρ g (f.symm (f u)))
    rw [f.symm_apply_apply]
  let := Theory.SpecificGroups.SymplecticFour.perfect_of_card_gt_two
    (show 2<Nat.card F by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 0<2) hn
      omega)
  let ef : commutator (Sp F) ≃* Sp F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  let e' := b.trans ef
  have hL (l : L) (w : Theory.SpecificGroups.SymplecticFour.Vector F) :
      τ (l:G) w=symplecticNatural 2 (e' l) w := by
    change f (ρ l (f.symm w))=_
    have hh := hf l (f.symm w)
    change f (ρ l (f.symm w))=symplecticNatural 2 (b l).val (f (f.symm w)) at hh
    rw [f.apply_symm_apply] at hh
    exact hh
  have hr' := (RankTwo.finrank_movedSpace_transport ρ τ (MulEquiv.refl G) f he a).symm.trans hr
  exact hnt (RankTwo.stabilizerTransitive_transport ρ τ (MulEquiv.refl G) f he a
    (SymplecticNaturalNormalizer.stabilizerTransitive_of_rank_two τ L e' hL hn hF a ha hr'))

/-- The source projective carrier is transported through the actual
characteristic-two symplectic quotient. -/
theorem not_nonbinary_model
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    {n : ℕ} (hn : 2≤n) (hm : ClassicalGroup.IsPSp L 2 (2^n))
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact not_nonbinary h h9
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm.trans
      (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn).symm))
    hn hF a ha hr hnt
end CFSG.Quasithin.ChapterG.Section11.WholeSymplectic
