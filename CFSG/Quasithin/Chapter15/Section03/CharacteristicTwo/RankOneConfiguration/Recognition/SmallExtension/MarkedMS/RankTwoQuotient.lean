module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The central-core quotient in the small marked models

The component star map factors through L/O₂(L). Since that quotient is
quasisimple and the three actual marked models are centerless, the kernel
of the induced surjection is exactly its center. This constructs
L/O₂,Z(L) ≃ L* with the original quotient map retained. The resulting
isomorphisms to actual derived rank-two carriers supply the last model
condition of MS1 without assuming simplicity of L/O₂(L).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31,
printed p.135; 15.3.26(2), 15.3.28(2), and 15.3.31, pp.1130–1132.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G]

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  exact e.map_eq_one_iff.mp (hz.le ((centerCongr e ⟨x, hx⟩).property))

/-- Every one of the actual three marked models is centerless. -/
theorem marked_star_center (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hm : Parabolics.SmallParabolicMarking d I c.L) :
    center (d.starImage I c.L) = ⊥ := by
  cases hm with
  | linearThree m => exact center_eq_bot_of_equiv m.equiv Matrix.PSL3Two.center_eq_bot
  | symplecticDerived m =>
    apply center_eq_bot_of_equiv (m.equiv.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
    exact alternatingGroup.center_eq_bot (by simp)
  | g2Derived m =>
    exact center_eq_bot_of_equiv m.equiv Theory.SpecificGroups.g2_derived_two_center_eq_bot

/-- A surjection from a quasisimple group onto a nontrivial centerless group
has kernel exactly the center. This supplies the central quotient comparison. -/
theorem ker_eq_center_of_quasisimple {A B : Type*} [Group A] [Group B]
    [IsQuasisimple A] [Nontrivial B] (f : A →* B) (hf : Function.Surjective f)
    (hz : center B = ⊥) : f.ker = center A := by
  apply le_antisymm
  · rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with h | h
    · exact h
    · have he : f = 1 := MonoidHom.ker_eq_top_iff.mp h
      obtain ⟨b, hb⟩ := exists_ne (1 : B)
      obtain ⟨a, rfl⟩ := hf b
      exact (hb (by rw [he]; rfl)).elim
  · intro x hx
    apply hz.le
    apply mem_center_iff.mpr
    intro b
    obtain ⟨a, rfl⟩ := hf b
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hx a)

/-- The O₂,Z quotient, before simplicity of the full O₂ quotient is known,
is canonically the marked star group. -/
noncomputable def centralCoreQuotientEquivStar (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    (c.L ⧸ centralPreimage (pCore 2 c.L)) ≃* d.starImage I c.L := by
  let f := QuotientGroup.lift (pCore 2 c.L) (componentMap d c)
    (core_le_componentMap_ker d c (component_core_centralizes_span d c hnormal P hP))
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective _ _ (componentMap_surjective d c) _
  let := c.core_quotient_quasisimple
  let : Nontrivial (d.starImage I c.L) :=
    (nontrivial_iff_ne_bot _).mpr (component_star_ne_bot d c)
  have hk : f.ker = center (c.L ⧸ pCore 2 c.L) := by
    exact ker_eq_center_of_quasisimple f hf (marked_star_center d c hm)
  have hkcomp : (componentMap d c).ker = centralPreimage (pCore 2 c.L) := by
    change (componentMap d c).ker = (center (c.L ⧸ pCore 2 c.L)).comap
      (QuotientGroup.mk' (pCore 2 c.L))
    rw [← hk]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hkcomp.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (componentMap d c)
      (componentMap_surjective d c))

/-- Compatibility of the central-core comparison with the original star map. -/
theorem centralCoreQuotientEquivStar_apply (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hm : Parabolics.SmallParabolicMarking d I c.L) (l : c.L) :
    centralCoreQuotientEquivStar d c hnormal P hP hm
      (QuotientGroup.mk' (centralPreimage (pCore 2 c.L)) l) = componentMap d c l := by
  rfl

/-- The small rank-two specialization of MS1, using actual derived carriers. -/
def SmallRankTwoQuotient (L : Type*) [Group L] : Prop :=
  Nonempty ((L ⧸ centralPreimage (pCore 2 L)) ≃*
    commutator (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ∨
  Nonempty ((L ⧸ centralPreimage (pCore 2 L)) ≃*
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) ∨
  Nonempty ((L ⧸ centralPreimage (pCore 2 L)) ≃*
    commutator (Atlas.G2.Model (ZMod 2)))

/-- The marked source alternative supplies the rank-two quotient condition
without assuming simplicity of L/O₂(L). -/
theorem smallRankTwoQuotient_of_marking (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hm : Parabolics.SmallParabolicMarking d I c.L) : SmallRankTwoQuotient c.L := by
  let e := centralCoreQuotientEquivStar d c hnormal P hP hm
  cases hm with
  | linearThree m =>
    let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
    exact Or.inl ⟨(e.trans m.equiv).trans (topEquiv.symm.trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩
  | symplecticDerived m => exact Or.inr (Or.inl ⟨e.trans m.equiv⟩)
  | g2Derived m => exact Or.inr (Or.inr ⟨e.trans m.equiv⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
