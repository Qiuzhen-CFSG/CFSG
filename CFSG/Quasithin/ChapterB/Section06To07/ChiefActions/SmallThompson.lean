module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSource
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.RankOneFieldSize

/-!
# Thompson images and degree-one pairs in the small chief branches

An offender on the natural five-point module contains an odd permutation.
Every nontrivial normal subgroup of S₅ contains A₅, so any normal subgroup
containing that offender is the whole actor. Applied to the original
maximum elementary group, this identifies the literal J(H) chief image.

A marked SL₂(2) pair is solvable, and offender generation makes its ambient
minimal parabolic solvable as well. Thus the original nonsolvable branch
cannot retain a degree-one pair after the field exclusion.

Source: Aschbacher–Smith, B.3.2(4), B.6.9 and3.1.9(5), pp.83,115–116,577–578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
/-- A normal subgroup containing a five-point offender is the whole actor. -/
theorem normal_eq_top_of_five_offender
    (ρ : Representation (ZMod 2) D W)
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5)))
    (N A : Subgroup D) [N.Normal] (hAN : A ≤ N) (hA : IsOffender ρ A) : N = ⊤ := by
  let B := A.map e.groupEquiv.toMonoidHom
  let J := N.map e.groupEquiv.toMonoidHom
  let : J.Normal := Subgroup.Normal.map inferInstance e.groupEquiv.toMonoidHom e.groupEquiv.surjective
  have hB : IsOffender (BinaryPermutation.naturalRepresentation (Fin 5)) B :=
    hA.map_equivariant _ _ e.groupEquiv.toMonoidHom e.groupEquiv.injective
      e.linearEquiv e.intertwines
  have hBJ : B ≤ J := Subgroup.map_mono hAN
  have hn : J ≠ ⊥ := fun hh => hB.1.1 (le_bot_iff.mp (hBJ.trans_eq hh))
  have halt : alternatingGroup (Fin 5) ≤ J := Equiv.Perm.alternatingGroup_le_of_normal
    (by simp) ((Subgroup.nontrivial_iff_ne_bot J).mpr hn)
  have hnalt : ¬ B ≤ alternatingGroup (Fin 5) := by
    obtain ⟨C,hCB,hC⟩ := hB.exists_bestOffender _
    exact fun hh => ((Offenders.Odd.isBestOffender_natural_iff_caseAFamily
      (Or.inl rfl) C).mp hC).not_le_alternating (hCB.trans hh)
  have hjtop : J = ⊤ := by
    have hd : J.index ∣ 2 := by
      simpa only [alternatingGroup.index_eq_two] using Subgroup.index_dvd_of_le halt
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exact False.elim (hnalt (hBJ.trans_eq (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2)))
  apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
  simpa only [Subgroup.map_top_of_surjective e.groupEquiv.toMonoidHom e.groupEquiv.surjective] using hjtop

omit [FiniteDimensional (ZMod 2) W] in
/-- A five-point chief offender from an original maximum elementary group
forces the literal global Thompson image to be the whole chief action. -/
theorem chief_five_thompson_image
    {G : Type*} [Group G] [Finite G]
    (ρ : Representation (ZMod 2) G W) (S : Sylow 2 G)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G))
    (hoff : IsOffender (imageRepresentation ρ) (actionSubgroup ρ A))
    (e : ActionEquiv (imageRepresentation ρ) (BinaryPermutation.naturalRepresentation (Fin 5))) :
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map (actionHom ρ) = ⊤ := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup G)
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  let : J.Normal := inferInstance
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let : (J.map q).Normal := Subgroup.Normal.map inferInstance q hq
  apply normal_eq_top_of_five_offender _ e (J.map q) (actionSubgroup ρ A) _ hoff
  exact Subgroup.map_mono ((le_sSup hA).trans (elementaryAbelianMaxJ_sylow_le_top S))

/-- The actual marked single-five branch of B.6.9, bundled before applying it
inside a dependent original-chief construction. -/
@[expose] def ChiefFiveMarkedSection (ρ : Representation (ZMod 2) D W) : Prop :=
  IsQuasisimple (generalizedFitting (offenderSubgroup ρ)) ∧
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)),
    Nonempty (MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (generalizedFitting (offenderSubgroup ρ))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))

/-- The bundled marking upgrades the literal chief image to the full natural action. -/
theorem minimalParabolic_chief_five_of_marked
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hS : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hmark : ChiefFiveMarkedSection (imageRepresentation ρ)) :
    Nonempty (ActionEquiv (imageRepresentation ρ)
      (BinaryPermutation.naturalRepresentation (Fin 5))) ∧
      offenderSubgroup (imageRepresentation ρ) = ⊤ := by
  obtain ⟨hqs,c,⟨e⟩⟩ := hmark
  exact minimalParabolic_chief_five_action ρ S hS hff hqs c e

/-- A marked degree-one pair forces solvability of the whole minimal parabolic. -/
theorem source_pair_degree_one_solvable
    (ρ : Representation (ZMod 2) D W)
    (T : Sylow 2 D) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 D = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (hd : F.degree = 1)
    (c : d.MarkedProduct (linearNatural F 2)) : Group.IsSolvable D := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let e := (ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
      BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := c.action.groupEquiv.toMonoidHom) c.action.groupEquiv.injective
  have hp : IsPGroup 2 (D ⧸ Y) := isPGroup_quotient_of_sup_eq_top Y T T.isPGroup'
    (offender_generation T hP ρ hff hcore).2
  let : Group.IsNilpotent (D ⧸ Y) := hp.isNilpotent
  exact Group.isSolvable_of_ker_le_range Y.subtype (QuotientGroup.mk' Y)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end CFSG.Quasithin.ChapterB
