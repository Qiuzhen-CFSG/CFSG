module

public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open InvolutionTypes InvolutionCentralizers
open scoped IsMulCommutative
/-!
# No A₆ subgroup in a symplectic involution centralizer

An inner involution centralizer lies in a genuine point or plane parabolic.
Perfectness places any A₆ subgroup in the determinant kernel of that parabolic.
Its projection to the SL₂ Levi factor is injective, since its kernel is solvable
and A₆ is simple and nonsolvable. This is impossible: the defining-characteristic
Sylow subgroup of SL₂ is abelian, whereas A₆ has noncommuting involutions in a
two-subgroup. The argument includes the binary field and uses no automorphism
classification or field-size comparison.

Source: Aschbacher–Smith, 16.1.4(1)–(2), printed p.1171; E.6.23, printed p.254.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
private abbrev A6 := alternatingGroup (Fin 6)
private instance : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
private instance : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem injective_through_kernel {G H : Type*} [Group G] [Group H]
    (p : G →* H) [Group.IsSolvable p.ker] (f : A6 →* G) (hf : Function.Injective f) :
    Function.Injective (p.comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (p.comp f).ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hh (x : A6) : f x ∈ p.ker := by
      have hx : x ∈ (p.comp f).ker := by rw [h]; trivial
      exact hx
    let j := f.codRestrict p.ker hh
    have hj : Function.Injective j := by
      intro x y hxy
      exact hf (congrArg Subtype.val hxy)
    exact (Group.IsPerfect.not_isSolvable A6 (Group.isSolvable_of_isSolvable_injective hj)).elim

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem not_injective_SL2 (f : A6 →* Matrix.SpecialLinearGroup (Fin 2) F) :
    ¬ Function.Injective f := by
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P
  apply alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute P
  intro a b _ _
  exact e.symm.injective (by simp only [map_mul]; exact mul_comm _ _)

private theorem not_injective_pointLocal (f : A6 →* pointLocal (F := F)) :
    ¬ Function.Injective f := by
  intro hf
  let : IsElementaryAbelian 2 (pointQuotient (F := F)).ker :=
    pointRadical_elementaryAbelian
  exact not_injective_SL2 (pointQuotient.comp f) (injective_through_kernel pointQuotient f hf)

private theorem not_injective_planeLocal (f : A6 →* planeLocal (F := F)) :
    ¬ Function.Injective f := by
  intro hf
  let : IsElementaryAbelian 2 (Plane.quotientMap (F := F)).ker :=
    Plane.radical_elementaryAbelian
  exact not_injective_SL2 (Plane.quotientMap.comp f)
    (injective_through_kernel Plane.quotientMap f hf)

private noncomputable def lift_to_local (W : Submodule F (Vector F)) (f : A6 →* stabilizer W) :
    A6 →* determinantKernel W where
  toFun x := ⟨(f x).val, ⟨f x,
    Abelianization.commutator_subset_ker ((determinantCharacter W).comp f)
      Group.IsPerfect.mem_commutator, rfl⟩⟩
  map_one' := Subtype.ext (congrArg (fun z : stabilizer W => (z : Sp F)) f.map_one)
  map_mul' x y := Subtype.ext (congrArg (fun z : stabilizer W => (z : Sp F)) (f.map_mul x y))

omit [Finite F] [CharP F 2] in
private theorem lift_to_local_injective (W : Submodule F (Vector F))
    (f : A6 →* stabilizer W) (hf : Function.Injective f) :
    Function.Injective (lift_to_local W f) := by
  intro x y h
  exact hf (Subtype.ext (congrArg (fun z : determinantKernel W => (z : Sp F)) h))

/-- The full parabolics contain no alternating-six subgroup. -/
private theorem not_injective_parabolic (P : Subgroup (Sp F)) (hP : IsParabolic P)
    (f : alternatingGroup (Fin 6) →* P) : ¬ Function.Injective f := by
  intro hf
  obtain ⟨g, hp | hp⟩ := hP
  · let e : P ≃* pointParabolic (F := F) :=
      (MulEquiv.subgroupCongr hp).trans ((MulAut.conj g).subgroupMap pointParabolic).symm
    let j := e.toMonoidHom.comp f
    exact not_injective_pointLocal (lift_to_local (point F) j)
      (lift_to_local_injective _ j (e.injective.comp hf))
  · let e : P ≃* planeParabolic (F := F) :=
      (MulEquiv.subgroupCongr hp).trans ((MulAut.conj g).subgroupMap planeParabolic).symm
    let j := e.toMonoidHom.comp f
    exact not_injective_planeLocal (lift_to_local (plane F) j)
      (lift_to_local_injective _ j (e.injective.comp hf))

/-- The full fixed group of an inner involution contains no A₆ subgroup. -/
theorem not_six_inner (g : Sp F) (hg : orderOf g = 2)
    (S : Subgroup (Sp F)) (hS : S ≤ (MulAut.conj g).fixedSubgroup) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨P, hP, _, _, hc⟩ := involution_centralizer_parabolic g hg
  rw [MulAut.fixedSubgroup_conj] at hS
  rintro ⟨e⟩
  exact not_injective_parabolic P hP ((inclusion (hS.trans hc)).comp e.symm.toMonoidHom)
    ((inclusion_injective (hS.trans hc)).comp e.symm.injective)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
