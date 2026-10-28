module

public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.ExtendScalars
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Solvable normalizers of abelian subgroups with abelian centralizer

In a faithful representation of degree at most four, the automizer of a
cross-characteristic abelian subgroup embeds in a solvable symmetric group.
If its ambient centralizer is also abelian, the normalizer is an extension
of solvable groups. Scalar extension gives the same criterion over any field.

This isolates the weight-space step used in Aschbacher–Smith,
Lemma A.3.21(c), printed pp. 55–56. The hypotheses about the centralizer
are explicit; applications must establish them from their weight dimensions.
-/

public section

namespace Representation

open scoped IsMulCommutative

variable {E G V : Type*} [Field E] [IsAlgClosed E] [Group G]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- If every occurring weight is a line, the ambient centralizer is abelian.
Centralizing operators preserve each weight and commute on a line; the
weight spaces span the whole faithful representation. -/
theorem centralizer_isMulCommutative_of_characterWeight_finrank_one
    (rho : Representation E G V) (A : Subgroup G) [IsMulCommutative A]
    (hrho : Function.Injective rho) (horder : (Nat.card A : E) ≠ 0)
    (hlines : ∀ chi : CharacterWeight (rho.comp A.subtype),
      Module.finrank E (characterWeightSpace (rho.comp A.subtype) chi.val) = 1) :
    IsMulCommutative (Subgroup.centralizer (A : Set G)) := by
  have hpres (g : G) (hg : g ∈ Subgroup.centralizer (A : Set G))
      (chi : CharacterWeight (rho.comp A.subtype)) (v : V)
      (hv : v ∈ characterWeightSpace (rho.comp A.subtype) chi.val) :
      rho g v ∈ characterWeightSpace (rho.comp A.subtype) chi.val := by
    simp only [characterWeightSpace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] at hv ⊢
    intro a
    change rho (a : G) (rho g v) = (chi.val a : E) • rho g v
    have hc : (a : G) * g = g * a :=
      (Subgroup.mem_centralizer_iff.mp hg) a a.property
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    change rho g ((rho.comp A.subtype) a v) = _
    rw [hv a, map_smul]
  refine .of_setLike_mul_comm ?_
  intro g hg h hh
  apply hrho
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← iSup_characterWeightSpace_eq_top (rho.comp A.subtype) horder]
  refine iSup_le fun chi v hv => ?_
  change rho (g * h) v = rho (h * g) v
  by_cases hv0 : v = 0
  · simp [hv0]
  let w : characterWeightSpace (rho.comp A.subtype) chi.val := ⟨v, hv⟩
  have hw : w ≠ 0 := fun he => hv0 (congrArg Subtype.val he)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (hlines chi) hw
    (⟨rho g v, hpres g hg chi v hv⟩ :
      characterWeightSpace (rho.comp A.subtype) chi.val)
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one (hlines chi) hw
    (⟨rho h v, hpres h hh chi v hv⟩ :
      characterWeightSpace (rho.comp A.subtype) chi.val)
  have ha' : a • v = rho g v := congrArg Subtype.val ha
  have hb' : b • v = rho h v := congrArg Subtype.val hb
  simp only [map_mul, Module.End.mul_apply]
  rw [← hb', map_smul, ← ha', map_smul, ← hb', smul_smul, smul_smul, mul_comm]

/-- An abelian centralizer and a faithful action of degree at most four make
the normalizer of a cross-characteristic abelian subgroup solvable. -/
theorem normalizer_isSolvable_of_abelian_centralizer
    (rho : Representation E G V) (A : Subgroup G)
    [IsMulCommutative A] [IsMulCommutative (Subgroup.centralizer (A : Set G))]
    (hrho : Function.Injective rho) (horder : (Nat.card A : E) ≠ 0)
    (hdim : Module.finrank E V ≤ 4) :
    Group.IsSolvable (Subgroup.normalizer (A : Set G)) := by
  obtain ⟨j, hj⟩ := automizer_embeds_perm_of_abelian rho A hrho horder 4 hdim
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable A.normalizerMonoidHom.range :=
    Group.isSolvable_of_isSolvable_injective hj
  have hker : A.normalizerMonoidHom.rangeRestrict.ker =
      (Subgroup.centralizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (A : Set G)) := by
    rw [MonoidHom.ker_rangeRestrict, A.normalizerMonoidHom_ker]
  let : Group.IsSolvable A.normalizerMonoidHom.rangeRestrict.ker := by
    rw [hker]
    let : IsMulCommutative ((Subgroup.centralizer (A : Set G)).subgroupOf
        (Subgroup.normalizer (A : Set G))) :=
      Subgroup.subgroupOf_isMulCommutative _ _
    infer_instance
  exact Group.isSolvable_of_ker_le_range
    A.normalizerMonoidHom.rangeRestrict.ker.subtype
    A.normalizerMonoidHom.rangeRestrict (by rw [Subgroup.range_subtype])

/-- The normalizer criterion over the original matrix field, with no splitting
field assumption. -/
theorem generalLinear_normalizer_isSolvable_of_abelian_centralizer
    {F : Type*} [Field F] (n : ℕ) (hn : n ≤ 4) (A : Subgroup (GL (Fin n) F))
    [IsMulCommutative A]
    [IsMulCommutative (Subgroup.centralizer (A : Set (GL (Fin n) F)))]
    (horder : (Nat.card A : F) ≠ 0) :
    Group.IsSolvable (Subgroup.normalizer (A : Set (GL (Fin n) F))) := by
  let E := AlgebraicClosure F
  let rho := (generalLinearNatural (F := F) n).extendScalars E
  have hrho : Function.Injective rho :=
    (extendScalars_faithful_iff E _).mp (generalLinearNatural_injective n)
  have horder' : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  apply normalizer_isSolvable_of_abelian_centralizer rho A hrho horder'
  simpa only [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin] using hn

end Representation
