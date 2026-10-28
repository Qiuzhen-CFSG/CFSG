module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Model
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.SpecificGroups.AlternatingFiveCore

/-!
# The corrected residual in the orthogonal component sieve

The selected map K₀U → A₅ has two-group kernel U. Its solvable residual is
therefore a genuine C-component, and its quotient by its own two-core is A₅
through the original map. Adjoining D preserves the embedded residual:
D normalizes K₀U and contributes a solvable quotient. This constructs the
candidate smaller component from the actual selected moved-module map.

Placement in the original Sylow overgroup and identification of the core's
image with UD/D remain separate deductions. The diagonal K₀ itself does
not satisfy the local-component contract, as proved in Quotients.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, and A.3.3(4).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

private instance : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)
private instance : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem residual_component_of_five_quotient
    {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : (solvableResidual A).IsCComponent := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  apply residual_isCComponent_of_surjective f hf
  rw [solvableResidual_eq_top]
  let e : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≃* alternatingGroup (Fin 5) := topEquiv
  let : IsSimpleGroup (⊤ : Subgroup (alternatingGroup (Fin 5))) := e.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact isCComponent_of_isSimpleGroup_of_isPerfect .top

/-- A two-group kernel of an A₅ epimorphism is the full two-core. -/
theorem core_eq_five_kernel
    {A : Type*} [Group A] [Finite A]
    (f : A →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : pCore 2 A = f.ker := by
  have he := (f.comap_pCore_of_ker_isPGroup hf hk).symm
  rw [alternatingGroup.five_twoCore_eq_bot] at he
  exact he

/-- The selected quotient presentation constructs a C-component of K₀U. -/
theorem moved_residual_isCComponent
    {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
    (m : MovedCoreModel U K i hKU) (hU : IsPGroup 2 U) :
    (solvableResidual (K ⊔ U : Subgroup G)).IsCComponent := by
  apply residual_component_of_five_quotient m.π m.surjective
  rw [m.kernel]
  exact hU.comap_subtype

/-- The intrinsic two-core of K₀U is exactly the selected kernel U. -/
theorem moved_actor_core
    {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
    (m : MovedCoreModel U K i hKU) (hU : IsPGroup 2 U) :
    pCore 2 (K ⊔ U : Subgroup G) = U.subgroupOf (K ⊔ U) := by
  rw [← m.kernel]
  exact core_eq_five_kernel m.π m.surjective (by rw [m.kernel]; exact hU.comap_subtype)

/-- Restricting the original selected map to the residual still covers A₅. -/
theorem moved_residual_surjective
    {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
    (m : MovedCoreModel U K i hKU) :
    Function.Surjective (m.π.comp (solvableResidual (K ⊔ U : Subgroup G)).subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, range_subtype,
    map_solvableResidual_eq m.π m.surjective, solvableResidual_eq_top]

/-- The residual's actor is the original A₅ quotient, with its own two-core
as exact kernel. No component or actor identification is assumed. -/
@[expose] noncomputable def movedResidualActorEquiv
    {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
    (m : MovedCoreModel U K i hKU) (hU : IsPGroup 2 U) :
    (solvableResidual (K ⊔ U : Subgroup G) ⧸
      pCore 2 (solvableResidual (K ⊔ U : Subgroup G))) ≃* alternatingGroup (Fin 5) := by
  let R := solvableResidual (K ⊔ U : Subgroup G)
  let f := m.π.comp R.subtype
  have hk : IsPGroup 2 f.ker := by
    rw [← MonoidHom.comap_ker, m.kernel]
    exact hU.comap_subtype.comap_subtype
  exact QuotientGroup.liftEquiv (pCore 2 R) (moved_residual_surjective m)
    (core_eq_five_kernel f (moved_residual_surjective m) hk)

/-- The actor equivalence preserves the literal selected map on representatives. -/
@[simp] theorem movedResidualActorEquiv_mk
    {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
    (m : MovedCoreModel U K i hKU) (hU : IsPGroup 2 U)
    (r : solvableResidual (K ⊔ U : Subgroup G)) :
    movedResidualActorEquiv m hU (QuotientGroup.mk' _ r) = m.π r.val := rfl

/-- An invariant two-group supplement does not change the embedded residual. -/
theorem residual_join_twoGroup_eq (A D : Subgroup G)
    (hn : D ≤ normalizer (A : Set G)) (hD : IsPGroup 2 D) :
    (solvableResidual (A ⊔ D : Subgroup G)).map (A ⊔ D).subtype =
      (solvableResidual A).map A.subtype := by
  let J := A ⊔ D
  let A' := A.subgroupOf J
  let : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hsup : A' ⊔ D.subgroupOf J = ⊤ := (codisjoint_subgroupOf_sup A D).eq_top
  let : Group.IsNilpotent (J ⧸ A') :=
    (isPGroup_quotient_of_sup_eq_top A' (D.subgroupOf J) hD.comap_subtype hsup).isNilpotent
  have he := map_solvableResidual_eq_of_solvable_quotient A'
  have hmap := congrArg (Subgroup.map J.subtype) he
  rw [map_map] at hmap
  have hm := map_solvableResidual_eq (subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ J from le_sup_left)).surjective
  rw [← hm, map_map]
  exact hmap.symm

/-- The residual remains a C-component after adjoining a normalizing two-group. -/
theorem residual_join_twoGroup_isCComponent (A D : Subgroup G)
    (hn : D ≤ normalizer (A : Set G)) (hD : IsPGroup 2 D)
    (hc : (solvableResidual A).IsCComponent) :
    (solvableResidual (A ⊔ D : Subgroup G)).IsCComponent := by
  let J := A ⊔ D
  let A' := A.subgroupOf J
  let e : A' ≃* A := subgroupOfEquivOfLe le_sup_left
  have hc' := hc.map_equiv e.symm
  rw [map_solvableResidual_eq e.symm.toMonoidHom e.symm.surjective] at hc'
  have hn' : A'.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hmap := hc'.map_subtype hn'.isSubnormal
  have he : (solvableResidual A').map A'.subtype = solvableResidual J := by
    let := hn'
    let : Group.IsNilpotent (J ⧸ A') :=
      (isPGroup_quotient_of_sup_eq_top A' (D.subgroupOf J) hD.comap_subtype
        (codisjoint_subgroupOf_sup A D).eq_top).isNilpotent
    exact map_solvableResidual_eq_of_solvable_quotient A'
  exact he ▸ hmap

omit [Finite G] in
/-- The lift normalizes K₀U: its commutator and central line lie in U,
while its selected involution centralizes K₀ and normalizes U. -/
theorem lift_normalizes_actor (K U : Subgroup G) (z i : G)
    (hZ : zpowers z ≤ U) (hiU : i ∈ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G)) :
    centralizerLift U z i ≤ normalizer (K ⊔ U : Subgroup G) := by
  have hKU : U ≤ K ⊔ U := le_sup_right
  apply sup_le
  · apply sup_le
    · exact (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)).trans
        (hKU.trans (K ⊔ U).le_normalizer)
    · apply zpowers_le.mpr
      apply (K.normalizer_inf_normalizer_le_normalizer_sup U)
      refine ⟨?_, hiU⟩
      apply _root_.centralizer_le_normalizer
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hKi hk)
  · exact hZ.trans (hKU.trans (K ⊔ U).le_normalizer)

/-- The actual selected moved-module presentation constructs the corrected
C-component inside K₀UD; no local-component membership is assumed. -/
theorem corrected_residual_isCComponent
    {U : Subgroup G} {z i : G}
    {hKU : diagonalResidual (centralizer ({z} : Set G)) i ≤ normalizer (U : Set G)}
    (m : MovedCoreModel U (diagonalResidual (centralizer ({z} : Set G)) i) i hKU)
    (hU : IsPGroup 2 U) (hZ : zpowers z ≤ U)
    (hiU : i ∈ normalizer (U : Set G))
    (hD : IsPGroup 2 (centralizerLift U z i)) :
    (solvableResidual (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔
      centralizerLift U z i : Subgroup G)).IsCComponent := by
  apply residual_join_twoGroup_isCComponent _ _
    (lift_normalizes_actor _ U z i hZ hiU ?_) hD (moved_residual_isCComponent m hU)
  exact (map_subtype_le _).trans inf_le_right

/-- The correction is compatible with the same embedded residual before
adjoining D, rather than an asserted identification with the diagonal K₀. -/
theorem corrected_residual_eq
    (U : Subgroup G) (z i : G) (hZ : zpowers z ≤ U)
    (hiU : i ∈ normalizer (U : Set G))
    (hD : IsPGroup 2 (centralizerLift U z i)) :
    (solvableResidual (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔
      centralizerLift U z i : Subgroup G)).map
        (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U ⊔ centralizerLift U z i).subtype =
    (solvableResidual (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U : Subgroup G)).map
      (diagonalResidual (centralizer ({z} : Set G)) i ⊔ U).subtype := by
  apply residual_join_twoGroup_eq _ _ (lift_normalizes_actor _ U z i hZ hiU ?_) hD
  exact (map_subtype_le _).trans inf_le_right

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
