module

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ParabolicSections
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer

/-!
# Excluding the linear-Levi rank-two local embeddings

The literal image of a perfect residual normalizing a nonidentity two-group
lies in a geometric parabolic. Its perfectness removes the torus quotient.
The remaining local factor has a two-group kernel and binary SL₂ quotient.
The solvable-kernel section obstruction therefore excludes both marked
rank-one families, even when the residual and component have central covers.

This proves the PSL₃, PSp₄, G₂ and triality local branches in the specialized
4.4.12 argument. The unitary and Ree branches require further analysis.
Source: Aschbacher--Smith 4.4.12, pp.621--622, and F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

variable {A S X : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S]
  [Group X]

private theorem no_quotient_in_local
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* S) (hπ : Function.Surjective π)
    (r : A →* X) [Group.IsSolvable r.ker]
    (D : Subgroup X) (hr : r.range ≤ D)
    (q : D →* SL(2,E)) [Group.IsSolvable q.ker] : False := by
  let j : A →* D := r.codRestrict D (fun x => hr ⟨x,rfl⟩)
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun _ hx => congrArg Subtype.val hx))
    (inclusion_injective _)
  let f := q.comp j
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.comp j).ker
    rw [← MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker j q.ker
  exact no_rankOne_quotient_in_binary_linear_two hS hexp π hπ f

private theorem core_quotient_kernel_solvable
    {D E : Type*} [Group D] [Field E]
    (e : (D ⧸ pCore 2 D) ≃* SL(2,E)) [Finite D] :
    Group.IsSolvable (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))).ker := by
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent
  infer_instance

variable [Group.IsPerfect A]
  (hS : ¬ Group.IsSolvable S)
  (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
  (π : A →* S) (hπ : Function.Surjective π)
include hS hexp π hπ

/-- The degree-three linear parabolic obstruction with the actual residual map. -/
theorem no_linear_three_local
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hn : 2 ≤ n) (hE : Nat.card E = 2 ^ n)
    (P : Subgroup PSL(3,E)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* PSL(3,E)) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set PSL(3,E))) : False := by
  obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le
    E (by omega) hE (normalizer (P : Set PSL(3,E))) ⟨P,hne,hp,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp r
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun x hx => by
      change (MulAut.conj g) (r x) = 1 at hx
      exact (MulAut.conj g).injective (hx.trans (MulAut.conj g).map_one.symm)))
    (inclusion_injective _)
  have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic E point := by
    rw [MonoidHom.range_comp]
    exact (map_mono hr).trans hg
  have hcard : 4 ≤ Nat.card E := by
    rw [hE]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  cases point with
  | false =>
    have hj' : j.range ≤ Matrix.PSL3.LinearThree.lineParabolic E := hj
    have hi := le_map_solvableResidual_of_isPerfect j.range _ hj'
    rw [Matrix.PSL3.LinearThree.PerfectSubgroups.lineParabolic_residual E hcard] at hi
    let e := Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv E
    let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
    let : Group.IsSolvable q.ker := core_quotient_kernel_solvable e
    exact no_quotient_in_local hS hexp π hπ j _ hi q
  | true =>
    have hj' : j.range ≤ Matrix.PSL3.LinearThree.pointParabolic E := hj
    have hi := le_map_solvableResidual_of_isPerfect j.range _ hj'
    rw [Matrix.PSL3.LinearThree.PerfectSubgroups.pointParabolic_residual E hcard] at hi
    let e := Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv E
    let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
    let : Group.IsSolvable q.ker := core_quotient_kernel_solvable e
    exact no_quotient_in_local hS hexp π hπ j _ hi q

/-- The symplectic local obstruction, retaining the full normalizer and map. -/
theorem no_symplectic_four_local
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp E))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* Theory.SpecificGroups.SymplecticFour.Sp E) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.twoLocal_parabolic_cover_of_charTwo
    (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp r
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun x hx => by
      change (MulAut.conj g) (r x) = 1 at hx
      exact (MulAut.conj g).injective (hx.trans (MulAut.conj g).map_one.symm)))
    (inclusion_injective _)
  have hj : j.range ≤ (normalizer (P : Set _)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hr
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hg | hg
  · have hi := (le_map_solvableResidual_of_isPerfect j.range _ (hj.trans hg)).trans
      Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_le
    let q := Theory.SpecificGroups.SymplecticFour.pointQuotient (F := E)
    let : Group.IsSolvable q.ker := by
      have hk : IsPGroup 2 q.ker := by
        change IsPGroup 2 (Theory.SpecificGroups.SymplecticFour.pointQuotient (F := E)).ker
        rw [Theory.SpecificGroups.SymplecticFour.pointQuotient_ker]
        exact IsElementaryAbelian.isPGroup 2 _
      let := hk.isNilpotent
      infer_instance
    exact no_quotient_in_local hS hexp π hπ j _ hi q
  · have hi := (le_map_solvableResidual_of_isPerfect j.range _ (hj.trans hg)).trans
      Theory.SpecificGroups.SymplecticFour.planeParabolic_solvableResidual_le
    let q := Theory.SpecificGroups.SymplecticFour.Plane.quotientMap (F := E)
    let : Group.IsSolvable q.ker := by
      have hk : IsPGroup 2 q.ker := by
        change IsPGroup 2 (Theory.SpecificGroups.SymplecticFour.Plane.quotientMap (F := E)).ker
        rw [Theory.SpecificGroups.SymplecticFour.Plane.quotientMap_ker]
        exact IsElementaryAbelian.isPGroup 2 _
      let := hk.isNilpotent
      infer_instance
    exact no_quotient_in_local hS hexp π hπ j _ hi q

/-- The two root-parabolic branches for the actual G₂ carrier. -/
theorem no_g2_local
    {E : Type*} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (P : Subgroup (Atlas.G2.Model E)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* Atlas.G2.Model E) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  obtain ⟨g,hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic P hne hp
  let j := (MulAut.conj g).toMonoidHom.comp r
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun x hx => by
      change (MulAut.conj g) (r x) = 1 at hx
      exact (MulAut.conj g).injective (hx.trans (MulAut.conj g).map_one.symm)))
    (inclusion_injective _)
  have hj : j.range ≤ (normalizer (P : Set _)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hr
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hg | hg
  · have hi := le_map_solvableResidual_of_isPerfect j.range _ (hj.trans hg)
    rw [Atlas.G2.HigherFieldResiduals.parabolic₁_residual hE] at hi
    let e := (Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL (F := E)).trans
      (Theory.PSL2.sl2QuotientEquiv E).symm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
    let : Group.IsSolvable q.ker := core_quotient_kernel_solvable e
    exact no_quotient_in_local hS hexp π hπ j _ hi q
  · have hi := le_map_solvableResidual_of_isPerfect j.range _ (hj.trans hg)
    rw [Atlas.G2.HigherFieldResiduals.parabolic₂_residual hE] at hi
    let e := (Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL (F := E)).trans
      (Theory.PSL2.sl2QuotientEquiv E).symm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
    let : Group.IsSolvable q.ker := core_quotient_kernel_solvable e
    exact no_quotient_in_local hS hexp π hπ j _ hi q

/-- Both triality parabolics, including the binary endpoint, have the same obstruction. -/
theorem no_triality_local
    (n : ℕ) (hn : 0 < n)
    (P : Subgroup (Triality.Standard.Carrier (Triality.Standard.binaryParameters n hn))) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* Triality.Standard.Carrier (Triality.Standard.binaryParameters n hn)) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let C := Triality.Standard.binaryParameters n hn
  obtain ⟨g,a,hg⟩ := Triality.Standard.TwoLocalCover.normalizer_cover n hn P hne hp
  let j := (MulAut.conj g).toMonoidHom.comp r
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun x hx => by
      change (MulAut.conj g) (r x) = 1 at hx
      exact (MulAut.conj g).injective (hx.trans (MulAut.conj g).map_one.symm)))
    (inclusion_injective _)
  have hj : j.range ≤ Triality.Standard.Parabolics.parabolic C a := by
    rw [MonoidHom.range_comp]
    exact (map_mono hr).trans hg
  let D := Triality.Standard.Parabolics.parabolic C a
  let N := (Triality.Standard.Parabolics.localFactor C a).subgroupOf D
  let jD := j.codRestrict D (fun x => hj ⟨x,rfl⟩)
  let : Group.IsPerfect jD.range := Group.IsPerfect.range jD
  let : IsCyclic (D ⧸ N) := Triality.Standard.Parabolics.parabolic_quotient_isCyclic C rfl a
  let : CommGroup (D ⧸ N) := IsCyclic.commGroup
  have hi : jD.range ≤ N := le_of_isPerfect_of_solvable_quotient _ _
  have hi' : j.range ≤ Triality.Standard.Parabolics.localFactor C a := by
    rintro _ ⟨x,rfl⟩
    exact hi ⟨x,rfl⟩
  cases a with
  | arms =>
    let e := (Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 C rfl).trans
      (Theory.PSL2.sl2QuotientEquiv (Triality.Standard.ExtensionField C)).symm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
    let : Group.IsSolvable q.ker := core_quotient_kernel_solvable e
    exact no_quotient_in_local hS hexp π hπ j _ hi' q
  | central =>
    let e := (Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 C rfl).trans
      (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' _)
    let : Group.IsSolvable q.ker := core_quotient_kernel_solvable e
    exact no_quotient_in_local hS hexp π hπ j _ hi' q

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
