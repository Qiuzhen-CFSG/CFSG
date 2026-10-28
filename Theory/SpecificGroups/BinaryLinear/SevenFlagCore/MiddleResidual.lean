module
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.PerfectDerived
import all Theory.SpecificGroups.BinaryLinear.SevenFlagCore
public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The moving core of the middle binary-five flag residual is nonabelian

The literal 1|3|1 flag has two cross-block roots in its residual two-core.
Cubic actors on the middle block put two noncommuting endpoint roots in
[O₂(O²(P)),O²(P)]. These are explicit matrix witnesses, independent of a
whole-parabolic perfectness or subgroup classification premise.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement Classical
namespace BinaryLinear.SevenFlagCore
open OuterCyclic InvariantNodeActions SmallParabolicLevi CubicPairNormalizers.CoreAbsorption

private def middleLabel : Fin 5 → Fin 5 := ![0,1,1,1,2]
private abbrev middleGroup := triangularGroup middleLabel
private noncomputable def middleResidual : Subgroup (LinearGroup 5) :=
  (pResidual 2 middleGroup).map middleGroup.subtype

private theorem root_matrix (r s : Fin 5) (hrs : r≠s) (i j : Fin 5) :
    matrix (root r s hrs 1) i j = (if i=j then 1 else 0) + (if i=r ∧ j=s then 1 else 0) := by
  rw [matrix_apply]
  by_cases hir : i=r <;> by_cases hjs : j=s <;>
    simp [standardBasis,root_apply,Pi.single_apply,hir,hjs,eq_comm]

private theorem root_in_middle (r s : Fin 5) (hrs : r≠s) (hc : middleLabel r ≤ middleLabel s) :
    root r s hrs 1 ∈ middleGroup := by
  intro i j hji
  rw [root_matrix]
  have hne : i≠j := fun he => by subst i; exact lt_irrefl _ hji
  have hn : ¬(i=r ∧ j=s) := by rintro ⟨rfl,rfl⟩; exact not_lt_of_ge hc hji
  simp [hne,hn]

private theorem root_in_middle_core (r s : Fin 5) (hrs : r≠s) (hc : middleLabel r < middleLabel s) :
    root r s hrs 1 ∈ middleGroup.pCoreIn 2 := by
  let g : middleGroup := ⟨root r s hrs 1,root_in_middle r s hrs hc.le⟩
  refine ⟨g,?_,rfl⟩
  rw [←ker_diagonalAction_eq_twoCore middleLabel (by decide)]
  change diagonalAction middleLabel g = 1
  funext k
  apply LinearEquiv.toLinearMap_injective
  have hb : blockMatrix middleLabel k g.val = 1 := by
    ext i j
    change matrix (root r s hrs 1) i.val j.val = _
    rw [root_matrix]
    have hn : ¬(i.val=r ∧ j.val=s) := by
      rintro ⟨hi,hj⟩
      have he := i.property.trans j.property.symm
      rw [hi,hj] at he
      exact (ne_of_lt hc) he
    simp [hn,Matrix.one_apply,Subtype.ext_iff]
  change Matrix.toLin' (blockMatrix middleLabel k g.val) = LinearMap.id
  rw [hb,Matrix.toLin'_one]

private theorem cross_root_in_residual (r s : Fin 5) (hrs : r≠s)
    (hc : middleLabel r < middleLabel s)
    (hp : (∃ k, k≠r ∧ middleLabel k=middleLabel r) ∨
      (∃ k, k≠s ∧ middleLabel k=middleLabel s)) :
    root r s hrs 1 ∈ middleResidual := by
  apply root_mem_residual (fun i => (middleLabel i).val) middleGroup
    (fun i j hij hijc => root_in_middle i j hij hijc) r s hrs hc
  rcases hp with ⟨k,hkr,hk⟩ | ⟨k,hks,hk⟩
  · exact Or.inl ⟨k,hkr,congrArg Fin.val hk⟩
  · exact Or.inr ⟨k,hks,congrArg Fin.val hk⟩

private theorem cubic_in_residual (r s : Fin 5) (hrs : r≠s) (hc : middleLabel r=middleLabel s) :
    cubic r s hrs ∈ middleResidual := by
  let g : middleGroup := ⟨cubic r s hrs,middleGroup.mul_mem
    (root_in_middle r s hrs hc.le) (root_in_middle s r hrs.symm hc.symm.le)⟩
  refine ⟨g,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show g^3=1 from Subtype.ext (cubic_cube r s hrs)))

private theorem middle_moving_core_nonabelian :
    ⁅⁅middleResidual.pCoreIn 2,middleResidual⁆,⁅middleResidual.pCoreIn 2,middleResidual⁆⁆ ≠ ⊥ := by
  have hR : middleResidual ≤ middleGroup := map_subtype_le _
  have h02 : root (0 : Fin 5) 2 (by decide) 1 ∈ middleResidual.pCoreIn 2 :=
    inf_pCoreIn_le_of_le 2 hR ⟨cross_root_in_residual 0 2 (by decide) (by decide)
      (Or.inr ⟨1,by decide,by decide⟩),root_in_middle_core 0 2 (by decide) (by decide)⟩
  have h24 : root (2 : Fin 5) 4 (by decide) 1 ∈ middleResidual.pCoreIn 2 :=
    inf_pCoreIn_le_of_le 2 hR ⟨cross_root_in_residual 2 4 (by decide) (by decide)
      (Or.inl ⟨1,by decide,by decide⟩),root_in_middle_core 2 4 (by decide) (by decide)⟩
  have h01 : root (0 : Fin 5) 1 (by decide) 1 ∈ ⁅middleResidual.pCoreIn 2,middleResidual⁆ := by
    rw [←root_column_commutator 0 2 1 (by decide) (by decide) (by decide)]
    exact commutator_mem_commutator h02 (cubic_in_residual 2 1 (by decide) (by decide))
  have h14 : root (1 : Fin 5) 4 (by decide) 1 ∈ ⁅middleResidual.pCoreIn 2,middleResidual⁆ := by
    rw [←root_row_commutator 1 2 4 (by decide) (by decide) (by decide),commutator_comm]
    exact commutator_mem_commutator (cubic_in_residual 1 2 (by decide) (by decide)) h24
  intro hz
  have hh := commutator_mem_commutator h01 h14
  rw [hz,mem_bot] at hh
  have he := congrArg (fun g : LinearGroup 5 => g (Pi.single 4 1) 0) hh
  norm_num [commutatorElement_def,mul_inv_rev,root_inv,LinearEquiv.mul_apply,root_apply,
    Pi.single_apply,show (0 : Fin 5) ≠ 4 from by decide,show (1 : Fin 5) ≠ 4 from by decide,
    show (4 : Fin 5) ≠ 1 from by decide,show (4 : Fin 5) ≠ 0 from by decide] at he
  exact (by decide : (3 : ZMod 2) ≠ 0) he

private theorem middle_cut_label : cutLabel ({0,3} : Set (Fin 4)) = middleLabel := by
  ext i
  fin_cases i <;> simp [cutLabel,middleLabel,
    show (Finset.univ : Finset (Fin 4))={0,1,2,3} from by decide,
    Finset.filter_insert,Finset.filter_singleton]

/-- The actual residual of a 1|3|1 flag has a nonabelian moving two-core,
witnessed by two endpoint roots recovered from middle-block cubics. -/
theorem middle_flag_residual_moving_core_nonabelian (b : Basis 4) :
    let P := cutStabilizer b ({0,3} : Set (Fin 4))
    let R := (pResidual 2 P).map P.subtype
    ⁅⁅R.pCoreIn 2,R⁆,⁅R.pCoreIn 2,R⁆⁆ ≠ ⊥ := by
  let P := cutStabilizer b ({0,3} : Set (Fin 4))
  let R₀ := pResidual 2 P
  let R := R₀.map P.subtype
  let e : P ≃* middleGroup := (flagCoordinates b {0,3}).trans
    (MulEquiv.subgroupCongr (congrArg triangularGroup middle_cut_label))
  let f : P →* LinearGroup 5 := middleGroup.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := middleGroup.subtype_injective.comp e.injective
  have he : R₀.map f = middleResidual := by
    rw [show R₀.map f = (R₀.map e.toMonoidHom).map middleGroup.subtype from (map_map _ _ _).symm]
    rw [map_pResidual]
    rfl
  change ⁅⁅R.pCoreIn 2,R⁆,⁅R.pCoreIn 2,R⁆⁆ ≠ ⊥
  intro hz
  have hz₀ : ⁅⁅R₀.pCoreIn 2,R₀⁆,⁅R₀.pCoreIn 2,R₀⁆⁆ = ⊥ := by
    apply map_injective P.subtype_injective
    simpa only [map_commutator,map_pCoreIn_of_injective 2 R₀ _ P.subtype_injective,Subgroup.map_bot] using hz
  apply middle_moving_core_nonabelian
  have hm := congrArg (Subgroup.map f) hz₀
  simpa only [map_commutator,map_pCoreIn_of_injective 2 R₀ f hf,he,Subgroup.map_bot] using hm

end BinaryLinear.SevenFlagCore
