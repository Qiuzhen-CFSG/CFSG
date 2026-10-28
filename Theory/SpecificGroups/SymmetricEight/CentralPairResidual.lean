module
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The residual two-core of the even four-pair stabilizer

The action on the four pairs maps the actual even stabilizer onto S₄ with
kernel of order eight. Three even pair flips generate this kernel; explicit
commutators with cubic pair permutations put them in the two-residual.
The residual therefore maps onto A₄ with the same kernel. Lifting the Klein
four two-core through this two-group kernel gives order32.
Only the three commutator identities and the eight kernel normal forms use
finite checking, together with the 24 evident pair-permutation lifts.
Source: Aschbacher–Smith13.5.23, printed pp.924–925.
-/

@[expose] public section
open Subgroup Equiv
open scoped commutatorElement
namespace Theory.SpecificGroups.SymmetricEight.CentralPair
open A6ShadowTwoLocals
private abbrev P := pairStabilizer.subgroupOf (alternatingGroup (Fin 8))
private def pair (i : Fin 8) : Fin 4 := ⟨i.val / 2, by omega⟩
private def representative (i : Fin 4) : Fin 8 := ⟨2*i.val, by omega⟩
private theorem pair_rep (i : Fin 4) : pair (representative i)=i := by
  apply Fin.ext
  simp [pair,representative]
private def pairFun (g : P) (i : Fin 4) : Fin 4 := pair (g.val.val (representative i))
private theorem pair_apply (g : P) (i : Fin 8) : pair (g.val.val i) = pairFun g (pair i) := by
  apply Fin.ext
  exact (g.property i (representative (pair i))).mpr (by simp [pair,representative])
private def pairAction : P →* Equiv.Perm (Fin 4) where
  toFun g := {
    toFun := pairFun g
    invFun := pairFun g⁻¹
    left_inv := by
      intro i
      change pairFun g⁻¹ (pair (g.val.val (representative i))) = i
      rw [←pair_apply]
      change pair (g.val.val.symm (g.val.val (representative i))) = i
      rw [g.val.val.symm_apply_apply,pair_rep]
    right_inv := by
      intro i
      change pairFun g (pair (g.val.val⁻¹ (representative i))) = i
      rw [←pair_apply]
      change pair (g.val.val (g.val.val.symm (representative i))) = i
      rw [g.val.val.apply_symm_apply,pair_rep] }
  map_one' := by apply Equiv.ext; intro i; exact pair_rep i
  map_mul' g h := by
    apply Equiv.ext
    intro i
    exact pair_apply g (h.val.val (representative i))
private def liftPerm (a : Equiv.Perm (Fin 4)) : S8 :=
  (@finProdFinEquiv 4 2).permCongr (Equiv.prodCongr a (Equiv.refl (Fin 2)))
private theorem lift_mem : ∀ a : Equiv.Perm (Fin 4), liftPerm a ∈ pairStabilizer := by decide +kernel
private theorem lift_even : ∀ a : Equiv.Perm (Fin 4), liftPerm a ∈ alternatingGroup (Fin 8) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private def lift (a : Equiv.Perm (Fin 4)) : P := ⟨⟨liftPerm a,lift_even a⟩,lift_mem a⟩
private theorem lift_action : ∀ a : Equiv.Perm (Fin 4), pairAction (lift a)=a := by decide +kernel
private theorem pairAction_surjective : Function.Surjective pairAction := fun a => ⟨lift a,lift_action a⟩
private theorem pair_card : Nat.card P=192 := by
  change Nat.card (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))) = 192
  rw [←CentralPair.centralizer_z,CentralPair.centralizer_z_card]
private theorem kernel_card : Nat.card pairAction.ker=8 := by
  have hc := pairAction.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr pairAction_surjective,card_top,
    Nat.card_perm,Nat.card_fin,pair_card] at hc
  norm_num [Nat.factorial] at hc ⊢
  omega
private def genPerm (i : Fin 3) : S8 :=
  Equiv.swap ⟨2*i.val,by omega⟩ ⟨2*i.val+1,by omega⟩ * Equiv.swap 6 7
private theorem gen_pairs : ∀ i, genPerm i ∈ pairStabilizer := by decide +kernel
private theorem gen_even : ∀ i, genPerm i ∈ alternatingGroup (Fin 8) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
private def gen (i : Fin 3) : P := ⟨⟨genPerm i,gen_even i⟩,gen_pairs i⟩
private def word (b : Fin 3 → Bool) : P :=
  (if b 0 then gen 0 else 1) * (if b 1 then gen 1 else 1) * (if b 2 then gen 2 else 1)
private theorem word_kernel : ∀ b, pairAction (word b)=1 := by decide +kernel
private theorem word_injective : Function.Injective word := by decide +kernel
private def kernelWord (b : Fin 3 → Bool) : pairAction.ker := ⟨word b,word_kernel b⟩
private theorem kernelWord_surjective : Function.Surjective kernelWord := by
  apply (Nat.bijective_iff_injective_and_card kernelWord).mpr ?_ |>.2
  refine ⟨fun x y he => word_injective (congrArg Subtype.val he),?_⟩
  rw [kernel_card,Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card]
  decide
private def next (i : Fin 3) : Fin 3 := ⟨(i.val+1)%3,Nat.mod_lt _ (by decide)⟩
private def cubic (i : Fin 3) : P := lift
  (Equiv.swap i.castSucc (next i).castSucc * Equiv.swap (next i).castSucc 3)
private theorem cubic_cube : ∀ i, cubic i ^ 3 = 1 := by decide +kernel
private theorem gen_commutator : ∀ i, ⁅gen i * gen (next i),cubic i⁆ = gen i := by decide +kernel
private theorem gen_residual (i : Fin 3) : gen i ∈ pResidual 2 P := by
  have hc : cubic i ∈ pResidual 2 P := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one (cubic_cube i)))
  rw [←gen_commutator i]
  exact (pResidual 2 P).mul_mem
    ((inferInstance : (pResidual 2 P).Normal).conj_mem (cubic i) hc (gen i * gen (next i)))
    ((pResidual 2 P).inv_mem hc)
private theorem kernel_le_residual : pairAction.ker ≤ pResidual 2 P := by
  intro x hx
  obtain ⟨b,he⟩ := kernelWord_surjective ⟨x,hx⟩
  have he' : word b=x := congrArg Subtype.val he
  rw [←he']
  unfold word
  apply (pResidual 2 P).mul_mem
  · apply (pResidual 2 P).mul_mem
    · split_ifs <;> first | exact gen_residual _ | exact (pResidual 2 P).one_mem
    · split_ifs <;> first | exact gen_residual _ | exact (pResidual 2 P).one_mem
  · split_ifs <;> first | exact gen_residual _ | exact (pResidual 2 P).one_mem

private theorem residual_image : (pResidual 2 P).map pairAction = alternatingGroup (Fin 4) := by
  rw [map_pResidual_of_surjective 2 pairAction pairAction_surjective,SymmetricFourResidual.residual_eq]
private def residualAction : pResidual 2 P →* alternatingGroup (Fin 4) :=
  (pairAction.comp (pResidual 2 P).subtype).codRestrict _
    (fun x => residual_image ▸ mem_map_of_mem pairAction x.property)
private theorem residualAction_surjective : Function.Surjective residualAction := by
  rintro ⟨y,hy⟩
  rw [←residual_image] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  exact ⟨⟨x,hx⟩,rfl⟩
private theorem residual_kernel : residualAction.ker = pairAction.ker.subgroupOf (pResidual 2 P) := by
  ext x
  change residualAction x=1 ↔ pairAction x.val=1
  exact Subtype.ext_iff
private theorem alternating_core_card : Nat.card (pCore 2 (alternatingGroup (Fin 4)))=4 := by
  rw [pCore_eq_comap_of_normal]
  change Nat.card ((pCore 2 (Equiv.Perm (Fin 4))).subgroupOf (alternatingGroup (Fin 4)))=4
  rw [Nat.card_congr (subgroupOfEquivOfLe (show pCore 2 (Equiv.Perm (Fin 4)) ≤
    alternatingGroup (Fin 4) from by
      rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
      intro x hx
      exact Equiv.Perm.mem_alternatingGroup.mpr
        ((Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff x).mp hx).1)).toEquiv,
    ←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]

/-- The intrinsic two-core of the actual even pair residual has order32. -/
theorem residual_twoCore_card : Nat.card (pCore 2 (pResidual 2
    (pairStabilizer.subgroupOf (alternatingGroup (Fin 8)))))=32 := by
  change Nat.card (pCore 2 (pResidual 2 P))=32
  have hk : Nat.card residualAction.ker=8 := by
    rw [residual_kernel,Nat.card_congr (subgroupOfEquivOfLe kernel_le_residual).toEquiv,kernel_card]
  rw [residualAction.card_pCore_of_ker_isPGroup residualAction_surjective
    (IsPGroup.of_card (n:=3) hk),hk,alternating_core_card]
end Theory.SpecificGroups.SymmetricEight.CentralPair
