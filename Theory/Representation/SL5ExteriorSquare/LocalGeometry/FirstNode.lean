module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Assembly
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.FlagSylow
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The first-node parabolic in the binary five-space

The subgroup fixing every standard flag space except the first has a
surjective small diagonal block with two-group kernel. It supplements the
point-parabolic residual, lies in the three- and four-flag residual joins,
and is not contained in the point-residual flag join. Its two-residual acts
trivially on the large block. Its two-residual is also its prime-to-three
residual, and its intersection with the point-residual flag group is the
original flag group. All maps use the original matrix coordinates.

These calculations supply the literal P and Y = O²(P) used by the exterior
local component and normalizer arguments. Source: Aschbacher--Smith,
notation before 12.5.3 and proof of 12.5.4, printed pp.817--819.
-/

@[expose] public noncomputable section

open Subgroup
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

noncomputable def firstNodeParabolic : Subgroup Group :=
  ⨅ (k : Fin 5) (_ : k.val ≠ 1), parabolic k.val

theorem firstNode_le_parabolic (k : Fin 5) (hk : k.val ≠ 1) :
    firstNodeParabolic ≤ parabolic k.val :=
  (iInf_le _ k).trans (iInf_le _ hk)

theorem flag_le_firstNode : flagGroup ≤ firstNodeParabolic := by
  apply le_iInf
  intro k
  apply le_iInf
  intro _
  exact flagGroup_le_parabolic k.val k.isLt

private theorem transvection_mem_parabolic (k : ℕ) (i j : Fin 5) (hij : i ≠ j)
    (c : ZMod 2) (hp : j.val < k → i.val < k) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ parabolic k := by
  rw [parabolic_eq_closure_transvections]
  exact subset_closure ⟨i,j,hij,c,hp,rfl⟩

/-- The first node supplies exactly the missing small block of the point parabolic. -/
theorem firstNode_sup_pointResidual :
    firstNodeParabolic ⊔ parabolicResidual 2 = parabolic 2 := by
  apply le_antisymm (sup_le (firstNode_le_parabolic 2 (by decide)) (parabolicResidual_le 2))
  rw [parabolic_eq_closure_transvections]
  apply (closure_le _).mpr
  rintro _ ⟨i,j,hij,c,hp,rfl⟩
  by_cases hj : j.val < 2
  · apply (le_sup_left : firstNodeParabolic ≤ firstNodeParabolic ⊔ parabolicResidual 2)
    apply mem_iInf.mpr
    intro k
    apply mem_iInf.mpr
    intro hk
    exact transvection_mem_parabolic _ _ _ hij c (by
      have hi := hp hj
      omega)
  · apply (le_sup_right : parabolicResidual 2 ≤ firstNodeParabolic ⊔ parabolicResidual 2)
    rw [parabolicResidual_two]
    have ht := transvection_mem_parabolic 2 i j hij c hp
    refine ⟨⟨_,ht⟩, ?_, rfl⟩
    change parabolicTwoSmallBlock ⟨_,ht⟩ = 1
    apply Subtype.ext
    ext a b
    rw [parabolicTwoSmallBlock_entry]
    have hjb : j.val ≠ b.val := by have := b.isLt; omega
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply,
      Fin.ext_iff, hjb]

private theorem binary_upper_mem_unipotent {n : ℕ} (a : SL(n, ZMod 2))
    (ha : a.val.IsUpperTriangular) :
    a ∈ Theory.SpecificGroups.LinearSylowNormalizers.unipotent n (ZMod 2) := by
  open Theory.SpecificGroups.LinearSylowNormalizers in
  apply (mem_unipotent n (ZMod 2) a).mpr
  refine ⟨(mem_borel n (ZMod 2) a).mpr ha, fun i => ?_⟩
  have hd := a.property
  rw [Matrix.det_of_isUpperTriangular ha] at hd
  have hp : (∏ j, a.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hi

/-- The first node is already in the three-space residual's Sylow join. -/
theorem firstNode_le_threeResidualFlag : firstNodeParabolic ≤ parabolicResidualFlag 3 := by
  intro g hg
  have hg3 := firstNode_le_parabolic 3 (by decide) hg
  change g ∈ parabolicResidual 3 ⊔ flagGroup
  rw [parabolicResidual_three]
  apply (MiddleCore.mem_threeFlag ⟨g,hg3⟩).mpr
  apply binary_upper_mem_unipotent
  intro i j hji
  rw [parabolicThreeSmallBlock_entry]
  exact (mem_parabolic_iff_lowerLeft_zero 4 g).mp
    (firstNode_le_parabolic 4 (by decide) hg) _ _ (by fin_cases i <;> fin_cases j <;> simp_all)
      (by fin_cases i <;> fin_cases j <;> simp_all)

/-- The first node lies in the six-space residual's Sylow join. -/
theorem firstNode_le_fourResidualFlag : firstNodeParabolic ≤ parabolicResidualFlag 4 := by
  rw [parabolicResidualFlag_four]
  exact firstNode_le_parabolic 4 (by decide)


/-- Inside the point parabolic, the first node fixes the flag of the large block. -/
theorem mem_firstNode_iff_large_upper (g : parabolic 2) :
    g.val ∈ firstNodeParabolic ↔
      (parabolicLeviHom 2 (by decide) g).2.val.IsUpperTriangular := by
  constructor
  · intro hg i j hji
    change j.val < i.val at hji
    have hi : i.val < 3 := i.isLt
    have hj : j.val < 3 := j.isLt
    rw [parabolicLeviHom_snd_entry]
    exact (mem_parabolic_iff_lowerLeft_zero (2+i.val) g.val).mp
      (firstNode_le_parabolic ⟨2+i.val, by omega⟩ (by dsimp; omega) hg) _ _
        (by dsimp; omega) (by dsimp; omega)
  · intro hu
    apply mem_iInf.mpr
    intro k
    apply mem_iInf.mpr
    intro hk
    apply (mem_parabolic_iff_lowerLeft_zero k.val g.val).mpr
    intro i j hi hj
    by_cases hj2 : j.val < 2
    · exact (mem_parabolic_iff_lowerLeft_zero 2 g.val).mp g.property i j (by omega) hj2
    · have hi2 : 2 ≤ i.val := by omega
      have he := hu (show (⟨j.val-2, by omega⟩ : Fin 3) < ⟨i.val-2, by omega⟩ by
        change j.val-2 < i.val-2; omega)
      rw [parabolicLeviHom_snd_entry] at he
      simpa only [Nat.add_sub_of_le hi2, Nat.add_sub_of_le (by omega : 2 ≤ j.val)] using he

/-- The literal two-dimensional block on the first-node subgroup. -/
noncomputable def firstNodeSmallHom : firstNodeParabolic →* SL(2, ZMod 2) :=
  parabolicTwoSmallBlock.comp (inclusion (firstNode_le_parabolic 2 (by decide)))

/-- Every small block occurs with identity large block. -/
theorem firstNodeSmallHom_surjective : Function.Surjective firstNodeSmallHom := by
  intro a
  obtain ⟨g,hg⟩ := parabolicLeviHom_surjective 2 (by decide) (a,1)
  have hm : g.val ∈ firstNodeParabolic := (mem_firstNode_iff_large_upper g).mpr (by
    rw [hg]; exact Matrix.blockTriangular_one)
  exact ⟨⟨g.val,hm⟩, congrArg Prod.fst hg⟩

/-- The large block of the first-node subgroup is a two-group. -/
theorem firstNode_large_block_unipotent (g : firstNodeParabolic) :
    (parabolicLeviHom 2 (by decide)
      (inclusion (firstNode_le_parabolic 2 (by decide)) g)).2 ∈
      Theory.SpecificGroups.LinearSylowNormalizers.unipotent 3 (ZMod 2) :=
  binary_upper_mem_unipotent _ ((mem_firstNode_iff_large_upper _).mp g.property)

/-- The only odd action in the first node comes from its small SL₂ block. -/
theorem firstNodeSmallHom_ker_isPGroup : IsPGroup 2 firstNodeSmallHom.ker := by
  let U := Theory.SpecificGroups.LinearSylowNormalizers.unipotent 3 (ZMod 2)
  have hU : IsPGroup 2 U :=
    Theory.SpecificGroups.LinearSylowNormalizers.unipotent_isPGroup 3 (ZMod 2) (by decide)
  have hp : IsPGroup 2 ((⊥ : Subgroup SL(2, ZMod 2)).prod U) := by
    intro x
    obtain ⟨n,hn⟩ := hU ⟨x.val.2,x.property.2⟩
    refine ⟨n, Subtype.ext (Prod.ext ?_ (congrArg Subtype.val hn))⟩
    change x.val.1 ^ 2^n = 1
    rw [show x.val.1 = 1 from x.property.1, one_pow]
  have hker : IsPGroup 2 (parabolicLeviHom 2 (by decide)).ker := by
    rw [parabolicLeviHom_ker]; exact pCore_isPGroup
  have hpre := (hp.comap_of_ker_isPGroup _ hker).comap_of_injective
    (inclusion (firstNode_le_parabolic 2 (by decide))) (inclusion_injective _)
  apply hpre.to_le
  intro g hg
  exact ⟨hg, firstNode_large_block_unipotent g⟩

/-- The first-node quotient is the literal small diagonal block. -/
theorem firstNodeSmallHom_ker : firstNodeSmallHom.ker = pCore 2 firstNodeParabolic := by
  have hcore : pCore 2 SL(2, ZMod 2) = ⊥ := by
    apply Subgroup.map_injective (f := (BinaryLinear.OuterCyclic.slEquivLinear 2).toMonoidHom)
      (BinaryLinear.OuterCyclic.slEquivLinear 2).injective
    rw [pCore_map_iso, Subgroup.map_bot]
    exact BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot
  have he := firstNodeSmallHom.comap_pCore_of_ker_isPGroup
    firstNodeSmallHom_surjective firstNodeSmallHom_ker_isPGroup
  rwa [hcore] at he

noncomputable def firstNodeQuotientEquiv :
    (firstNodeParabolic ⧸ pCore 2 firstNodeParabolic) ≃* SL(2, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq firstNodeSmallHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective firstNodeSmallHom firstNodeSmallHom_surjective)

theorem firstNodeQuotientEquiv_mk (g : firstNodeParabolic) :
    firstNodeQuotientEquiv (QuotientGroup.mk' _ g) = firstNodeSmallHom g := rfl

/-- The first node supplies a direction missing from the point-residual flag group. -/
theorem firstNode_not_le_pointResidualFlag : ¬ firstNodeParabolic ≤ parabolicResidualFlag 2 := by
  intro hh
  let g : Group := Matrix.SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) 1
  have hg : g ∈ firstNodeParabolic := by
    apply mem_iInf.mpr
    intro k
    apply mem_iInf.mpr
    intro hk
    exact transvection_mem_parabolic _ _ _ (by decide) _ (by dsimp; omega)
  have hg2 := firstNode_le_parabolic 2 (by decide) hg
  have hs := (MiddleCore.mem_twoFlag ⟨g,hg2⟩).mp (by
    simpa only [parabolicResidualFlag, parabolicResidual_two, MiddleCore.twoFlag] using hh hg)
  have hz := (MiddleCore.mem_smallUnipotent _).mp hs
  have he := hz.2.1
  rw [parabolicTwoSmallBlock_entry] at he
  norm_num [g, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply, Fin.ext_iff] at he

/-- The two-residual kills the unipotent large block of the first node. -/
theorem firstNode_residual_large_block (g : firstNodeParabolic)
    (hg : g ∈ pResidual 2 firstNodeParabolic) :
    (parabolicLeviHom 2 (by decide)
      (inclusion (firstNode_le_parabolic 2 (by decide)) g)).2 = 1 := by
  let U := Theory.SpecificGroups.LinearSylowNormalizers.unipotent 3 (ZMod 2)
  let f : firstNodeParabolic →* U :=
    ((MonoidHom.snd _ _).comp ((parabolicLeviHom 2 (by decide)).comp
      (inclusion (firstNode_le_parabolic 2 (by decide))))).codRestrict U
        firstNode_large_block_unipotent
  have hp : IsPGroup 2 U :=
    Theory.SpecificGroups.LinearSylowNormalizers.unipotent_isPGroup 3 (ZMod 2) (by decide)
  have hq : IsPGroup 2 (firstNodeParabolic ⧸ f.ker) :=
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hx : f g = 1 := (show pResidual 2 firstNodeParabolic ≤ f.ker from
    sInf_le ⟨inferInstance,hq⟩) hg
  exact congrArg Subtype.val hx

end Representation.SL5ExteriorSquare


open Subgroup
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare

private theorem symmetric_three_residuals :
    pResidual 2 (Equiv.Perm (Fin 3)) = primeToResidual 3 (Equiv.Perm (Fin 3)) := by
  rw [Equiv.Perm.twoResidual_eq_alternating]
  symm
  apply primeToResidual_eq_of_generated (alternatingGroup (Fin 3))
    (by rw [alternatingGroup.index_eq_two]; decide)
    {g : Equiv.Perm (Fin 3) | g.IsThreeCycle}
    (Equiv.Perm.closure_three_cycles_eq_alternating)
  intro x hx
  refine ⟨1, ?_⟩
  simpa only [pow_one, ← hx.orderOf] using pow_orderOf_eq_one x

/-- The two- and prime-to-three residuals agree in the literal small block. -/
theorem smallBlock_twoResidual_eq_primeToThree :
    pResidual 2 SL(2,ZMod 2) = primeToResidual 3 SL(2,ZMod 2) := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_pResidual, map_primeToResidual]
  exact symmetric_three_residuals

/-- Both original notations denote the same first-node residual. -/
theorem firstNode_twoResidual_eq_primeToThree :
    pResidual 2 firstNodeParabolic = primeToResidual 3 firstNodeParabolic :=
  twoResidual_eq_primeToResidual_three_of_two_kernel firstNodeSmallHom
    firstNodeSmallHom_surjective firstNodeSmallHom_ker_isPGroup
    smallBlock_twoResidual_eq_primeToThree

/-- The two first-node choices meet in the original full flag subgroup. -/
theorem firstNode_inf_pointResidualFlag :
    firstNodeParabolic ⊓ parabolicResidualFlag 2 = flagGroup := by
  apply le_antisymm
  · rintro g ⟨hg,hgR⟩
    have hg2 := firstNode_le_parabolic 2 (by decide) hg
    have hr : g ∈ MiddleCore.twoFlag := by
      change g ∈ parabolicResidual 2 ⊔ flagGroup at hgR
      rw [parabolicResidual_two] at hgR
      exact hgR
    have hs := (MiddleCore.mem_twoFlag ⟨g,hg2⟩).mp hr
    have h10 := ((MiddleCore.mem_smallUnipotent _).mp hs).2.1
    apply mem_iInf.mpr
    intro k
    by_cases hk : k.val = 1
    · rw [hk]
      apply (mem_parabolic_iff_lowerLeft_zero 1 g).mpr
      intro i j hi hj
      have hj0 : j = (0 : Fin 5) := Fin.ext (by omega)
      subst j
      by_cases hi2 : 2 ≤ i.val
      · exact (mem_parabolic_iff_lowerLeft_zero 2 g).mp hg2 i 0 hi2 (by decide)
      · have hi1 : i = (1 : Fin 5) := Fin.ext (by omega)
        subst i
        exact (parabolicTwoSmallBlock_entry ⟨g,hg2⟩ 1 0).symm.trans h10
    · exact firstNode_le_parabolic k hk hg
  · exact le_inf flag_le_firstNode le_sup_right

end Representation.SL5ExteriorSquare
