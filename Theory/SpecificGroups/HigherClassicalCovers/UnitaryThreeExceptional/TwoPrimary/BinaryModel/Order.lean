module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel.Pair
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.RepresentativeBound.UnitaryTwo
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.ScalarKernel

/-!
# Counting the full standard involution centralizer in PSU₄(3)

The determinant-product homomorphism on GU₂(3) × GU₂(3) maps onto the
four norm-one scalars. Its kernel therefore has order 2304. Every SU₄
lift of the projective centralizer is uniquely a compatible block pair,
optionally followed by block interchange, so the full preimage has order
4608. Its projective kernel is the entire SU₄ scalar kernel of order four.
Thus the centralizer has order 1152 and the concrete binary pair, whose
image has order 288, has index four.

The count reuses `RepresentativeBound/UnitaryTwo`, the signed block-shape
theorem in `RepresentativeCore/QuotientCore/Blocks`, and
`IsotropicStabilizers/ScalarKernel`. It does not use an ambient PSU₄ order
formula or enumerate four-by-four matrices.

Sources: GLS3, chapter 2, §2.7 and chapter 6, §6.1; local model input for
Aschbacher–Smith I.1.4(5), printed p.408 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks
@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel

private def detU : U₂ →* unitary F where
  toFun A := ⟨A.val.det, Matrix.det_of_mem_unitary A.property⟩
  map_one' := Subtype.ext Matrix.det_one
  map_mul' A D := Subtype.ext (Matrix.det_mul A.val D.val)

private def diagU (d : unitary F) : U₂ :=
  ⟨!![d.val,0;0,1], by
    rw [Matrix.mem_unitaryGroup_iff']
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, d.property.1]⟩

private theorem detU_diagU (d : unitary F) : detU (diagU d) = d := by
  apply Subtype.ext
  simp [detU, diagU, Matrix.det_fin_two]

private theorem unitScalar_card : Nat.card (unitary F) = 4 := by
  let e : unitary F ≃ {x : F // star x * x = 1} := {
    toFun x := ⟨x.val, x.property.1⟩
    invFun x := ⟨x.val, x.property, by simpa only [mul_comm] using x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

private def pairDet : (U₂ × U₂) →* unitary F where
  toFun p := detU p.1 * detU p.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

private theorem pairDet_surjective : Function.Surjective pairDet := by
  intro d
  refine ⟨(diagU d,1), ?_⟩
  change detU (diagU d) * detU 1 = d
  rw [detU_diagU, map_one, mul_one]

private abbrev BlockPairs := pairDet.ker

private theorem blockPairs_card : Nat.card BlockPairs = 2304 := by
  have h := pairDet.ker.card_mul_index
  have hi : pairDet.ker.index = 4 := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective pairDet pairDet_surjective).toEquiv,
      unitScalar_card]
  rw [hi] at h
  simp only [Nat.card_prod, RepresentativeBound.unitaryTwo_card] at h
  change Nat.card BlockPairs * 4 = 96 * 96 at h
  omega

private def makeSU (A : Mat₄) (hu : A.conjTranspose * A = 1) (hd : A.det = 1) :
    (form 4).specialSubgroup :=
  ⟨⟨A,A.conjTranspose,mul_eq_one_comm.mp hu,hu⟩,by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change A.conjTranspose * 1 * A = 1
      rwa [mul_one]
    · apply Units.ext; exact hd⟩

private def blockSU (p : BlockPairs) : (form 4).specialSubgroup :=
  makeSU (block p.val.1.val p.val.2.val) (by
    rw [block_adj, block_mul]
    change block (star p.val.1.val * p.val.1.val) (star p.val.2.val * p.val.2.val) = 1
    rw [Matrix.mem_unitaryGroup_iff'.mp p.val.1.property,
      Matrix.mem_unitaryGroup_iff'.mp p.val.2.property, block_one]) (by
    rw [block_det]
    exact congrArg Subtype.val p.property)

private def swapSU : (form 4).specialSubgroup := makeSU swap (by
  change star swap * swap = 1; rw [star_swap, swap_sq]) swap_det

private abbrev Lift := standardCentralizer.comap (project 4)

private def assemble (x : BlockPairs × Bool) : Lift :=
  ⟨if x.2 then blockSU x.1 * swapSU else blockSU x.1, by
    apply (project_mem_standardCentralizer_iff _).mpr
    cases x.2
    · exact Or.inl (block_commutes_standard _ _)
    · right
      change (block _ _ * swap) * standardInvolutionMatrix =
        -(standardInvolutionMatrix * (block _ _ * swap))
      rw [mul_assoc, swap_anti, mul_neg, ← mul_assoc, block_commutes_standard, mul_assoc]⟩

private theorem block_injective {A D E H : Mat₂} (he : block A D = block E H) : A = E ∧ D = H :=
  ⟨by simpa only [top_block] using congrArg top he,
   by simpa only [bot_block] using congrArg bot he⟩

private theorem block_ne_swap (A D E H : U₂) :
    block A.val D.val ≠ block E.val H.val * swap := by
  intro he
  have hz : A.val = 0 := by
    apply Matrix.ext; intro i j
    have h := congrArg (fun M : Mat₄ => M (Fin.castAdd 2 i) (Fin.castAdd 2 j)) he
    fin_cases i <;> fin_cases j <;>
      simpa [block, swap, Matrix.mul_apply, Fin.sum_univ_succ] using h
  have hu := Matrix.mem_unitaryGroup_iff'.mp A.property
  rw [hz] at hu
  have h := congrArg (fun M : Mat₂ => M 0 0) hu
  norm_num at h

private theorem assemble_injective : Function.Injective assemble := by
  rintro ⟨p,s⟩ ⟨q,t⟩ h
  have hm := congrArg (fun x : Lift => x.val.val.val) h
  have same (he : block p.val.1.val p.val.2.val = block q.val.1.val q.val.2.val) : p = q := by
    obtain ⟨hA,hD⟩ := block_injective he
    exact Subtype.ext (Prod.ext (Subtype.ext hA) (Subtype.ext hD))
  cases s <;> cases t
  · exact Prod.ext (same hm) rfl
  · exact (block_ne_swap _ _ _ _ hm).elim
  · exact (block_ne_swap _ _ _ _ hm.symm).elim
  · have hh := congrArg (fun M : Mat₄ => M * swap) hm
    change (block _ _ * swap) * swap = (block _ _ * swap) * swap at hh
    simp only [mul_assoc, swap_sq, mul_one] at hh
    exact Prod.ext (same hh) rfl

private theorem assemble_surjective : Function.Surjective assemble := by
  intro g
  obtain ⟨A,D,hd,he⟩ := signed_exists g.val g.property
  let p : BlockPairs := ⟨(A,D), Subtype.ext hd⟩
  rcases he with he | he
  · refine ⟨(p,false), Subtype.ext (Subtype.ext (Units.ext ?_))⟩
    exact he.symm
  · refine ⟨(p,true), Subtype.ext (Subtype.ext (Units.ext ?_))⟩
    exact he.symm

private theorem lift_card : Nat.card Lift = 4608 := by
  rw [← Nat.card_congr (Equiv.ofBijective assemble ⟨assemble_injective,assemble_surjective⟩),
    Nat.card_prod, blockPairs_card]
  norm_num

private def liftProject : Lift →* standardCentralizer where
  toFun g := ⟨project 4 g.val, g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (project 4) x.val y.val)

private theorem liftProject_surjective : Function.Surjective liftProject := by
  intro g
  obtain ⟨s,hs⟩ := project_surjective 4 g.val
  exact ⟨⟨s, by change project 4 s ∈ standardCentralizer; rw [hs]; exact g.property⟩,
    Subtype.ext hs⟩

private def liftKernelEquiv : liftProject.ker ≃ (project 4).ker where
  toFun g := ⟨g.val.val, congrArg Subtype.val g.property⟩
  invFun g := ⟨⟨g.val, by
    change project 4 g.val ∈ standardCentralizer
    rw [g.property]
    exact standardCentralizer.one_mem⟩, Subtype.ext g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full projective centralizer has order 1152: 2304 compatible block pairs,
then block interchange, divided by the full scalar kernel of order four. -/
theorem standardCentralizer_card : Nat.card standardCentralizer = 1152 := by
  have hk : Nat.card liftProject.ker = 4 := by
    rw [Nat.card_congr liftKernelEquiv]
    exact IsotropicStabilizers.scalarKernel_card (form 4) (form_conj_cube 4)
  have h := liftProject.ker.card_mul_index
  rw [hk, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      liftProject liftProject_surjective).toEquiv, lift_card] at h
  omega

/-- The same concrete binary pair has index four in the full centralizer. -/
theorem pair_range_index : pair.range.index = 4 := by
  have h := pair.range.card_mul_index
  rw [pair_range_card, standardCentralizer_card] at h
  omega

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel
