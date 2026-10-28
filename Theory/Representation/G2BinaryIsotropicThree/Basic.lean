module

public import Theory.Representation.G2BinaryIsotropicThree.Certificate
public import Theory.Representation.G2BinaryNondegeneratePlane.Stabilizer

/-!
# The two three-space targets for the binary natural G₂ geometry

Both coordinate targets have dimension three. An octonion automorphism fixing
the second target pointwise fixes three singular basis vectors; their products
recover the entire octonion basis. Its pointwise stabilizer is therefore
trivial. This gives the exact faithful branch needed in 13.3.12(3), without
merging the two corresponding orbits of the derived group.

Source: Aschbacher–Smith 13.3.12, printed p.890.
-/

@[expose] public section

open Atlas.SplitOctonion Module Submodule
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

def target (b : Bool) : Submodule K W where
  carrier := {v | Certificate.inTarget b v}
  zero_mem' := by cases b <;> simp [Certificate.inTarget]
  add_mem' := by
    intro x y hx hy
    cases b <;> simp_all [Certificate.inTarget]
  smul_mem' := by
    intro a x hx
    cases b <;> simp_all [Certificate.inTarget]

def targetEmbed (b : Bool) : (Fin 3→K) →ₗ[K] W where
  toFun v := if b then ![v 0,0,0,v 1,v 2,0] else ![v 0,v 1,v 2,0,0,0]
  map_add' x y := by cases b <;> ext i <;> fin_cases i <;> simp
  map_smul' a x := by cases b <;> ext i <;> fin_cases i <;> simp

def targetCoord (b : Bool) : W →ₗ[K] (Fin 3→K) where
  toFun v := if b then ![v 0,v 3,v 4] else ![v 0,v 1,v 2]
  map_add' x y := by cases b <;> ext i <;> fin_cases i <;> simp
  map_smul' a x := by cases b <;> ext i <;> fin_cases i <;> simp

def targetEquiv (b : Bool) : (Fin 3→K) ≃ₗ[K] target b where
  toFun v := ⟨targetEmbed b v,by cases b <;> simp [target,targetEmbed,Certificate.inTarget]⟩
  invFun v := targetCoord b v.val
  left_inv v := by cases b <;> ext i <;> fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    have hv := v.property
    cases b <;> simp only [target,Certificate.inTarget] at hv
    · ext i
      fin_cases i <;> simp [targetEmbed,targetCoord,hv.1,hv.2.1,hv.2.2]
    · ext i
      fin_cases i <;> simp [targetEmbed,targetCoord,hv.1,hv.2.1,hv.2.2]
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' a x := Subtype.ext (map_smul _ a x)

theorem finrank_target (b : Bool) : finrank K (target b)=3 := by
  rw [←(targetEquiv b).finrank_eq]
  simp

private theorem fixed_basis_of_fixed_coordinate (g : Model K) (i : Fin 8)
    (hi : i≠3) (hi' : i≠4)
    (hx : rho g (Atlas.G2.Restricted.NaturalCoordinates.projection K
      ⟨basisVector i,by simp [mem_traceZero,SplitOctonion.trace,basisVector,Ne.symm hi,Ne.symm hi']⟩)=
      Atlas.G2.Restricted.NaturalCoordinates.projection K
      ⟨basisVector i,by simp [mem_traceZero,SplitOctonion.trace,basisVector,Ne.symm hi,Ne.symm hi']⟩) :
    g.val (basisVector i)=basisVector i := by
  have ht : SplitOctonion.trace (basisVector i : Carrier K)=0 := by
    simp [SplitOctonion.trace,basisVector,Ne.symm hi,Ne.symm hi']
  have he : Natural.action K g (mk K ⟨basisVector i,ht⟩)=mk K ⟨basisVector i,ht⟩ := by
    apply (equiv K).injective
    change rho g (equiv K (mk K ⟨basisVector i,ht⟩))=equiv K (mk K ⟨basisVector i,ht⟩) at hx
    change equiv K (Natural.action K g ((equiv K).symm (equiv K _)))=_ at hx
    simpa only [LinearEquiv.symm_apply_apply] using hx
  obtain ⟨r,hr⟩ := (mk_eq_mk_iff K _ _).mp he
  change r • unit=g.val (basisVector i)-basisVector i at hr
  have hv : g.val (basisVector i)=r • unit+basisVector i := (eq_sub_iff_add_eq.mp hr).symm
  have hn := automorphism_norm g (basisVector i)
  rw [hv] at hn
  have hr0 : r=0 := by
    clear hx he ht hv hr
    fin_cases i <;> simp_all [SplitOctonion.norm,unit,basisVector]
  simpa [hr0] using hv

private def basisWord (x y z : Carrier K) : Fin 8→Carrier K :=
  ![x,mul x y,mul x z,mul x (mul y z),mul (mul y z) x,y,z,mul y z]
private theorem basisWord_eq : ∀i,
    basisWord (basisVector 0) (basisVector 5) (basisVector 6) i=basisVector i := by decide +kernel

theorem eq_one_of_fixes_other (g : Model K)
    (hg : ∀v∈target true,rho g v=v) : g=1 := by
  have hfix (i : Fin 8) (hi : i=0∨i=5∨i=6) : g.val (basisVector i)=basisVector i := by
    rcases hi with rfl|rfl|rfl
    all_goals
      apply fixed_basis_of_fixed_coordinate g _ (by decide) (by decide)
      apply hg
      simp [target,Certificate.inTarget,Atlas.G2.Restricted.NaturalCoordinates.projection,basisVector]
  have h0 := hfix 0 (Or.inl rfl)
  have h5 := hfix 5 (Or.inr (Or.inl rfl))
  have h6 := hfix 6 (Or.inr (Or.inr rfl))
  have hh (i : Fin 8) : g.val (basisVector i)=basisVector i := by
    rw [←basisWord_eq i]
    fin_cases i <;> simp [basisWord,automorphism_mul,h0,h5,h6]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro i
  simpa [Pi.basisFun_apply,basisVector] using hh i

end Atlas.G2.Natural.BinaryIsotropicThree
