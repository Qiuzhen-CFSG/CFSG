module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondCocycles
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondReduction
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.Core
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondEmbedding

/-!
# The two fixed-core orbits of second-endpoint reflections

The reflection-fiber cocycle equations leave six binary coordinates. Explicit
conjugators in the first reflection's core centralizer place each cocycle in
one of the two fibers represented by the second reflection and its root-one
conjugate. The checked dihedral quotient reduction then covers every involution
outside the original common Borel. All statements retain `secondSylow`, so the
ambient pair-census consumer uses the literal parabolic embeddings.

Source: binary Ree parabolic reflection geometry used in quasithin F.4.8;
root coordinates follow Shinoda (1975), pp. 81–83 and Parrott (1972), p. 683.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo SecondExtension

private def fixedCore (a b c d e f : ZMod 2) : Core :=
  ⟨a,b,c,b,a,d,e,a+a*b+b*c+e,a*b+a*c+d,f⟩

private theorem fixedCore_fixed (a b c d e f : ZMod 2) : Core.r (fixedCore a b c d e f) = fixedCore a b c d e f := by
  rw [← rPolynomial_eq]
  apply Core.ext <;> simp [rPolynomial, fixedCore]
  all_goals try ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals try ring_nf
  all_goals reduce_mod_char

private def secondCocycle (a b c d e f : ZMod 2) : SylowModel :=
  ⟨⟨0,a,b,b,c,d,c,e,f,b+b*c+c*d+f⟩,
    Multiplicative.ofAdd ((a.val : ZMod 4)+2*(d.val : ZMod 4))⟩

private def secondWitness (a b c d e f : ZMod 2) : Core :=
  fixedCore 0 e (a+b) (d+e+a*e) (a*b+c+e+a*e+b*e)
    (a+b+a*c+d+a*e+b*e+f)

def secondReflection : SecondModel := SemidirectProduct.inr (DihedralGroup.sr 0)
def secondRootOne : SecondModel := secondSylow SylowModel.rootOne

def secondRepresentative (e : ZMod 2) : SecondModel :=
  if e=0 then secondReflection else secondRootOne⁻¹ * secondReflection * secondRootOne

private def secondRepPrefix (e : ZMod 2) : SylowModel :=
  if e=0 then 1 else ⟨⟨0,1,1,1,1,0,1,0,1,1⟩,Multiplicative.ofAdd 1⟩

private theorem secondWitness_equation (a b c d e f : ZMod 2) :
    SylowModel.Collected.collectedMul (secondCocycle a b c d e f)
      (secondWeylPolynomial (SemidirectProduct.inl (secondWitness a b c d e f))) =
    SylowModel.Collected.collectedMul (SemidirectProduct.inl (secondWitness a b c d e f))
      (secondRepPrefix (a+e)) := by
  exact (by decide +kernel : ∀ a b c d e f : ZMod 2,
    SylowModel.Collected.collectedMul (secondCocycle a b c d e f)
      (secondWeylPolynomial (SemidirectProduct.inl (secondWitness a b c d e f))) =
    SylowModel.Collected.collectedMul (SemidirectProduct.inl (secondWitness a b c d e f))
      (secondRepPrefix (a+e))) a b c d e f


private theorem secondAction_sr_zero : secondAction (DihedralGroup.sr 0) = secondWeyl := by
  change secondWeyl * rotationAction ^ (0 : ZMod 3).val = secondWeyl
  simp only [ZMod.val_zero,pow_zero,mul_one]

private def secondSr (x : radical) : SecondModel := ⟨x,DihedralGroup.sr 0⟩

private theorem secondSr_mul_inl (x g : radical) :
    secondSr x * SemidirectProduct.inl g = secondSr (x*secondWeyl g) := by
  apply SemidirectProduct.ext
  · change x * secondAction (DihedralGroup.sr 0) g = _
    rw [secondAction_sr_zero]
    rfl
  · simp [secondSr,SemidirectProduct.mul_right]

private theorem inl_mul_secondSr (g x : radical) :
    SemidirectProduct.inl g * secondSr x = secondSr (g*x) := by
  apply SemidirectProduct.ext
  · change g * secondAction 1 x = _
    rw [map_one, MulAut.one_apply]
    rfl
  · simp [secondSr,SemidirectProduct.mul_right]

private def rootOneRadical : radical := ⟨SylowModel.rootOne,rfl⟩

private theorem secondRepPrefix_mem (e : ZMod 2) : secondRepPrefix e ∈ radical := by
  by_cases h:e=0 <;> simp [secondRepPrefix,h,mem_radical]

private theorem secondRepresentative_eq (e : ZMod 2) :
    secondRepresentative e = secondSr ⟨secondRepPrefix e,secondRepPrefix_mem e⟩ := by
  fin_cases e
  · rfl
  · have hu : secondRootOne = SemidirectProduct.inl rootOneRadical :=
      secondSylow_radical rootOneRadical
    change secondRootOne⁻¹ * secondSr 1 * secondRootOne = _
    rw [hu,← map_inv,inl_mul_secondSr,secondSr_mul_inl]
    apply congrArg secondSr
    apply Subtype.ext
    change (SylowModel.rootOne)⁻¹ * 1 * (secondWeyl rootOneRadical).val = _
    rw [mul_one,← secondWeylPolynomial_eq,← SylowModel.Collected.collectedInv_eq,
      ← SylowModel.Collected.collectedMul_eq]
    decide +kernel


theorem second_fiber_conjugate (y : SecondModel) (hy : y^2=1)
    (hq : y.right = DihedralGroup.sr 0) :
    ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
      y = secondSylow (SemidirectProduct.inl g) * secondRepresentative e *
        (secondSylow (SemidirectProduct.inl g))⁻¹ := by
  have hc : y.left.val * secondWeylPolynomial y.left.val = 1 := by
    have he := congrArg (fun z : SecondModel => z.left.val) hy
    rw [pow_two] at he
    change y.left.val * (secondAction y.right y.left).val = 1 at he
    rw [hq,secondAction_sr_zero,← secondWeylPolynomial_eq] at he
    exact he
  have hn := polynomial_cocycle_form y.left.val y.left.property hc
  let a := y.left.val.left.b1
  let b := y.left.val.left.b2
  let c := y.left.val.left.b4
  let d := y.left.val.left.b5
  let e := y.left.val.left.b7
  let f := y.left.val.left.b8
  let g := secondWitness a b c d e f
  have hg : Core.r g = g := fixedCore_fixed ..
  let gr : radical := ⟨SemidirectProduct.inl g,rfl⟩
  refine ⟨g,hg,a+e,?_⟩
  have hySr : y = secondSr y.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hq
  have hge : secondSylow (SemidirectProduct.inl g) = SemidirectProduct.inl gr :=
    secondSylow_radical gr
  rw [hySr,hge]
  apply (eq_mul_inv_iff_mul_eq).2
  rw [secondRepresentative_eq,secondSr_mul_inl,inl_mul_secondSr]
  apply congrArg secondSr
  apply Subtype.ext
  change y.left.val * (secondWeyl gr).val = gr.val * secondRepPrefix (a+e)
  rw [← secondWeylPolynomial_eq]
  change y.left.val * secondWeylPolynomial (SemidirectProduct.inl g) = _
  have he := secondWitness_equation a b c d e f
  rw [SylowModel.Collected.collectedMul_eq,SylowModel.Collected.collectedMul_eq] at he
  have hform : y.left.val = secondCocycle a b c d e f := hn
  rw [hform]
  exact he

theorem second_involution_conjugate (y : SecondModel) (hy : y^2=1)
    (hn : y∉secondSylow.range) :
    ∃ g : Core, Core.r g = g ∧ ∃ e : ZMod 2,
      y = secondSylow (SemidirectProduct.inl g) * secondRepresentative e *
        (secondSylow (SemidirectProduct.inl g))⁻¹ :=
  second_involution_conjugate_of_fiber secondRepresentative second_fiber_conjugate y hy hn

end Tits.AmalgamRigidity.FullRee.PointedPairs
