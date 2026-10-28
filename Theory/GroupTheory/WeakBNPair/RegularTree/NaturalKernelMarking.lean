module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalActor

/-!
# Matrix markings of natural kernels and their reflections

Changing the SL₂ coordinates by an inner automorphism transports the natural
kernel by the same matrix. A nonidentity involution normalizing a nontrivial
diagonal element has an anti-diagonal matrix in characteristic two. Its
conjugation sends the full upper root onto the lower root with the explicit
scalar change. These calculations retain the original actor and kernel.

The source application constructs the two path-root images in one marking;
it does not infer naturality of a full kernel from a quotient by its center.
Source: DGS, *Groups and Graphs* (1985), (14.12)--(14.13), pp.217--218.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {X F : Type*} [Group X] [Field F] [CharP F 2]
variable {π : X →* SL(2,F)}

/-- Transport the full natural kernel through an inner marking of its unchanged quotient. -/
def NaturalKernel.marking (d : NaturalKernel π) (a : SL(2,F)) :
    NaturalKernel ((MulAut.conj a).toMonoidHom.comp π) := by
  let π' := (MulAut.conj a).toMonoidHom.comp π
  let e : π'.ker ≃* π.ker := MulEquiv.subgroupCongr
    (MonoidHom.ker_comp_of_injective π (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
  let A := Matrix.SL2.naturalAction F a
  refine ⟨(e.trans d.coords).trans A,?_⟩
  intro g z
  have he : e ⟨g*z*g⁻¹,(inferInstance : π'.ker.Normal).conj_mem z z.property g⟩=
      ⟨g*e z*g⁻¹,(inferInstance : π.ker.Normal).conj_mem (e z) (e z).property g⟩ := rfl
  change A (d.coords (e ⟨g*z*g⁻¹,_⟩))=
    Matrix.SL2.naturalAction F (a*π g*a⁻¹) (A (d.coords (e z)))
  rw [he,d.equivariant]
  have hr : (Matrix.SL2.naturalAction F (a*π g*a⁻¹))*A=
      A*(Matrix.SL2.naturalAction F (π g)) := by
    change (Matrix.SL2.naturalAction F (a*π g*a⁻¹))*(Matrix.SL2.naturalAction F a)=_
    rw [←map_mul,inv_mul_cancel_right,map_mul]
  exact (congrArg (fun f : MulAut (Multiplicative (Fin 2 → F)) =>
    f (d.coords (e z))) hr).symm

/-- A nonidentity involution normalizing a nontrivial diagonal element is anti-diagonal. -/
theorem braid_of_diagonal_normalizing_involution
    (g : SL(2,F)) (hgg : g*g=1) (hgne : g≠1)
    (b : F) (hb : b≠0) (hb1 : b≠1)
    (c : F) (hc : c≠0)
    (hconj : g*Matrix.SpecialLinearGroup.diag2 b hb*g⁻¹=Matrix.SpecialLinearGroup.diag2 c hc) :
    ∃ a : F, a≠0 ∧ g=upper a*lower a⁻¹*upper a := by
  have hmul : g*Matrix.SpecialLinearGroup.diag2 b hb=Matrix.SpecialLinearGroup.diag2 c hc*g := by
    rw [←hconj,mul_assoc,inv_mul_cancel,mul_one]
  have h00 : g.val 0 0=0 := by
    by_contra h00
    have he := congrArg (fun z : SL(2,F) => z.val 0 0) hmul
    have hh : g.val 0 0*b=g.val 0 0*c := by
      simpa [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply,Fin.sum_univ_two,mul_comm] using he
    have hbc : b=c := mul_left_cancel₀ h00 hh
    have hcomm : Commute g (Matrix.SpecialLinearGroup.diag2 b hb) := by
      subst c
      exact hmul
    obtain ⟨a,ha,hg⟩ := diagonal_of_commute g b hb hb1 hcomm
    have hsq : a^2=1 := by
      have he := congrArg (fun z : SL(2,F) => z.val 0 0) hgg
      rw [hg] at he
      simpa [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.diag2_coe',
        Matrix.mul_apply,Fin.sum_univ_two,pow_two] using he
    have ha1 : a=1 := by
      rcases sq_eq_one_iff.mp hsq with he | he
      · exact he
      · simpa only [CharTwo.neg_eq] using he
    apply hgne
    rw [hg]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.diag2_coe',ha1]
  have hdet : g.val 0 1*g.val 1 0=1 := by
    simpa only [Matrix.det_fin_two,h00,zero_mul,zero_sub,CharTwo.neg_eq] using g.property
  have ha : g.val 0 1≠0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : g.val 1 1=0 := by
    have he := congrArg (fun z : SL(2,F) => z.val 0 1) hgg
    have hh : g.val 0 1*g.val 1 1=0 := by
      simpa [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,h00] using he
    exact (mul_eq_zero.mp hh).resolve_left ha
  have h10 : g.val 1 0=(g.val 0 1)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  refine ⟨g.val 0 1,ha,?_⟩
  apply Subtype.ext
  rw [braid_matrix _ ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00,h11,h10]

/-- The same anti-diagonal reflection sends upper parameters to explicit lower parameters. -/
theorem braid_conjugates_upper (a : F) (ha : a≠0) (b : F) :
    (upper a*lower a⁻¹*upper a)*upper b*(upper a*lower a⁻¹*upper a)⁻¹=
      lower (a⁻¹^2*b) := by
  rw [inv_eq_of_mul_eq_one_right (braid_square a ha)]
  apply Subtype.ext
  change ((upper a*lower a⁻¹*upper a).val * (upper b).val) *
    (upper a*lower a⁻¹*upper a).val = (lower (a⁻¹^2*b)).val
  rw [braid_matrix _ ha]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul,dotProduct,upper,lower,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
      Fin.sum_univ_two,mul_inv_cancel₀ ha,inv_mul_cancel₀ ha,pow_two,mul_assoc,mul_comm,mul_left_comm]

end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic

