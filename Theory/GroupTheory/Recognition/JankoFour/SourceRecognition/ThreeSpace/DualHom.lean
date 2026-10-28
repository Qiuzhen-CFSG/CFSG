module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.DualGeneration
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.MultiplicitySimple

/-!
# The full contragredient radical action

Evaluation on the original source basis identifies Hom(Z,W) with the three
copies of the original rank-four pair section W. The simultaneous root
coordinates give equivariance for the shear and adjacent swaps. The marked
root-generation theorem extends this to every element of the literal K/R.
The original S/R acts by postcomposition on W in the same equivalence.

Thus R/Z(R) is the Hom module from the actual Z to the actual W, with both
source quotient actions retained. The next tensor extension expresses this
as Z* tensor W; identifying W as the natural L₂(4) module remains separate.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.4), pp.597–598, DOI 10.1007/BF01232280.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
local instance : IsElementaryAbelian 2 d.space := d.elementary
variable (W : Type*) [Group W] [IsElementaryAbelian 2 W]

private def homToTriple : (d.space →* W) →* W × (W × W) where
  toFun f := (f (d.markedPoint 2), f (d.markedPoint 1), f (d.markedPoint 0))
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem homToTriple_injective : Function.Injective (d.homToTriple W) := by
  intro f g he
  apply MonoidHom.eq_of_eqOn_dense d.markedPoint_generates
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact congrArg (fun w : W × (W × W) => w.2.2) he
  · exact congrArg (fun w : W × (W × W) => w.2.1) he
  · exact congrArg (fun w : W × (W × W) => w.1) he

private theorem homToTriple_surjective : Function.Surjective (d.homToTriple W) := by
  rintro ⟨u,v,w⟩
  let b := (Pi.basisFun (ZMod 2) (Fin 3)).map d.markedCoordinates
  let f := b.constr (ZMod 2) ![Additive.ofMul w,Additive.ofMul v,Additive.ofMul u]
  refine ⟨f.toAddMonoidHom.toMultiplicative,?_⟩
  have hf (i : Fin 3) : f (Additive.ofMul (d.markedPoint i)) =
      ![Additive.ofMul w,Additive.ofMul v,Additive.ofMul u] i := by
    have hb : b i = Additive.ofMul (d.markedPoint i) := by
      simp [b,d.markedCoordinates_single]
    rw [←hb]
    exact b.constr_basis (ZMod 2) _ i
  exact Prod.ext (congrArg Additive.toMul (hf 2))
    (Prod.ext (congrArg Additive.toMul (hf 1)) (congrArg Additive.toMul (hf 0)))

private noncomputable def homTripleEquiv : (d.space →* W) ≃* W × (W × W) :=
  MulEquiv.ofBijective (d.homToTriple W) ⟨d.homToTriple_injective W,d.homToTriple_surjective W⟩

@[simp] private theorem homTripleEquiv_apply (f : d.space →* W) :
    d.homTripleEquiv W f = (f (d.markedPoint 2),f (d.markedPoint 1),f (d.markedPoint 0)) := rfl


variable {W} in
private def compatibleSubgroup {V : Type*} [Group V]
    (ρ : MulAut d.space →* MulAut V)
    (F : V →* (d.space →* W)) : Subgroup (MulAut d.space) where
  carrier := {a | ∀ v t, F (ρ a v) (a t) = F v t}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb v t
    rw [map_mul,MulAut.mul_apply,MulAut.mul_apply,ha,hb]
  inv_mem' := by
    intro a ha v t
    have hh := ha (ρ a⁻¹ v) (a⁻¹ t)
    rw [map_inv] at hh
    simpa only [map_inv,MulAut.apply_inv_self] using hh.symm

attribute [local instance] R_normal_in_K R_normal_in_S_intrinsic

/-- The literal radical is the contragredient Hom module for the same three-space and four-space. -/
theorem exists_radical_hom_equiv (h : IsTypeJ4 z) :
    letI := d.multiplicitySpace_elementary h
    ∃ F : (d.R ⧸ center d.R) ≃* (d.space →* d.multiplicitySpace),
      (∀ a : MulAut d.space, ∀ v t,
        F (d.linearRadicalAction h a v) (a t) = F v t) ∧
      (∀ b : d.S ⧸ d.R.subgroupOf d.S, ∀ v t,
        F (d.SRadicalAction h b v) t = d.multiplicityAction h b (F v t)) := by
  let := d.R_center_quotient_elementary h
  let := d.multiplicitySpace_elementary h
  obtain ⟨f,_,hS,ha,hp,hq⟩ := d.exists_multiplicity_coordinates_root_actions h
  let F := f.symm.trans (d.homTripleEquiv d.multiplicitySpace).symm
  have hF (u v w : d.multiplicitySpace) :
      F (f (u,v,w)) (d.markedPoint 2) = u ∧
      F (f (u,v,w)) (d.markedPoint 1) = v ∧
      F (f (u,v,w)) (d.markedPoint 0) = w := by
    have he : d.homTripleEquiv d.multiplicitySpace (F (f (u,v,w))) = (u,v,w) := by
      simp only [F,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply]
    exact ⟨congrArg Prod.fst he,congrArg (fun t => t.2.1) he,congrArg (fun t => t.2.2) he⟩
  have hmarker (u v w : d.multiplicitySpace) (i : Fin 3) :
      F (f (u,v,w)) (d.markedPoint i) = ![w,v,u] i := by
    fin_cases i
    · exact (hF u v w).2.2
    · exact (hF u v w).2.1
    · exact (hF u v w).1
  let H := d.compatibleSubgroup (d.linearRadicalAction h) F.toMonoidHom
  have hmem (a : MulAut d.space)
      (ha : ∀ u v w : d.multiplicitySpace, ∀ i : Fin 3,
        F (d.linearRadicalAction h a (f (u,v,w))) (a (d.markedPoint i)) =
          F (f (u,v,w)) (d.markedPoint i)) : a ∈ H := by
    intro v t
    obtain ⟨⟨u,v,w⟩,rfl⟩ := f.surjective v
    have he : (F (d.linearRadicalAction h a (f (u,v,w)))).comp a.toMonoidHom = F (f (u,v,w)) := by
      apply MonoidHom.eq_of_eqOn_dense d.markedPoint_generates
      rintro _ ⟨i,rfl⟩
      exact ha u v w i
    exact congrArg (fun g : d.space →* d.multiplicitySpace => g t) he
  have hshear : d.markedShear ∈ H := by
    apply hmem
    intro u v w i
    rw [ha]
    fin_cases i
    · change F (f (u,v,v*w)) (d.markedShear (d.markedPoint 0)) = F (f (u,v,w)) (d.markedPoint 0)
      rw [d.markedShear_points.1,map_mul,(hF u v (v*w)).2.2,(hF u v (v*w)).2.1,
        (hF u v w).2.2]
      have hv : v*v=1 := by
        simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 d.multiplicitySpace) v
      calc
        (v*w)*v = (v*v)*w := by ac_rfl
        _ = w := by rw [hv,one_mul]
    · change F (f (u,v,v*w)) (d.markedShear (d.markedPoint 1)) = F (f (u,v,w)) (d.markedPoint 1)
      rw [d.markedShear_points.2.1,(hF u v (v*w)).2.1,(hF u v w).2.1]
    · change F (f (u,v,v*w)) (d.markedShear (d.markedPoint 2)) = F (f (u,v,w)) (d.markedPoint 2)
      rw [d.markedShear_points.2.2,(hF u v (v*w)).1,(hF u v w).1]
  have hswap01 : d.markedPermutation (Equiv.swap 0 1) ∈ H := by
    apply hmem
    intro u v w i
    rw [hp,d.markedPermutation_point,hmarker,hmarker]
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hswap12 : d.markedPermutation (Equiv.swap 1 2) ∈ H := by
    apply hmem
    intro u v w i
    rw [hq,d.markedPermutation_point,hmarker,hmarker]
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have htop : H=⊤ := by
    apply top_unique
    rw [←d.marked_roots_generate]
    apply (closure_le _).mpr
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact hshear
    · exact hswap01
    · exact hswap12
  refine ⟨F,?_,?_⟩
  · intro a v t
    exact (show a ∈ H from htop ▸ mem_top a) v t
  · intro b v t
    obtain ⟨⟨u,v,w⟩,rfl⟩ := f.surjective v
    have he : F (d.SRadicalAction h b (f (u,v,w))) =
        (d.multiplicityAction h b).toMonoidHom.comp (F (f (u,v,w))) := by
      apply MonoidHom.eq_of_eqOn_dense d.markedPoint_generates
      rintro _ ⟨i,rfl⟩
      rw [←hS]
      change F (f (d.multiplicityAction h b u,d.multiplicityAction h b v,
        d.multiplicityAction h b w)) (d.markedPoint i) =
        d.multiplicityAction h b (F (f (u,v,w)) (d.markedPoint i))
      rw [hmarker,hmarker]
      fin_cases i <;> rfl
    exact congrArg (fun g : d.space →* d.multiplicitySpace => g t) he

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
