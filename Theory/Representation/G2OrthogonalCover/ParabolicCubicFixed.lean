module
public import Theory.Representation.G2OrthogonalCover.ParabolicFixed
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Cubic fixed vectors in moved G₂ parabolic cover subspaces

The short residual's two-core fixes only the natural plane. A cubic element
of its actual two-core quotient acts there as a cubic SL₂ matrix, so fixes
only zero. The cover kernel is globally fixed and misses every fully moved
core-fixed subspace. For the long residual that entire moved subspace is zero.
Conjugation retains the original subgroup, its two-core and the cubic element.

Source: Aschbacher--Smith, 9.4.1 and I.2.3(1), printed pp.735 and413.
Root coordinates use the attributed ATLAS imports (LICENSES/ATLAS.txt).
-/

public noncomputable section
open Atlas.SplitOctonion Representation Representation.OneCohomology
open Representation.BinaryOffender Subgroup Matrix
open scoped MatrixGroups
namespace Atlas.G2.Natural.OrthogonalCover.ParabolicCubicFixed
open Explicit LieParabolicSetup SylowFlag ParabolicFixed
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
private theorem natural_short_fixed (v : Space F)
    (h : ∀ q ∈ radical₁ (F := F), Natural.action F q v = v) :
    v ∈ naturalPlane F := by
  let c := Restricted.NaturalCoordinates.equiv F v
  have hc (q : Model F) (hq : q ∈ radical₁) :
      Restricted.NaturalCoordinates.action F q c = c := by
    change Restricted.NaturalCoordinates.equiv F
      (Natural.action F q ((Restricted.NaturalCoordinates.equiv F).symm c)) = c
    rw [show (Restricted.NaturalCoordinates.equiv F).symm c = v from
      (Restricted.NaturalCoordinates.equiv F).symm_apply_apply v, h q hq]
  have ha := hc (rootA 1) ⟨![1,0,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  have hb := hc (rootB 1) ⟨![0,1,0,0,0,0], by simp, by simp [unipotentProduct]⟩
  have hd := hc (rootD 1) ⟨![0,0,0,1,0,0], by simp, by simp [unipotentProduct]⟩
  have h2 : c 2 = 0 := by simpa using congrFun hd 0
  have h3 : c 3 = 0 := by simpa using congrFun hb 0
  have h4 : c 4 = 0 := by simpa using congrFun ha 0
  have h5 : c 5 = 0 := by simpa using congrFun ha 1
  apply (mem_naturalPlane F v).mpr
  refine ⟨c 0,c 1,?_⟩
  change c = _
  ext i
  fin_cases i <;> simp [h2,h3,h4,h5]


omit [Algebra (ZMod 2) F] in
private theorem short_plane_cubic_fixed [Finite F]
    (b : local₁ (F := F))
    (hb : orderOf (QuotientGroup.mk' (pCore 2 (local₁ (F := F))) b) = 3)
    (v : Space F) (hv : v ∈ naturalPlane F) (hfix : Natural.action F b.val v = v) :
    v = 0 := by
  obtain ⟨x,⟨a,rfl⟩,rfl⟩ := hv
  let e : (local₁ (F := F) ⧸ pCore 2 (local₁ (F := F))) ≃* SL(2,F) :=
    (QuotientGroup.quotientMulEquivOfEq local₁_intrinsic_pCore).trans
      local₁RadicalQuotientEquivSL
  have he : e (QuotientGroup.mk' (pCore 2 (local₁ (F := F))) b) = shortSLHom b := rfl
  have ho : orderOf (shortSLHom b) = 3 := by
    rw [←he,e.orderOf_eq]
    exact hb
  have hplane : (planeLift F a).val = a 0 • basisVector 0 + a 1 • basisVector 1 := by
    ext i
    fin_cases i <;> simp [planeLift,basisVector]
  have hcoord := congrArg (Restricted.NaturalCoordinates.coordinates F) hfix
  rw [action_mk,Restricted.NaturalCoordinates.coordinates_mk,
    Restricted.NaturalCoordinates.coordinates_mk] at hcoord
  have hmat : (shortSLHom b).val *ᵥ a = a := by
    ext i
    fin_cases i
    · have hi := congrFun hcoord 0
      change b.val.val (planeLift F a).val 0 = a 0 at hi
      rw [hplane,map_add,map_smul,map_smul] at hi
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      change b.val.val (basisVector 0) 0 * a 0 +
        b.val.val (basisVector 1) 0 * a 1 = a 0
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hi
    · have hi := congrFun hcoord 1
      change b.val.val (planeLift F a).val 1 = a 1 at hi
      rw [hplane,map_add,map_smul,map_smul] at hi
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      change b.val.val (basisVector 0) 1 * a 0 +
        b.val.val (basisVector 1) 1 * a 1 = a 1
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using hi
  rw [Matrix.SL2.cubic_fixed_eq_zero (shortSLHom b) ho a hmat,map_zero,map_zero]

variable [Finite F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (Model F) W}
  (p : σ.IntertwiningMap (fullBinaryNatural F))

omit [CharP F 2] [Algebra (ZMod 2) F] [Finite F] [FiniteDimensional (ZMod 2) W] in
private theorem conjugate_action (g b : Model F) (w : W) :
    σ ((MulAut.conj g) b) (σ g w) = σ g (σ b w) := by
  rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
  congr 2
  simp [MulAut.conj_apply,mul_assoc]

omit [CharP F 2] [Algebra (ZMod 2) F] [Finite F] [FiniteDimensional (ZMod 2) W] in
private theorem conjugate_core_fixed (B : Subgroup (Model F)) (g : Model F)
    (w : W) (hw : w ∈ fixedSpace σ (B.pCoreIn 2)) :
    σ g w ∈ fixedSpace σ ((B.map (MulAut.conj g).toMonoidHom).pCoreIn 2) := by
  intro q
  have hq : q.val ∈ (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    exact q.property
  obtain ⟨r,hr,he⟩ := hq
  change σ q.val (σ g w) = σ g w
  rw [←he]
  change σ ((MulAut.conj g) r) (σ g w) = σ g w
  rw [conjugate_action]
  exact congrArg (σ g) (hw ⟨r,hr⟩)

/-- A cubic in the actual local two-core quotient fixes no nonzero vector
of a fully moved core-fixed subspace in a central natural G₂ cover. -/
theorem cover_moved_subspace_cubic_fixed_eq_zero
    (hq : 2 < Nat.card F) (hp : IsCover p)
    (B : Subgroup (Model F)) (g : Model F)
    (hB : B.map (MulAut.conj g).toMonoidHom = local₁ ∨
      B.map (MulAut.conj g).toMonoidHom = local₂)
    (A : Submodule (ZMod 2) W) (hA : A ≤ fixedSpace σ (B.pCoreIn 2))
    (hm : subspaceCommutator σ A B = A)
    (b : B) (hb : orderOf (QuotientGroup.mk' (pCore 2 B) b) = 3)
    (w : W) (hw : w ∈ A) (hfix : σ b.val w = w) : w = 0 := by
  have hinj (x y : W) (he : σ g x = σ g y) : x = y := by
    have hh := congrArg (σ g⁻¹) he
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] using hh
  rcases hB with hB | hB
  · let eB : B ≃* local₁ (F := F) :=
      (B.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hB)
    let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
    have ho : orderOf (QuotientGroup.mk' (pCore 2 (local₁ (F := F))) (eB b)) = 3 := by
      change orderOf (eQ (QuotientGroup.mk' (pCore 2 B) b)) = 3
      rw [eQ.orderOf_eq]
      exact hb
    have hw' : σ g w ∈ fixedSpace σ ((local₁ (F := F)).pCoreIn 2) := by
      rw [←hB]
      exact conjugate_core_fixed F B g w (hA hw)
    have hn : p (σ g w) ∈ naturalPlane F := by
      apply natural_short_fixed F
      intro r hr
      change fullBinaryNatural F r (p (σ g w)) = p (σ g w)
      rw [←p.isIntertwining]
      exact congrArg p (hw' ⟨r,by rwa [local₁_pCore]⟩)
    have hf : Natural.action F (eB b).val (p (σ g w)) = p (σ g w) := by
      change fullBinaryNatural F ((MulAut.conj g) b.val) (p (σ g w)) = _
      rw [←p.isIntertwining,conjugate_action,hfix]
    have hz := short_plane_cubic_fixed F (eB b) ho (p (σ g w)) hn hf
    have hpw : p w = 0 := by
      have hh := congrArg (fullBinaryNatural F g⁻¹) hz
      rw [p.isIntertwining,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply,map_zero] at hh
      exact hh
    exact Submodule.disjoint_def.mp
      (cover_moved_subspace_disjoint F p hq hp B g (Or.inl hB) A hA hm)
      w hw (hp.2.1 hpw)
  · have hAF : A ≤ fixedSpace σ B := by
      intro x hx c
      apply hinj
      have hx' : σ g x ∈ fixedSpace σ ((local₂ (F := F)).pCoreIn 2) := by
        rw [←hB]
        exact conjugate_core_fixed F B g x (hA hx)
      have hc : (MulAut.conj g) c.val ∈ local₂ :=
        hB ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom c.property
      have hh := long_fixed F p hq hp hx' ⟨(MulAut.conj g) c.val,hc⟩
      change σ ((MulAut.conj g) c.val) (σ g x) = σ g x at hh
      rwa [conjugate_action] at hh
    have hz : A = ⊥ := hm.symm.trans ((subspaceCommutator_eq_bot_iff _ _ _).mpr hAF)
    simpa only [hz,Submodule.mem_bot] using hw

end Atlas.G2.Natural.OrthogonalCover.ParabolicCubicFixed
