module

public import Theory.Representation.G2NaturalOffenders.Long
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The pointwise fixer of a long-root fixed space in the natural G₂ module

In characteristic two the fixed four-space of a nonidentity A-root element
has full pointwise fixer equal to the one-parameter A-root subgroup. Norm
preservation lifts fixed quotient vectors to fixed octonion vectors. A Weyl
conjugation places three of them in the opposite-pair stabilizer, whose SL₂
matrix must be upper unitriangular. Conjugating back identifies the actual
root parameter. The final theorem transports both the fixed space and the
root subgroup by the same conjugation.

This is the pointwise-fixer assertion used in Aschbacher–Smith K.4.5,
printed p.460, from the natural-module geometry of B.4.6(4), printed p.88.
The proof uses the literal octonion quotient and its binary scalar restriction;
no finite group order or classification premise is needed.
-/

@[expose] public noncomputable section

open Atlas.G2 Atlas.SplitOctonion
open Atlas.G2.Restricted.NaturalCoordinates
open Atlas.G2.NaturalOffenders
open Representation Representation.BinaryOffender Subgroup
open scoped MatrixGroups
namespace Atlas.G2.NaturalLongRootFixer
variable {F : Type*} [Field F] [CharP F 2]

private theorem fixed_basis_of_quotient (g : Model F) (i : Fin 8)
    (hi : i ≠ 3) (hi' : i ≠ 4)
    (hx : trace (basisVector i : Carrier F) = 0)
    (hq : Natural.action F g (Natural.mk F ⟨basisVector i, hx⟩) =
      Natural.mk F ⟨basisVector i, hx⟩) :
    g.val (basisVector i) = basisVector i := by
  change Natural.mk F (Natural.traceZeroAction F g ⟨basisVector i, hx⟩) =
    Natural.mk F ⟨basisVector i, hx⟩ at hq
  obtain ⟨r, hr⟩ := (Natural.mk_eq_mk_iff F _ _).mp hq
  change r • unit = g.val (basisVector i) - basisVector i at hr
  have hv : g.val (basisVector i) = r • unit + basisVector i :=
    (eq_sub_iff_add_eq.mp hr).symm
  have hn := automorphism_norm g (basisVector i)
  rw [hv] at hn
  have hr0 : r = 0 := by
    clear hv hr hq hx
    fin_cases i <;> simp_all [Atlas.SplitOctonion.norm, unit, basisVector]
  simpa [hr0] using hv

private theorem rootE_of_fixed_basis (g : Model F)
    (h0 : g.val (basisVector 0) = basisVector 0)
    (h7 : g.val (basisVector 7) = basisVector 7)
    (h5 : g.val (basisVector 5) = basisVector 5) : ∃ b : F, g = rootE b := by
  let p : PairStabilizer.fixingPair (F := F) := ⟨g,h0,h7⟩
  let M := PairStabilizer.imageSL p
  have hblock : PairStabilizer.blockHom M = g :=
    congrArg Subtype.val (PairStabilizer.block_imageSL p)
  have h00 : M.val 0 0 = 1 := by
    have h := congrFun h5 5
    rw [← hblock] at h
    simpa [PairStabilizer.blockHom, PairStabilizer.blockEquiv,
      PairStabilizer.blockLinear, basisVector] using h
  have h10 : M.val 1 0 = 0 := by
    have h := congrFun h5 6
    rw [← hblock] at h
    simpa [PairStabilizer.blockHom, PairStabilizer.blockEquiv,
      PairStabilizer.blockLinear, basisVector] using h
  have h11 : M.val 1 1 = 1 := by
    have hd : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using M.prop
    rw [h00,h10] at hd
    simpa using hd
  refine ⟨M.val 0 1, ?_⟩
  rw [← hblock]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [PairStabilizer.blockHom, PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear, rootE, Explicit.rootEEquiv,
    Explicit.rootELinear, Explicit.rootEApply, h00, h10, h11,
    sub_eq_add_neg, CharTwo.neg_eq]

private theorem rootA_of_fix_upperFour (g : Model F)
    (hf : ∀ v ∈ upperFour (F := F), action F g v = v) :
    ∃ a : F, g = rootA a := by
  have hfix (i : Fin 8) (hi : i=1 ∨ i=2 ∨ i=5) :
      g.val (basisVector i) = basisVector i := by
    have hx : trace (basisVector i : Carrier F) = 0 := by
      rcases hi with rfl | rfl | rfl <;> simp [trace,basisVector]
    apply fixed_basis_of_quotient g i (by rcases hi with rfl|rfl|rfl <;> decide)
      (by rcases hi with rfl|rfl|rfl <;> decide) hx
    apply (equiv F).injective
    change repEquiv F (Natural.action F g (Natural.mk F ⟨basisVector i,hx⟩)) = _
    rw [(repEquiv F).isIntertwining]
    apply hf
    change projection F ⟨basisVector i,hx⟩ ∈ upperFour
    rcases hi with rfl | rfl | rfl <;> simp [projection, upperFour,basisVector]
  let w : Model F := weylS * weylR
  have hw (i j : Fin 8) (hij : (i=2 ∧ j=0) ∨ (i=5 ∧ j=7) ∨ (i=1 ∧ j=5)) :
      w.val (basisVector i) = basisVector j := by
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      funext k <;> fin_cases k <;>
      simp [w, weylS,weylSEquiv,weylSLinear,weylSApply,
        weylR,weylREquiv,weylRLinear,weylRApply,basisVector,CharTwo.neg_eq]
  have hc (i j : Fin 8) (hi : i=1 ∨ i=2 ∨ i=5)
      (hij : w.val (basisVector i) = basisVector j) :
      (w * g * w⁻¹).val (basisVector j) = basisVector j := by
    rw [← hij]
    change w.val (g.val (w.val.symm (w.val (basisVector i)))) = w.val (basisVector i)
    rw [w.val.symm_apply_apply, hfix i hi]
  obtain ⟨a,ha⟩ := rootE_of_fixed_basis (w*g*w⁻¹)
    (hc 2 0 (by simp) (hw 2 0 (by simp)))
    (hc 5 7 (by simp) (hw 5 7 (by simp)))
    (hc 1 5 (by simp) (hw 1 5 (by simp)))
  refine ⟨a, ?_⟩
  have he : w⁻¹ * rootE a * w = rootA a := by
    apply Natural.action_injective F
    apply LinearMap.ext
    intro v
    apply (equiv F).injective
    change repEquiv F (Natural.action F _ v) = repEquiv F (Natural.action F _ v)
    rw [(repEquiv F).isIntertwining, (repEquiv F).isIntertwining]
    have hr : (weylR : Model F)⁻¹ = weylR := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using (weylR_sq (K:=F)))
    have hs : (weylS : Model F)⁻¹ = weylS := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using (weylS_sq (K:=F)))
    simp only [w, mul_inv_rev, hr, hs, map_mul, Module.End.mul_apply,
      action_weylR, action_weylS, action_rootE, action_rootA]
    ext i
    fin_cases i <;> simp
  rw [← he, ← ha]
  group

variable [Algebra (ZMod 2) F]

private theorem natural_fixed_iff (g : Model F) (v : Natural.Space F) :
    binaryNatural g v = v ↔ binaryAction g (equiv F v) = equiv F v := by
  have hc := (repEquiv F).isIntertwining g v
  change equiv F (Natural.action F g v) = action F g (equiv F v) at hc
  constructor
  · intro h
    change Natural.action F g v = v at h
    change action F g (equiv F v) = equiv F v
    rw [← hc,h]
  · intro h
    apply (equiv F).injective
    exact hc.trans h

/-- Fixing the fixed four-space of a nonzero long-root element pointwise
forces membership in that same one-parameter root group. -/
theorem pointwise_fixedSpace_rootA_iff (r : F) (hr : r ≠ 0) (g : Model F) :
    (∀ v ∈ fixedSpace (binaryNatural (F:=F)) (zpowers (rootA r)),
      binaryNatural g v = v) ↔ ∃ a : F, g = rootA a := by
  constructor
  · intro hf
    apply rootA_of_fix_upperFour g
    intro v hv
    have hfv : (equiv F).symm v ∈
        fixedSpace (binaryNatural (F:=F)) (zpowers (rootA r)) := by
      rw [mem_fixedSpace_zpowers_iff,natural_fixed_iff]
      change action F (rootA r) (equiv F ((equiv F).symm v)) = _
      rw [LinearEquiv.apply_symm_apply]
      exact (fixed_rootA_iff r hr v).mpr hv
    have h := (natural_fixed_iff g _).mp (hf _ hfv)
    change action F g (equiv F ((equiv F).symm v)) = _ at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  · rintro ⟨a,rfl⟩ v hv
    apply (natural_fixed_iff _ v).mpr
    rw [mem_fixedSpace_zpowers_iff,natural_fixed_iff] at hv
    obtain ⟨h4,h5⟩ := (fixed_rootA_iff r hr (equiv F v)).mp hv
    change coordinates F v 4 = 0 at h4
    change coordinates F v 5 = 0 at h5
    change action F (rootA a) (equiv F v) = equiv F v
    ext i
    fin_cases i <;> simp [h4,h5]

/-- The literal highest-root subgroup is the full pointwise fixer. -/
theorem subspaceKernel_fixedSpace_rootA (r : F) (hr : r ≠ 0) :
    subspaceKernel (binaryNatural (F:=F))
      (fixedSpace (binaryNatural (F:=F)) (zpowers (rootA r))) ⊤ =
      LieParabolicSetup.highestRoot := by
  ext g
  simp only [mem_subspaceKernel,mem_top, true_and,pointwise_fixedSpace_rootA_iff r hr]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨Multiplicative.ofAdd a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a.toAdd,rfl⟩

private theorem kernel_map_conj (ρ : Representation (ZMod 2) (Model F) (Natural.Space F))
    (A : Subgroup (Model F)) (c : Model F) :
    subspaceKernel ρ (fixedSpace ρ (A.map (MulAut.conj c).toMonoidHom)) ⊤ =
      (subspaceKernel ρ (fixedSpace ρ A) ⊤).map (MulAut.conj c).toMonoidHom := by
  have hf (v : Natural.Space F) (hv : v ∈ fixedSpace ρ A) :
      ρ c v ∈ fixedSpace ρ (A.map (MulAut.conj c).toMonoidHom) := by
    rintro ⟨_,a,ha,rfl⟩
    change ρ (c*a*c⁻¹) (ρ c v) = ρ c v
    have hav : ρ a v = v := hv ⟨a,ha⟩
    simp only [map_mul,Module.End.mul_apply,ρ.inv_self_apply,hav]
  have hb (w : Natural.Space F) (hw : w ∈ fixedSpace ρ (A.map (MulAut.conj c).toMonoidHom)) :
      ρ c⁻¹ w ∈ fixedSpace ρ A := by
    intro a
    change ρ a.val (ρ c⁻¹ w) = ρ c⁻¹ w
    have h := hw ⟨c*a.val*c⁻¹,⟨a.val,a.property,rfl⟩⟩
    change ρ (c*a.val*c⁻¹) w = w at h
    have h' := congrArg (ρ c⁻¹) h
    simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using h'
  apply le_antisymm
  · intro g hg
    refine ⟨c⁻¹*g*c,⟨Subgroup.mem_top _,?_⟩,?_⟩
    · intro v hv
      have h := congrArg (ρ c⁻¹) (hg.2 _ (hf v hv))
      simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using h
    · change c*(c⁻¹*g*c)*c⁻¹=g
      group
  · rintro _ ⟨g,hg,rfl⟩
    refine ⟨Subgroup.mem_top _,?_⟩
    intro w hw
    change ρ (c*g*c⁻¹) w = w
    simp only [map_mul,Module.End.mul_apply,hg.2 _ (hb w hw),ρ.self_inv_apply]

/-- Conjugation transports the actual fixer and the actual long-root embedding
simultaneously, retaining the marked root parameter. -/
theorem subspaceKernel_fixedSpace_longRoot (g : Model F) (r : F) (hr : r ≠ 0) :
    subspaceKernel (binaryNatural (F:=F))
      (fixedSpace (binaryNatural (F:=F)) (zpowers (MulAut.conj g (rootA r)))) ⊤ =
      (LieParabolicSetup.highestRoot (F:=F)).map (MulAut.conj g).toMonoidHom := by
  change subspaceKernel (binaryNatural (F:=F))
    (fixedSpace (binaryNatural (F:=F)) (zpowers ((MulAut.conj g).toMonoidHom (rootA r)))) ⊤ = _
  rw [← MonoidHom.map_zpowers,kernel_map_conj,subspaceKernel_fixedSpace_rootA r hr]

end Atlas.G2.NaturalLongRootFixer
