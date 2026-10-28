module
public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Containment
public import Theory.SpecificGroups.G2Even.TwoRank.Elementary

/-!
# Natural fixed spaces for the G₂ offender calculation

The short C root fixes exactly the upper three-space in the six-dimensional
natural quotient. The full A–B–C subgroup and the A–B plane have this same
fixed space. Within the actual short-root centralizer, fixing this space
pointwise removes the explicit SL₂ block, leaving precisely A–B–C elements.
These are coordinate statements about the existing octonion representation.

Source: Aschbacher–Smith B.4.6(3), (6), (11), (13), printed pp.88–90.
The root and block formulas are the attributed ATLAS ports already imported
by `NaturalCoordinates` and `CentralizerCore.Containment`.
-/

@[expose] public noncomputable section
namespace Atlas.G2.NaturalOffenders
open Representation Subgroup
open Restricted.NaturalCoordinates LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

/-- The upper totally singular three-space in the six natural coordinates. -/
def upper : Submodule F (Fin 6 → F) where
  carrier := {v | v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h3,h4,h5⟩ ⟨k3,k4,k5⟩; simp_all
  smul_mem' := by rintro c v ⟨h3,h4,h5⟩; simp_all

omit [CharP F 2] in
@[simp] theorem mem_upper (v : Fin 6 → F) : v ∈ upper ↔ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := Iff.rfl

def upperEquiv : upper (F:=F) ≃ₗ[F] (Fin 3 → F) where
  toFun v := ![v.val 0,v.val 1,v.val 2]
  invFun v := ⟨![v 0,v 1,v 2,0,0,0], by simp⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [v.prop.1,v.prop.2.1,v.prop.2.2]
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

omit [CharP F 2] in
theorem upper_finrank : Module.finrank F (upper (F:=F)) = 3 := by
  rw [upperEquiv.finrank_eq]
  simp

theorem fixed_rootC_iff (a : F) (ha : a ≠ 0) (v : Fin 6 → F) :
    action F (rootC a) v = v ↔ v ∈ upper := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [action_rootC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at h0 h1 h2
    refine ⟨?_,?_,?_⟩
    · exact (mul_eq_zero.mp (add_eq_left.mp h1)).resolve_left ha
    · exact (mul_eq_zero.mp (add_eq_left.mp h2)).resolve_left ha
    · exact (mul_eq_zero.mp (add_eq_left.mp h0)).resolve_left (pow_ne_zero _ ha)
  · rintro ⟨h3,h4,h5⟩
    ext i
    fin_cases i <;> simp [h3,h4,h5]

theorem rootA_fix_upper (a : F) {v : Fin 6 → F} (hv : v ∈ upper) : action F (rootA a) v = v := by
  ext i
  fin_cases i <;> simp [hv.1,hv.2.1,hv.2.2]

theorem rootB_fix_upper (a : F) {v : Fin 6 → F} (hv : v ∈ upper) : action F (rootB a) v = v := by
  ext i
  fin_cases i <;> simp [hv.1,hv.2.1,hv.2.2]

theorem rootC_fix_upper (a : F) {v : Fin 6 → F} (hv : v ∈ upper) : action F (rootC a) v = v := by
  ext i
  fin_cases i <;> simp [hv.1,hv.2.1,hv.2.2]

theorem elementary_fix_upper {g : Model F} (hg : g ∈ EvenTwoRank.elementary F)
    {v : Fin 6 → F} (hv : v ∈ upper) : action F g v = v := by
  obtain ⟨p,rfl⟩ := hg
  have he : EvenTwoRank.elementaryEmbedding F p =
      rootA (p.toAdd 0) * (rootB (p.toAdd 1) * rootC (p.toAdd 2)) := by
    simp [EvenTwoRank.elementaryEmbedding, EvenTwoRank.elementaryParameters, unipotentProduct,mul_assoc]
  rw [he,map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply,
    rootC_fix_upper _ hv,rootB_fix_upper _ hv,rootA_fix_upper _ hv]

omit [CharP F 2] in
theorem rootA_mem_elementary (a : F) : rootA a ∈ EvenTwoRank.elementary F :=
  ⟨Multiplicative.ofAdd ![a,0,0], by simp [EvenTwoRank.elementaryEmbedding,
    EvenTwoRank.elementaryParameters, unipotentProduct]⟩
omit [CharP F 2] in
theorem rootB_mem_elementary (a : F) : rootB a ∈ EvenTwoRank.elementary F :=
  ⟨Multiplicative.ofAdd ![0,a,0], by simp [EvenTwoRank.elementaryEmbedding,
    EvenTwoRank.elementaryParameters, unipotentProduct]⟩
omit [CharP F 2] in
theorem rootC_mem_elementary (a : F) : rootC a ∈ EvenTwoRank.elementary F :=
  ⟨Multiplicative.ofAdd ![0,0,a], by simp [EvenTwoRank.elementaryEmbedding,
    EvenTwoRank.elementaryParameters, unipotentProduct]⟩

theorem longRoot_fix_upper {g : Model F} (hg : g ∈ longRootLocal)
    {v : Fin 6 → F} (hv : v ∈ upper) : action F g v = v := by
  obtain ⟨p,rfl⟩ := hg
  change action F (rootA p.toAdd.1 * rootB p.toAdd.2) v = v
  rw [map_mul, Module.End.mul_apply, rootB_fix_upper _ hv, rootA_fix_upper _ hv]

theorem mem_upper_of_fixed_longRoots {v : Fin 6 → F}
    (ha : action F (rootA 1) v = v) (hb : action F (rootB 1) v = v) : v ∈ upper := by
  have h0 := congrFun hb 0
  have h1 := congrFun ha 0
  have h2 := congrFun ha 1
  simp only [action_rootA,action_rootB,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul] at h0 h1 h2
  exact ⟨add_eq_left.mp h0,add_eq_left.mp h1,add_eq_left.mp h2⟩

private theorem block_basis_one (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    action F (PairStabilizer.blockHom M) (Pi.single 1 1) = ![0,M.val 0 0,M.val 1 0,0,0,0] := by
  ext i
  fin_cases i <;> simp [action_apply,projection,representative,Natural.traceZeroAction_val,
    PairStabilizer.blockHom,PairStabilizer.blockEquiv,PairStabilizer.blockLinear,CharTwo.neg_eq]
private theorem block_basis_two (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    action F (PairStabilizer.blockHom M) (Pi.single 2 1) = ![0,M.val 0 1,M.val 1 1,0,0,0] := by
  ext i
  fin_cases i <;> simp [action_apply,projection,representative,Natural.traceZeroAction_val,
    PairStabilizer.blockHom,PairStabilizer.blockEquiv,PairStabilizer.blockLinear,CharTwo.neg_eq]

/-- In the short-root centralizer, fixing the natural three-space removes the SL₂ factor. -/
theorem mem_elementary_of_centralizes_of_fix_upper (a : F) (ha : a ≠ 0) {g : Model F}
    (hc : Commute g (rootC a)) (hf : ∀ v ∈ upper (F:=F), action F g v = v) :
    g ∈ EvenTwoRank.elementary F := by
  obtain ⟨p,t,M,hg⟩ := ShortRootProducts.CentralizerCore.centralizer_rootC_factor a ha
    (mem_centralizer_singleton_iff.mpr hc.eq)
  have h1 := hf (Pi.single 1 1) (by simp)
  have h2 := hf (Pi.single 2 1) (by simp)
  rw [hg] at h1 h2
  change action F (rootA p.toAdd.1 * rootB p.toAdd.2 * rootC t * PairStabilizer.blockHom M) _ = _ at h1 h2
  simp only [map_mul, Module.End.mul_apply, block_basis_one,block_basis_two] at h1 h2
  have hu1 : ![0,M.val 0 0,M.val 1 0,0,0,0] ∈ upper (F:=F) := by simp
  have hu2 : ![0,M.val 0 1,M.val 1 1,0,0,0] ∈ upper (F:=F) := by simp
  rw [rootC_fix_upper _ hu1,rootB_fix_upper _ hu1,rootA_fix_upper _ hu1] at h1
  rw [rootC_fix_upper _ hu2,rootB_fix_upper _ hu2,rootA_fix_upper _ hu2] at h2
  have hm : M = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using congrFun h1 1
    · simpa using congrFun h2 1
    · simpa using congrFun h1 2
    · simpa using congrFun h2 2
  rw [hg,hm,map_one,mul_one]
  exact (EvenTwoRank.elementary F).mul_mem
    ((EvenTwoRank.elementary F).mul_mem (rootA_mem_elementary _) (rootB_mem_elementary _))
    (rootC_mem_elementary _)

end Atlas.G2.NaturalOffenders
