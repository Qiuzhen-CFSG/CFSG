module

public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.QuotientActions
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Graph-stable full-torus subgroups in scalar covers of PSL₃

The full diagonal torus contains the scalar center. A graph actor preserving
upper unipotent matrices and a subgroup of this torus normalizes that subgroup
by coordinate reversal: the triangular linear factor acts trivially there,
and the field factor is a uniform power map. Perfectness identifies the
explicit lifted actor in every scalar SL₃ quotient over the same PSL₃ marking.

Source: Aschbacher–Smith 4.4.13(1), pp.623–624; GLS3 §2.7.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.FullTorusGraphEscape
variable (F : Type*) [Field F]

theorem projection_kernel_le_torusSL : (projection F).ker ≤ (torusSL F).range := by
  intro x hx
  rw [projection_ker] at hx
  obtain ⟨r,hr,he⟩ := SpecialLinearGroup.mem_center_iff.mp hx
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have hr0 : r ≠ 0 := by intro hh; simp [hh] at hr3
  let u : Fˣ := Units.mk0 r hr0
  have hu3 : u ^ 3 = 1 := Units.ext hr3
  have hi : (u*u)⁻¹ = u := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hu3)
  refine ⟨(u,u),?_⟩
  apply Subtype.ext
  rw [← he,torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply,hi,u]

theorem torus_preimage_projection :
    (torus F).comap (projection F) = (torusSL F).range := by
  have hm : (torusSL F).range.map (projection F) = torus F := by
    rw [← MonoidHom.range_comp]
    rfl
  rw [← hm,comap_map_eq,sup_eq_left.mpr (projection_kernel_le_torusSL F)]

private theorem torusSL_unipotent_eq_one (x : SL(3,F))
    (hx : x ∈ (torusSL F).range) (hu : x ∈ unipotentSL F) : x = 1 := by
  obtain ⟨d,rfl⟩ := hx
  have h00 := ((mem_pointLocalSL_iff F _).mp hu.1).1
  have h22 := ((mem_lineLocalSL_iff F _).mp hu.2).2.2
  have hd : d = 1 := Prod.ext (Units.ext h00) (Units.ext h22)
  rw [hd,map_one]

variable [Finite F]

/-- Coefficient automorphisms preserve every subgroup of the full special torus. -/
theorem field_preserves_torus_subgroup (σ : F ≃+* F) (H : Subgroup SL(3,F))
    (hH : H ≤ (torusSL F).range) {x : SL(3,F)} (hx : x ∈ H) :
    Atlas.fieldEquivSL 3 σ x ∈ H := by
  obtain ⟨m,hm⟩ := (Units.map σ.toMonoidHom).map_cyclic
  obtain ⟨d,hd⟩ := hH hx
  have he : Atlas.fieldEquivSL 3 σ x = x ^ m := by
    rw [← hd,field_torusSL,← map_zpow]
    congr 1
    exact Prod.ext (hm d.1) (hm d.2)
  rw [he]
  exact H.zpow_mem hx m

variable [CharP F 2]

/-- A U-preserving linear factor cannot change a diagonal matrix when its
image is again diagonal. This equality holds before projectivization. -/
theorem linear_fixes_special_torus (m : GL (Fin 3) F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (x : SL(3,F)) (hx : x ∈ (torusSL F).range)
    (himage : linearConjSL F m x ∈ (torusSL F).range) : linearConjSL F m x = x := by
  obtain ⟨d,rfl⟩ := hx
  obtain ⟨u,hu,he⟩ := linearConjSL_torus_factor F m hm d
  have hut : u ∈ (torusSL F).range := by
    have hh := (torusSL F).range.mul_mem himage
      ((torusSL F).range.inv_mem ⟨d,rfl⟩)
    rwa [he,mul_inv_cancel_right] at hh
  rw [he,torusSL_unipotent_eq_one F u hut hu,one_mul]

omit [Finite F] in
theorem reversal_conjugation (x : SL(3,F)) :
    linearConjSL F (reversalGL F) x = reversalSL F * x * (reversalSL F)⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL,map_mul,map_mul,map_inv,reversalSL_toGL]

theorem reversal_not_mem_borel : projection F (reversalSL F) ∉ borel F := by
  intro hw
  have hb : reversalSL F ∈ borelSL F := by
    rw [← borel_comap]
    exact hw
  have h20 := ((mem_borelSL_iff F _).mp hb).2.1
  simp [reversalSL,reversalGL] at h20

/-- Stability under a standard graph actor gives an escaping Weyl normalizer
for the prescribed full-torus subgroup of SL₃. -/
theorem reversal_normalizes_of_graph_stable
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hU : (unipotent F).map (projectiveActor F m σ true).toMonoidHom = unipotent F)
    (H : Subgroup SL(3,F)) (hH : H ≤ (torusSL F).range)
    (hstable : ∀ x ∈ H, specialActor F m σ true x ∈ H) :
    reversalSL F ∈ normalizer (H : Set SL(3,F)) := by
  apply mem_normalizer_fintype
  intro x hx
  have hm := linear_part_unipotent F m σ true hU
  have hgraph : oppositionGraphSL F x ∈ (torusSL F).range := by
    obtain ⟨d,rfl⟩ := hH hx
    exact ⟨(d.2⁻¹,d.1⁻¹),(oppositionGraphSL_torusSL F d).symm⟩
  have hfield : Atlas.fieldEquivSL 3 σ (oppositionGraphSL F x) ∈ (torusSL F).range :=
    field_preserves_torus_subgroup F σ _ le_rfl hgraph
  have he : specialActor F m σ true x =
      Atlas.fieldEquivSL 3 σ (oppositionGraphSL F x) :=
    linear_fixes_special_torus F m hm _ hfield (hH (hstable x hx))
  have hh := field_preserves_torus_subgroup F σ.symm H hH (hstable x hx)
  rw [he] at hh
  have hinv : Atlas.fieldEquivSL 3 σ.symm
      (Atlas.fieldEquivSL 3 σ (oppositionGraphSL F x)) = oppositionGraphSL F x := by
    apply Subtype.ext
    ext i j
    simp [Atlas.fieldEquivSL,SpecialLinearGroup.map_apply_coe]
  rw [hinv] at hh
  have hg : oppositionGraphSL F x =
      (reversalSL F * x * (reversalSL F)⁻¹)⁻¹ := by
    obtain ⟨d,rfl⟩ := hH hx
    change linearConjSL F (reversalGL F) (graphSL F (torusSL F d)) = _
    simp only [graphSL_torusSL,map_inv,reversal_conjugation]
  exact H.inv_mem_iff.mp (hg ▸ hh)

variable {L : Type*} [Group L]

omit [Finite F] [CharP F 2] in
/-- Every quotient of SL₃ over its given projective map has central kernel. -/
theorem scalar_lift_kernel_central (r : L →* PSL(3,F)) (k : SL(3,F) →* L)
    (hk : Function.Surjective k) (hfac : r.comp k = projection F) : r.ker ≤ center L := by
  intro z hz
  obtain ⟨x,rfl⟩ := hk z
  have hx : x ∈ center SL(3,F) := by
    rw [← projection_ker,MonoidHom.mem_ker,← DFunLike.congr_fun hfac x]
    exact hz
  apply mem_center_iff.mpr
  intro y
  obtain ⟨v,rfl⟩ := hk y
  simpa only [map_mul] using congrArg k (mem_center_iff.mp hx v)

omit [Finite F] [CharP F 2] in
/-- The explicit standard action lifts uniquely through an actual scalar cover. -/
theorem scalar_actor_lift (r : L →* PSL(3,F)) (k : SL(3,F) →* L)
    (hk : Function.Surjective k) (hfac : r.comp k = projection F)
    (α : MulAut L) (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hcomm : ∀ x, r (α x) = projectiveActor F m σ ε (r x)) :
    α.toMonoidHom.comp k = k.comp (specialActor F m σ ε).toMonoidHom := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq r
    (scalar_lift_kernel_central F r k hk hfac)
  ext x
  change r (α (k x)) = r (k (specialActor F m σ ε x))
  have hp (y : SL(3,F)) : r (k y) = projection F y := DFunLike.congr_fun hfac y
  rw [hcomm,hp,hp]
  change _ = centerAction F (specialActor F m σ ε) (projection F x)
  rw [centerAction_specialActor]

/-- A diagram-moving actor preserving U and the prescribed torus subgroup
supplies an escaping normalizer in every actual scalar SL₃ cover. -/
theorem normalizer_escape_of_graph_stable [Finite L] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (r : L →* PSL(3,F)) (k : SL(3,F) →* L)
    (hk : Function.Surjective k) (hfac : r.comp k = projection F)
    (α : MulAut L) (β : MulAut PSL(3,F))
    (hcomm : ∀ x, r (α x) = β (r x))
    (hU : (unipotent F).map β.toMonoidHom = unipotent F)
    (hmove : β ∉ ExtensionBorel.linearField F)
    (A : Subgroup L) (hA : A ≤ (torus F).comap r)
    (hstable : A.map α.toMonoidHom = A) :
    ¬ normalizer (A : Set L) ≤ (borel F).comap r := by
  obtain ⟨m,σ,h | h⟩ := ResidualLinear.standard_opposition_factorization β (by
    rw [Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top F hn hF]
    trivial)
  · exact (hmove (h ▸ (ExtensionBorel.linearField F).mul_mem
      (mem_sup_left ⟨m,rfl⟩) (mem_sup_right ⟨σ,rfl⟩))).elim
  · have hβ : β = projectiveActor F m σ true := h
    have he := scalar_actor_lift F r k hk hfac α m σ true (fun x => by
      rw [hcomm,hβ])
    let H := A.comap k
    have hH : H ≤ (torusSL F).range := by
      have hh := comap_mono (f := k) hA
      rw [comap_comap,hfac,torus_preimage_projection] at hh
      exact hh
    have hHs : ∀ x ∈ H, specialActor F m σ true x ∈ H := by
      intro x hx
      change k (specialActor F m σ true x) ∈ A
      have hex : α (k x) = k (specialActor F m σ true x) := DFunLike.congr_fun he x
      rw [← hex]
      exact hstable.le (mem_map_of_mem _ hx)
    have hw := reversal_normalizes_of_graph_stable F m σ (hβ ▸ hU) H hH hHs
    have hwA := H.le_normalizer_map k (mem_map_of_mem k hw)
    rw [show H.map k = A from map_comap_eq_self_of_surjective hk A] at hwA
    intro hle
    have hh := hle hwA
    change r (k (reversalSL F)) ∈ borel F at hh
    have hp : r (k (reversalSL F)) = projection F (reversalSL F) :=
      DFunLike.congr_fun hfac _
    rw [hp] at hh
    exact reversal_not_mem_borel F hh

end Matrix.PSL3.FullTorusGraphEscape
