module

public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Theory.SpecificGroups.PSp4Three.Transvections
public import Theory.SpecificGroups.PSp4Three.Generation
public import Theory.AtlasPort.LinearAlgebra.LinearFunctionalFiber
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Projective symplectic geometry for the ternary rank-two group

The projective action has kernel exactly the center. Alternating-frame extension
identifies its three point-stabilizer orbits, and projectivization counts them.
These facts hold in arbitrary characteristic and will give the orbit sizes
1, 12, and 27 on the 40 points over the three-element field.

Adapted from Gerald Höhn, ATLAS, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
from `Atlas/LinearGroups/Symplectic/Center.lean`, `Atlas/LinearGroups/Symplectic/Projective.lean`, `Atlas/LinearGroups/Symplectic/ProjectiveGeneration.lean`, `Atlas/LinearAlgebra/AlternatingFrame.lean`, `Atlas/LinearGroups/Symplectic/OrthogonalFrame.lean`, `Atlas/LinearGroups/Symplectic/PointGeometry.lean`, `Atlas/LinearGroups/Symplectic/PointOrbits.lean`, `Atlas/LinearAlgebra/ProjectiveSubmodule.lean`, `Atlas/LinearGroups/Symplectic/PointCount.lean`.
Covered adaptations retain the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`; citation: `LICENSES/ATLAS-CITATION.cff`).
Changes: CFSG imports and module boundaries; local namespace to avoid
collisions with other ports; unused results outside this argument omitted.
-/

@[expose] public section

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

/-- Central commutation with genuine transvections forces preservation of every line. -/
theorem central_preserves_lines (g : Sp n F) (hg : g ∈ Subgroup.center (Sp n F))
    (v : Vector n F) (hv : v ≠ 0) : ∃ a : F, a • v = g • v := by
  have hgv : g • v ≠ 0 := by
    change toLinear g v ≠ 0
    exact (map_ne_zero_iff (toLinear g) (toLinear g).injective).mpr hv
  obtain ⟨x,hx⟩ := exists_form_left hgv 1
  have ht := transvection_conjugate g v 1
  rw [← Subgroup.mem_center_iff.mp hg (transvection v 1), mul_assoc,
    mul_inv_cancel, mul_one] at ht
  have h := congrArg (fun t : Sp n F => t • x) ht
  refine ⟨form x v, ?_⟩
  simpa [transvection_apply,hx] using h

/-- This scalar conclusion uses neither order nor transvection generation. -/
theorem central_is_scalar (g : Sp n F) (hg : g ∈ Subgroup.center (Sp n F)) :
    ∃ a : F, ∀ x : Vector n F, g • x = a • x := by
  obtain ⟨a,ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (fun v => by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        obtain ⟨a,ha⟩ := central_preserves_lines g hg v hv
        exact fun h => h a ha)
  refine ⟨a,fun x => ?_⟩
  exact congrArg (fun l : Vector n F →ₗ[F] Vector n F => l x) ha

theorem scalar_is_central (g : Sp n F) (a : F)
    (ha : ∀ x : Vector n F, g • x = a • x) : g ∈ Subgroup.center (Sp n F) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply ext_action
  intro x
  rw [mul_smul, mul_smul, ha, ha]
  exact (toLinear h).map_smul a x

end Matrix.PSp4Three
end

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

abbrev Points (n : ℕ) (F : Type*) [Field F] := ℙ F (Vector n F)

theorem fixes_points_iff_central (g : Sp n F) :
    (∀ p : Points n F, g • p = p) ↔ g ∈ Subgroup.center (Sp n F) := by
  constructor
  · intro hg
    obtain ⟨a,ha⟩ := (toLinear g).toLinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (fun v => by
        by_cases hv : v = 0
        · simp [hv,linearIndependent_fin2]
        · rw [LinearIndependent.pair_iff' hv]
          have h := hg (Projectivization.mk F v hv)
          rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
          obtain ⟨a,ha⟩ := h
          exact fun hli => hli a ha)
    apply scalar_is_central g a
    intro x
    exact congrArg (fun l : Vector n F →ₗ[F] Vector n F => l x) ha
  · intro hg p
    obtain ⟨a,ha⟩ := central_is_scalar g hg
    rw [← Projectivization.mk_rep p,Projectivization.smul_mk,Projectivization.mk_eq_mk_iff']
    exact ⟨a,(ha p.rep).symm⟩

def pointPerm : Sp n F →* Equiv.Perm (Points n F) := MulAction.toPermHom _ _

theorem pointPerm_kernel : (pointPerm (n := n) (F := F)).ker = Subgroup.center (Sp n F) := by
  ext g
  change pointPerm g = 1 ↔ _
  rw [Equiv.Perm.ext_iff]
  exact fixes_points_iff_central g

def projectivePerm : PSp n F →* Equiv.Perm (Points n F) :=
  QuotientGroup.lift _ pointPerm (by rw [pointPerm_kernel])

instance projectiveAction : MulAction (PSp n F) (Points n F) :=
  MulAction.compHom (Points n F) projectivePerm

@[simp] theorem projection_smul (g : Sp n F) (p : Points n F) :
    projection g • p = g • p := rfl

instance projective_faithful : FaithfulSMul (PSp n F) (Points n F) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  obtain ⟨h,rfl⟩ := projection_surjective g
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (fixes_points_iff_central h).mp hg

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

def projectiveTransvectionGroup (n : ℕ) (F : Type*) [Field F] : Subgroup (PSp n F) :=
  Subgroup.closure {g | ∃ (v : Vector n F) (a : F), g = projection (transvection v a)}

theorem projectiveTransvectionGroup_eq_top : projectiveTransvectionGroup n F = ⊤ := by
  have hle : transvectionGroup n F ≤ (projectiveTransvectionGroup n F).comap projection := by
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨v,a,rfl⟩
    exact Subgroup.subset_closure ⟨v,a,rfl⟩
  apply top_unique
  intro p _
  obtain ⟨g,rfl⟩ := projection_surjective p
  exact hle (mem_transvectionGroup n g)

/-- Projective transitivity comes from genuine transvections, without an order argument. -/
theorem exists_projective_send (p q : Points n F) :
    ∃ g : PSp n F, g • p = q := by
  obtain ⟨g,_,hg⟩ := exists_generated_send p.rep_nonzero q.rep_nonzero
  refine ⟨projection g,?_⟩
  rw [projection_smul,← Projectivization.mk_rep p, Projectivization.smul_mk]
  simpa only [hg] using Projectivization.mk_rep q

instance projective_pretransitive : MulAction.IsPretransitive (PSp n F) (Points n F) :=
  ⟨exists_projective_send⟩

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three.Frame
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V)

/-- Independent vectors have a partner dual to the first and orthogonal to the second. -/
theorem exists_dual_partner (hB : B.Nondegenerate) {u v : V} (hu : u ≠ 0)
    (hv : v ∉ Submodule.span F {u}) : ∃ f, B u f = 1 ∧ B v f = 0 := by
  obtain ⟨f,hf⟩ := exists_partner B hB hu
  obtain ⟨w,hw,hvw⟩ : ∃ w, B u w = 0 ∧ B v w ≠ 0 := by
    by_contra! h
    have he : v = (B v f) • u := by
      apply sub_eq_zero.mp
      apply hB.1
      intro x
      have hux : B u (x-(B u x) • f) = 0 := by simp [map_sub,map_smul,hf]
      have hvx := h (x-(B u x) • f) hux
      simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,
        smul_eq_mul] at hvx ⊢
      simpa only [mul_comm] using hvx
    apply hv
    rw [he]
    exact (Submodule.span F {u}).smul_mem _ (Submodule.subset_span (by simp))
  refine ⟨f-(B v f / B v w) • w, ?_, ?_⟩
  · simp [map_sub,map_smul,hw,hf]
  · simp [map_sub,map_smul,hvw]

/-- The first splitting can retain a second independent orthogonal vector in its complement. -/
theorem split_retaining_orthogonal (hA : B.IsAlt) (hB : B.Nondegenerate)
    {u v : V} (hu : u ≠ 0) (hv : v ∉ Submodule.span F {u}) (huv : B u v = 0) :
    ∃ f, B u f = 1 ∧ v ∈ complement B u f := by
  obtain ⟨f,hf,hvf⟩ := exists_dual_partner B hB hu hv
  refine ⟨f,hf,?_,hvf⟩
  change B v u = 0
  rw [← hA.neg_eq u v,huv,neg_zero]
end Matrix.PSp4Three.Frame
end

noncomputable section
namespace Matrix.PSp4Three
variable {F : Type*} [Field F]

@[simp] theorem headTail_e_succ {n : ℕ} (i : Fin n) :
    headTail n (e (F := F) i.succ) = ((0,0),e i) := by
  simp [headTail,e,Pi.single_apply]
  funext j
  cases j <;> simp [Pi.single_apply]

/-- Extend two independent orthogonal vectors to an actual alternating isometry. -/
theorem exists_isometry_orthogonal_pair {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (n : ℕ) (B : LinearMap.BilinForm F V)
    (hA : B.IsAlt) (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2*(n+2))
    (u v : V) (hu : u ≠ 0) (hv : v ∉ Submodule.span F {u}) (huv : B u v = 0) :
    ∃ g : B.IsometryEquiv (form (n := n+2) (F := F)),
      g u = e 0 ∧ g v = e 1 := by
  obtain ⟨f,huf,hvf⟩ := Matrix.PSp4Three.Frame.split_retaining_orthogonal B hA hB hu hv huv
  have hvu : B v u = 0 := hvf.1
  have hvf₂ : B v f = 0 := hvf.2
  let W := Matrix.PSp4Three.Frame.complement B u f
  let C := B.restrict W
  let vW : W := ⟨v,hvf⟩
  have hvW : vW ≠ 0 := by
    intro h
    have hv0 : v = 0 := congrArg Subtype.val h
    exact hv (hv0 ▸ (Submodule.span F {u}).zero_mem)
  have hC := Matrix.PSp4Three.Frame.complement_alternating B hA u f
  have hCN := Matrix.PSp4Three.Frame.complement_nondegenerate B hA u f huf hB
  have hW : Module.finrank F W = 2*(n+1) := by
    have h := Matrix.PSp4Three.Frame.finrank_complement B hA u f huf
    change Module.finrank F W + 2 = Module.finrank F V at h
    omega
  obtain ⟨w,hw⟩ := Matrix.PSp4Three.Frame.exists_partner C hCN hvW
  obtain ⟨k,hkv,_⟩ := exists_isometry_pair n C hC hCN hW vW w hw
  let s := Matrix.PSp4Three.Frame.split B hA u f huf
  let t : V ≃ₗ[F] Vector (n+2) F :=
    (s.trans ((LinearEquiv.refl F (F × F)).prodCongr k.toLinearEquiv)).trans
      (headTail (n+1)).symm
  have ht (z : V) : headTail (n+1) (t z) = ((s z).1,k (s z).2) := by simp [t]
  have htB : ∀ x y, form (t x) (t y) = B x y := by
    intro x y
    rw [form_headTail,ht,ht]
    have hk := k.map_app (s y).2 (s x).2
    change form (k (s x).2) (k (s y).2) = B (s x).2.val (s y).2.val at hk
    rw [hk]
    have hb := Matrix.PSp4Three.Frame.split_form B hA u f huf (s x) (s y)
    simpa only [s,LinearEquiv.symm_apply_apply] using hb.symm
  refine ⟨{ toLinearEquiv := t, map_app' := htB },?_,?_⟩
  · change t u = e 0
    apply (headTail (n+1)).injective
    rw [ht]
    have hs : s u = ((1,0),0) := by
      apply Prod.ext
      · simp [s,Matrix.PSp4Three.Frame.split,huf,hA.self_eq_zero]
      · apply Subtype.ext
        change u-Matrix.PSp4Three.Frame.planeProjection B u f u=0
        rw [Matrix.PSp4Three.Frame.projection_e B hA u f huf,sub_self]
    rw [hs]
    simp [headTail,e]
    rfl
  · change t v = e 1
    apply (headTail (n+1)).injective
    rw [ht]
    have hs : s v = ((0,0),vW) := by
      apply Prod.ext
      · change (B v f,-B v u)=(0,0)
        exact Prod.ext hvf₂ (by change -B v u = 0; rw [hvu,neg_zero])
      · apply Subtype.ext
        change v-Matrix.PSp4Three.Frame.planeProjection B u f v=v
        simp [Matrix.PSp4Three.Frame.planeProjection,hvu,hvf₂]
    rw [hs,hkv]
    exact (headTail_e_succ (F := F) (n := n+1) 0).symm

end Matrix.PSp4Three
end

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

/-- Orthogonality of actual projective lines in the retained alternating form. -/
def Orthogonal (p q : Points n F) : Prop := form p.rep q.rep = 0

theorem orthogonal_mk {x y : Vector n F} (hx : x ≠ 0) (hy : y ≠ 0) :
    Orthogonal (Projectivization.mk F x hx) (Projectivization.mk F y hy) ↔ form x y = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F x hx
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep F y hy
  unfold Orthogonal
  rw [← ha,← hb]
  simp [Units.smul_def,map_smul]

@[simp] theorem orthogonal_self (p : Points n F) : Orthogonal p p := form_self _

theorem orthogonal_symm {p q : Points n F} (h : Orthogonal p q) : Orthogonal q p := by
  unfold Orthogonal at *
  rw [form_swap,h,neg_zero]

theorem orthogonal_smul (g : Sp n F) (p q : Points n F) :
    Orthogonal (g • p) (g • q) ↔ Orthogonal p q := by
  rw [← Projectivization.mk_rep p,← Projectivization.mk_rep q,
    Projectivization.smul_mk,Projectivization.smul_mk,orthogonal_mk,orthogonal_mk]
  simp only [smul_eq_mulVec,preserves]

theorem projective_orthogonal_smul (g : PSp n F) (p q : Points n F) :
    Orthogonal (g • p) (g • q) ↔ Orthogonal p q := by
  obtain ⟨g,rfl⟩ := projection_surjective g
  exact orthogonal_smul g p q

theorem e_nonzero (i : Fin n) : e (F := F) i ≠ 0 := by
  intro h
  have := congrFun h (.inl i)
  simp [e] at this

theorem f_nonzero (i : Fin n) : f (F := F) i ≠ 0 := by
  intro h
  have := congrFun h (.inr i)
  simp [f] at this

def ePoint (i : Fin n) : Points n F := Projectivization.mk F (e i) (e_nonzero i)
def fPoint (i : Fin n) : Points n F := Projectivization.mk F (f i) (f_nonzero i)

/-- Normalize two distinct orthogonal lines using actual partial-frame extension. -/
theorem normalize_orthogonal_pair (n : ℕ) (p q : Points (n+2) F)
    (hpq : p ≠ q) (ho : Orthogonal p q) :
    ∃ g : Sp (n+2) F, g • p = ePoint 0 ∧ g • q = ePoint 1 := by
  have hq : q.rep ∉ Submodule.span F {p.rep} := by
    intro h
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h
    apply hpq
    rw [← Projectivization.mk_rep p,← Projectivization.mk_rep q]
    apply Eq.symm
    exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨a,ha⟩
  obtain ⟨k,hkp,hkq⟩ := exists_isometry_orthogonal_pair n (form (n := n+2) (F := F)) form_alternating
    form_nondegenerate (by simp [Vector,Index,two_mul])
    p.rep q.rep p.rep_nonzero hq ho
  refine ⟨ofLinear k.toLinearEquiv k.map_app',?_,?_⟩
  · rw [← Projectivization.mk_rep p,Projectivization.smul_mk]
    simp only [ofLinear_apply,ePoint]
    change Projectivization.mk F (k p.rep) _ = _
    simp only [hkp]
  · rw [← Projectivization.mk_rep q,Projectivization.smul_mk]
    simp only [ofLinear_apply,ePoint]
    change Projectivization.mk F (k q.rep) _ = _
    simp only [hkq]

/-- Normalize a nonorthogonal pair without using a group order or generation premise. -/
theorem normalize_nonorthogonal_pair (n : ℕ) (p q : Points (n+1) F)
    (ho : ¬ Orthogonal p q) :
    ∃ g : Sp (n+1) F, g • p = ePoint 0 ∧ g • q = fPoint 0 := by
  have hc : form p.rep q.rep ≠ 0 := ho
  let v := (form p.rep q.rep)⁻¹ • q.rep
  have hv : v ≠ 0 := smul_ne_zero (inv_ne_zero hc) q.rep_nonzero
  have hpv : form p.rep v = 1 := by simp [v,map_smul,hc]
  have hqv : q = Projectivization.mk F v hv := by
    rw [← Projectivization.mk_rep q]
    apply Eq.symm
    exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨_,rfl⟩
  obtain ⟨k,hkp,hkv⟩ := exists_isometry_pair n form form_alternating
    form_nondegenerate (by simp [Vector,Index,two_mul]) p.rep v hpv
  refine ⟨ofLinear k.toLinearEquiv k.map_app',?_,?_⟩
  · rw [← Projectivization.mk_rep p,Projectivization.smul_mk]
    simp only [ofLinear_apply,ePoint]
    change Projectivization.mk F (k p.rep) _ = _
    simp only [hkp]
  · rw [hqv,Projectivization.smul_mk]
    simp only [ofLinear_apply,fPoint]
    change Projectivization.mk F (k v) _ = _
    simp only [hkv]

end Matrix.PSp4Three
end

noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F]

/-- Orthogonal lines other than the base line form a full point-stabilizer orbit. -/
theorem orthogonal_stabilizer_transitive (n : ℕ) (p x y : Points (n+2) F)
    (hx : p ≠ x) (hy : p ≠ y) (hox : Orthogonal p x) (hoy : Orthogonal p y) :
    ∃ g : MulAction.stabilizer (PSp (n+2) F) p, g • x = y := by
  obtain ⟨a,hap,hax⟩ := normalize_orthogonal_pair n p x hx hox
  obtain ⟨b,hbp,hby⟩ := normalize_orthogonal_pair n p y hy hoy
  have hp : (b⁻¹*a) • p = p := by rw [mul_smul,hap,← hbp,inv_smul_smul]
  have hxy : (b⁻¹*a) • x = y := by rw [mul_smul,hax,← hby,inv_smul_smul]
  exact ⟨⟨projection (b⁻¹*a),hp⟩,hxy⟩

/-- Nonorthogonal lines form the other full point-stabilizer orbit. -/
theorem nonorthogonal_stabilizer_transitive (n : ℕ) (p x y : Points (n+1) F)
    (hox : ¬ Orthogonal p x) (hoy : ¬ Orthogonal p y) :
    ∃ g : MulAction.stabilizer (PSp (n+1) F) p, g • x = y := by
  obtain ⟨a,hap,hax⟩ := normalize_nonorthogonal_pair n p x hox
  obtain ⟨b,hbp,hby⟩ := normalize_nonorthogonal_pair n p y hoy
  have hp : (b⁻¹*a) • p = p := by rw [mul_smul,hap,← hbp,inv_smul_smul]
  have hxy : (b⁻¹*a) • x = y := by rw [mul_smul,hax,← hby,inv_smul_smul]
  exact ⟨⟨projection (b⁻¹*a),hp⟩,hxy⟩

/-- The three geometric classes are the base line, its punctured perp, and its complement. -/
def suborbitIndex (p x : Points n F) : Fin 3 := by
  classical
  exact if x=p then 0 else if Orthogonal p x then 1 else 2

@[simp] theorem suborbitIndex_self (p : Points n F) : suborbitIndex p p = 0 := by
  simp [suborbitIndex]

theorem suborbitIndex_invariant (p x : Points n F)
    (g : MulAction.stabilizer (PSp n F) p) : suborbitIndex p (g • x) = suborbitIndex p x := by
  classical
  have hgp : g.val • p = p := g.prop
  have he : g.val • x = p ↔ x=p := by
    simpa only [hgp] using (show g.val • x = g.val • p ↔ x=p from smul_left_cancel_iff g.val)
  have ho : Orthogonal p (g.val • x) ↔ Orthogonal p x := by
    simpa only [hgp] using projective_orthogonal_smul g.val p x
  change suborbitIndex p (g.val • x) = _
  simp only [suborbitIndex,he,ho]

theorem suborbitIndex_transitive (hn : 2 ≤ n) (p x y : Points n F)
    (h : suborbitIndex p x = suborbitIndex p y) :
    ∃ g : MulAction.stabilizer (PSp n F) p, g • x = y := by
  classical
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  by_cases hx : x=p
  · have hy : y=p := by
      by_contra hy
      by_cases hoy : Orthogonal p y <;> simp [suborbitIndex,hx,hy,hoy] at h
    subst x; subst y
    exact ⟨1,one_smul _ _⟩
  · by_cases hy : y=p
    · by_cases hox : Orthogonal p x <;> simp [suborbitIndex,hx,hy,hox] at h
    · by_cases hox : Orthogonal p x
      · by_cases hoy : Orthogonal p y
        · exact orthogonal_stabilizer_transitive k p x y (Ne.symm hx) (Ne.symm hy) hox hoy
        · simp [suborbitIndex,hx,hy,hox,hoy] at h
      · by_cases hoy : Orthogonal p y
        · simp [suborbitIndex,hx,hy,hox,hoy] at h
        · exact nonorthogonal_stabilizer_transitive (k+1) p x y hox hoy

/-- Equality of the geometric classes is exactly equality of point-stabilizer orbits. -/
theorem stabilizer_orbit_iff (hn : 2 ≤ n) (p x y : Points n F) :
    y ∈ MulAction.orbit (MulAction.stabilizer (PSp n F) p) x ↔
      suborbitIndex p x = suborbitIndex p y := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (suborbitIndex_invariant p x g).symm
  · exact suborbitIndex_transitive hn p x y

end Matrix.PSp4Three
end

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Matrix.PSp4Three
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Inclusion of a genuine linear subspace identifies exactly its projective points. -/
def projectiveSubmoduleEquiv (W : Submodule F V) :
    (ℙ F W) ≃ {p : ℙ F V // p.rep ∈ W} := by
  let m := Projectivization.map W.subtype W.subtype_injective
  have hm (p : ℙ F W) : (m p).rep ∈ W := by
    induction p using Projectivization.ind with
    | h v hv =>
      change (Projectivization.mk F v.val (W.subtype_injective.ne hv)).rep ∈ W
      obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep F v.val (W.subtype_injective.ne hv)
      rw [← ha]
      exact W.smul_mem a.val v.prop
  refine Equiv.ofBijective (fun p => ⟨m p,hm p⟩) ⟨?_,?_⟩
  · intro p q h
    exact Projectivization.map_injective W.subtype W.subtype_injective (congrArg Subtype.val h)
  · intro p
    let v : W := ⟨p.val.rep,p.prop⟩
    have hv : v ≠ 0 := by intro h; exact p.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk F v hv,?_⟩
    apply Subtype.ext
    change Projectivization.mk F p.val.rep _ = p.val
    exact Projectivization.mk_rep p.val

end Matrix.PSp4Three
end

noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Matrix.PSp4Three
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- Cardinality of the actual projective point set, independently of group order. -/
theorem card_points : Nat.card (Points n F) = (Nat.card F^(2*n)-1)/(Nat.card F-1) := by
  rw [Projectivization.card'',Module.natCard_eq_pow_finrank (K := F)]
  simp [Vector,Index,two_mul]

/-- The entire perp is the projectivization of an actual hyperplane kernel. -/
def perpendicularPointsEquiv (p : Points n F) :
    (ℙ F (form p.rep).ker) ≃ {q : Points n F // Orthogonal p q} :=
  Matrix.PSp4Three.projectiveSubmoduleEquiv (form p.rep).ker

theorem card_perpendicular_points (p : Points n F) :
    Nat.card {q : Points n F // Orthogonal p q} =
      (Nat.card F^(2*n-1)-1)/(Nat.card F-1) := by
  rw [← Nat.card_congr (perpendicularPointsEquiv p),Projectivization.card'']
  obtain ⟨v,hv⟩ := Matrix.PSp4Three.Frame.exists_partner form form_nondegenerate p.rep_nonzero
  have hk : Nat.card (form p.rep).ker = Nat.card F^(2*n-1) := by
    change Nat.card {x : Vector n F // form p.rep x=0} = _
    have h := Atlas.LinearFunctional.card_fiber (form p.rep) v hv 0
    simpa [Vector,Index,two_mul] using h
  rw [hk]

omit [Finite F] in
theorem card_suborbit_zero (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=0} = 1 := by
  classical
  have he : {q : Points n F | suborbitIndex p q=0} = {p} := by
    ext q
    by_cases hq : q=p <;> by_cases ho : Orthogonal p q <;> simp [suborbitIndex,hq,ho]
  calc
    _ = Nat.card ↥({p} : Set (Points n F)) := Nat.card_congr (Equiv.setCongr he)
    _ = 1 := by simp

omit [Finite F] in
theorem suborbitIndex_eq_one_iff (p q : Points n F) :
    suborbitIndex p q=1 ↔ Orthogonal p q ∧ q ≠ p := by
  classical
  by_cases hq : q=p <;> by_cases ho : Orthogonal p q <;> simp [suborbitIndex,hq,ho]

omit [Finite F] in
theorem suborbitIndex_eq_two_iff (p q : Points n F) :
    suborbitIndex p q=2 ↔ ¬ Orthogonal p q := by
  classical
  by_cases hq : q=p
  · subst q; simp
  · by_cases ho : Orthogonal p q <;> simp [suborbitIndex,hq,ho]

theorem card_suborbit_one (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=1} =
      Nat.card {q : Points n F // Orthogonal p q} - 1 := by
  classical
  let a : {q : Points n F // Orthogonal p q} := ⟨p,orthogonal_self p⟩
  let eqv : {q : Points n F // suborbitIndex p q=1} ≃
      {q : {q : Points n F // Orthogonal p q} // q ≠ a} :=
    { toFun := fun q => ⟨⟨q.val,((suborbitIndex_eq_one_iff p q.val).mp q.prop).1⟩,
        fun h => ((suborbitIndex_eq_one_iff p q.val).mp q.prop).2 (congrArg Subtype.val h)⟩
      invFun := fun q => ⟨q.val.val,(suborbitIndex_eq_one_iff p q.val.val).mpr
        ⟨q.val.prop,fun h => q.prop (Subtype.ext h)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let := Fintype.ofFinite {q : Points n F // Orthogonal p q}
  have hu : Fintype.card {x : {q : Points n F // Orthogonal p q} // x=a} = 1 :=
    Fintype.card_unique
  rw [Nat.card_congr eqv,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    hu,Nat.card_eq_fintype_card]

theorem card_suborbit_two (p : Points n F) :
    Nat.card {q : Points n F // suborbitIndex p q=2} =
      Nat.card (Points n F) - Nat.card {q : Points n F // Orthogonal p q} := by
  classical
  let := Fintype.ofFinite (Points n F)
  let eqv := Equiv.subtypeEquivRight (suborbitIndex_eq_two_iff p)
  rw [Nat.card_congr eqv,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]

end Matrix.PSp4Three
end
