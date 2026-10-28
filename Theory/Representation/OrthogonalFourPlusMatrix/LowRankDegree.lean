module
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic

/-!
# Rank two forces the determinant module's field degree

The scalar commutant reconstructs a coefficient-field automorphism for each
binary normalizer element. A nontrivial twist moves at least half the binary
matrix space. Rank two therefore forces field linearity when the field
degree is at least two. Scalar restriction makes this degree divide two,
so it equals two. The equivariant adapter retains the original normal
subgroup and rank-two element; `WholePairExclusion` is its source consumer.

Source: Aschbacher--Smith G.11.7, printed p.368.
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.LowRankDegree
open Module
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "V" => Mat (F := F)
local notation "action" => Representation.restrictScalars (k := ZMod 2) (representation (F := F))
/-- The actual determinant action as binary linear automorphisms. -/
@[expose] def linearAction : PairSL (F := F) →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    (Representation.restrictScalars (k := ZMod 2) (representation (F := F))).asGroupHom

private theorem normalizer_semilinear (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer ((linearAction (F := F)).range : Set (V ≃ₗ[ZMod 2] V))) :
    ∃ σ : F ≃+* F, ∀ (c : F) (M : V), t (c • M) = σ c • t M := by
  let q (c : F) : V →+ V :=
    { toFun := fun M => t (c • t.symm M)
      map_zero' := by simp
      map_add' := by intro M N; simp [smul_add] }
  have hq (c : F) : ∃ d : F, ∀ M, q c M = d • M := by
    apply centralizer_scalar
    intro g M
    have hg : linearAction g ∈ (linearAction (F := F)).range := ⟨g, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem ht) (linearAction g)).mp hg
    obtain ⟨h, hh⟩ := hmem
    have hh' : linearAction h = t⁻¹ * linearAction g * t := by simpa using hh
    have hi (N : V) : t.symm (action g N) = action h (t.symm N) := by
      have he := LinearEquiv.congr_fun hh' (t.symm N)
      change action h (t.symm N) = t.symm (action g (t (t.symm N))) at he
      simpa only [LinearEquiv.apply_symm_apply] using he.symm
    have he (N : V) : t (action h N) = action g (t N) := by
      apply t.symm.injective
      rw [LinearEquiv.symm_apply_apply, hi, LinearEquiv.symm_apply_apply]
    change t (c • t.symm (action g M)) = action g (t (c • t.symm M))
    have hsmul (N : V) : action h (c • N) = c • action h N :=
      (matrixAction h).map_smul c N
    rw [hi, ← hsmul, he]
  let φ : F → F := fun c => q c (Matrix.single 0 0 1) 0 0
  have hφ (c : F) (M : V) : q c M = φ c • M := by
    obtain ⟨d, hd⟩ := hq c
    have he : φ c = d := by simp [φ, hd, Matrix.single]
    exact he ▸ hd M
  have hmul (a b : F) (M : V) : q (a * b) M = q a (q b M) := by
    simp [q, mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ, q, Matrix.single]
      map_mul' := by
        intro a b
        change q (a * b) (Matrix.single 0 0 1) 0 0 = φ a * φ b
        rw [hmul, hφ, hφ]
        simp [Matrix.single]
      map_zero' := by simp [φ, q]
      map_add' := by intro a b; simp [φ, q, add_smul] }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective, Finite.surjective_of_injective φhom.injective⟩, fun c M => ?_⟩
  have he := hφ c (t M)
  change t (c • M) = φ c • t M
  simpa only [q, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.symm_apply_apply] using he

/-- A rank-two element of the actual binary determinant normalizer forces
coefficient-field degree two once that degree is greater than one. -/
theorem field_degree_eq_two (hn : 2≤finrank (ZMod 2) F)
    (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer ((linearAction (F := F)).range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id))=2) :
    finrank (ZMod 2) F=2 := by
  obtain ⟨σ,hσ⟩ := normalizer_semilinear t ht
  have hdim : finrank (ZMod 2) V=finrank (ZMod 2) F*4 := by
    have hv : finrank F V=4 := by
      change finrank F (Matrix (Fin 2) (Fin 2) F)=4
      rw [finrank_matrix]
      norm_num
    rw [←Module.finrank_mul_finrank (ZMod 2) F,hv]
  have hs (c : F) : σ c=c := by
    by_contra hc
    have hb := Representation.BinaryOffender.NaturalTensor.finrank_le_twice_operatorFixedCodim
      t.toLinearMap σ.toRingHom ⟨c,hc⟩ hσ
    change finrank (ZMod 2) V ≤ 2*finrank (ZMod 2)
      (LinearMap.range (t.toLinearMap-LinearMap.id)) at hb
    rw [hdim,hr] at hb
    omega
  let f : V →ₗ[F] V :=
    { toFun := t, map_add' := t.map_add,
      map_smul' := fun c M => by simpa only [hs,RingHom.id_apply] using hσ c M }
  let e := LinearEquiv.ofBijective f t.bijective
  have he : e.restrictScalars (ZMod 2)=t := by ext M; rfl
  have hd := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) e
  rw [he,hr] at hd
  have hpos : 0<finrank F (LinearMap.range (e.toLinearMap-LinearMap.id)) := by
    by_contra hh
    have hz : finrank F (LinearMap.range (e.toLinearMap-LinearMap.id))=0 := by omega
    rw [hz,mul_zero] at hd
    omega
  nlinarith
/-- The field bound on the original normal-subgroup action, with its actual
module coordinates and the original rank-two element retained. -/
theorem field_degree_eq_two_of_equivariant
    {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (N : Subgroup G) [N.Normal]
    (e : N ≃* PairSL (F := F)) (f : W ≃ₗ[ZMod 2] V)
    (hf : ∀ (n : N) (w : W), f (ρ n w)=action (e n) (f w))
    (hn : 2≤finrank (ZMod 2) F) (a : G)
    (hr : finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a)=2) :
    finrank (ZMod 2) F=2 := by
  let σ : Representation (ZMod 2) G V := f.conjRingEquiv.toMonoidHom.comp ρ
  let τ : G →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp σ.asGroupHom
  have ht (n : N) : τ n=linearAction (e n) := by
    apply LinearEquiv.ext
    intro M
    change f (ρ n (f.symm M))=action (e n) M
    rw [hf,f.apply_symm_apply]
  have himage : N.map τ=(linearAction (F := F)).range := by
    ext t
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨e ⟨n,hn⟩,(ht ⟨n,hn⟩).symm⟩
    · rintro ⟨g,rfl⟩
      refine ⟨e.symm g,(e.symm g).property,?_⟩
      rw [ht,e.apply_symm_apply]
  have hnorm : τ a ∈ Subgroup.normalizer ((linearAction (F := F)).range : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [←himage]
    apply Subgroup.le_normalizer_map τ
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.normalizer_eq_top]
    trivial
  have he (g : G) (w : W) : f (ρ g w)=σ g (f w) := by
    change f (ρ g w)=f (ρ g (f.symm (f w)))
    rw [f.symm_apply_apply]
  apply field_degree_eq_two hn (τ a) hnorm
  change finrank (ZMod 2) (Representation.RankTwo.movedSpace σ a)=2
  exact (Representation.RankTwo.finrank_movedSpace_transport ρ σ
    (MulEquiv.refl G) f he a).symm.trans hr
end ClassicalOrthogonal.FourPlusMatrix.LowRankDegree
