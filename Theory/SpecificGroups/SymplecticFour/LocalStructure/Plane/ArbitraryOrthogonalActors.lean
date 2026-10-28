module
public import Theory.Representation.SymplecticFourOrthogonalCover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.OrthogonalActors
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
/-!
# Orthogonal actors fixing an arbitrary symplectic plane

A symplectic basis change transports every quadratic refinement to another
refinement in the same coefficient family. Isotropic-plane transitivity then
moves a pointwise-fixed self-orthogonal plane to the standard plane. Its
actors are the literal shear radical, so the explicit coefficient count
bounds their order by 2q. No standard-plane marking is a hypothesis.

Source: MS93 (3.3), printed p.867, the O4^epsilon(q) plane-actor comparison.
-/

public section
noncomputable section
open Matrix Representation.SymplecticFourOrthogonalCover
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem linear_square_expansion (l : Vector F →ₗ[F] F) (v : Vector F) :
    (l v)^2 = ∑ i, (l (Pi.single i 1))^2*v i^2 := by
  have hv : v = ∑ i, v i • Pi.single i 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  have hl : l v = ∑ i, v i*l (Pi.single i 1) := by
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul,smul_eq_mul]
  rw [hl,CharTwo.sum_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow,mul_comm]

/-- Symplectic coordinate changes retain the full family of quadratic refinements. -/
theorem refinement_comp_symplectic (c : Vector F) (g : Sp F) :
    ∃ d : Vector F, ∀ v, refinement c (g • v) = refinement d v := by
  let d : Vector F := fun i => (correction g (Pi.single i 1))^2+
    ∑ k, c k*(g.val k i)^2
  refine ⟨d,fun v => ?_⟩
  have hq (v : Vector F) : refinement c v = rowQuadratic v+∑ i,c i*v i^2 := by
    rw [refinement_apply]
    rfl
  have hq' (v : Vector F) : refinement d v = rowQuadratic v+∑ i,d i*v i^2 := by
    rw [refinement_apply]
    rfl
  rw [hq,hq']
  change rowQuadratic (g.val *ᵥ v)+_ = _
  rw [correction_square,add_assoc,linear_square_expansion]
  congr 1
  have hh (k) : (g • v) k^2 = ∑ i, (g.val k i)^2*v i^2 := by
    change (∑ i, g.val k i*v i)^2 = _
    rw [CharTwo.sum_sq]
    simp only [mul_pow]
  simp_rw [hh,Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [d]
  rw [add_mul,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc]

omit [Finite F] [CharP F 2] in
private theorem mem_radical_image_of_fixes_plane (g : Sp F)
    (hfix : ∀ v ∈ plane F, g • v = v) :
    ∃ h : g ∈ planeLocal, (⟨g,h⟩ : planeLocal (F := F)) ∈ radical := by
  have hA : g.val.toBlocks₁₁ = 1 := by
    ext i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inl i)
    simpa [smul_eq_mulVec,e,Matrix.mulVec_single,Matrix.toBlocks₁₁,Matrix.one_apply,Pi.single_apply] using h
  have hP : g ∈ planeParabolic := by
    rw [mem_planeParabolic_iff]
    intro i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inr i)
    simpa [smul_eq_mulVec,e,Matrix.mulVec_single] using h
  have hg : g ∈ planeLocal := (mem_local_iff g).mpr ⟨hP,by rw [hA]; exact Matrix.det_one⟩
  refine ⟨hg,?_⟩
  apply Subtype.ext
  exact hA

omit [Finite F] [CharP F 2] in
private def planeActor (A : Subgroup (Sp F))
    (hfix : ∀ g : A, ∀ v ∈ plane F, g.val • v=v) :
    A →* radical (F := F) where
  toFun g := ⟨⟨g.val,(mem_radical_image_of_fixes_plane g.val (hfix g)).choose⟩,
    (mem_radical_image_of_fixes_plane g.val (hfix g)).choose_spec⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl



/-- Pointwise standard-plane fixers are literal radical actors. -/
theorem card_le_of_fixes_standard_plane (A : Subgroup (Sp F))
    (hfix : ∀ g : A, ∀ v ∈ plane F, g.val • v=v)
    (c : Vector F) (hc : ∀ g : A, ∀ v, refinement c (g.val • v)=refinement c v) :
    Nat.card A ≤ 2*Nat.card F := by
  let δ := planeActor A hfix
  have hi : Function.Injective δ := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : radical (F := F) => z.val.val) h
  have hcard : Nat.card A = Nat.card δ.range :=
    Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
  rw [hcard]
  apply card_radical_subgroup_le δ.range c
  intro g v
  obtain ⟨z,hz⟩ := g.property
  rw [←hz]
  exact hc z v

/-- Orthogonal actors fixing any self-orthogonal plane have order at most 2q. -/
theorem card_le_of_fixes_self_orthogonal_plane (A : Subgroup (Sp F))
    (P : Submodule F (Vector F)) (hP : (form F).orthogonal P=P)
    (hfix : ∀ a : A, ∀ v ∈ P, a.val • v=v)
    (c : Vector F) (hc : ∀ a : A, ∀ v, refinement c (a.val • v)=refinement c v) :
    Nat.card A ≤ 2*Nat.card F := by
  have hd : Module.finrank F P=2 := by
    have h := LinearMap.BilinForm.finrank_orthogonal (W := P) TwoLocalCover.form_nondegenerate
    rw [hP] at h
    have hV : Module.finrank F (Vector F)=4 := by simp [Vector]
    rw [hV] at h
    omega
  have hne : P ≠ ⊥ := by
    intro he
    have hz : Module.finrank F P=0 := by rw [he]; exact finrank_bot F (Vector F)
    omega
  have hiso : ∀ x ∈ P, ∀ y ∈ P, form F x y=0 := by
    intro x hx y hy
    have hh : y ∈ (form F).orthogonal P := by rwa [hP]
    exact hh x hx
  obtain ⟨g,hg⟩ := TwoLocalCover.isotropic_subspace_conjugate_standard P hne hiso
  have hplane : P.map (toLinear g).toLinearMap=plane F := by
    rcases hg with hp | hp
    · have h := (toLinear g).finrank_map_eq P
      rw [hp,finrank_point,hd] at h
      omega
    · exact hp
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hcard : Nat.card A=Nat.card A' :=
    Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv
  obtain ⟨d,hdc⟩ := refinement_comp_symplectic c g⁻¹
  rw [hcard]
  apply card_le_of_fixes_standard_plane A' ?_ d ?_
  · rintro ⟨x,hx⟩ v hv
    obtain ⟨a,ha,rfl⟩ := hx
    rw [←hplane] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    change (g*a*g⁻¹) • (g • w) = g • w
    simp only [mul_smul,inv_smul_smul,hfix ⟨a,ha⟩ w hw]
  · rintro ⟨x,hx⟩ v
    obtain ⟨a,ha,rfl⟩ := hx
    rw [←hdc,←hdc]
    change refinement c (g⁻¹ • ((g*a*g⁻¹) • v)) = refinement c (g⁻¹ • v)
    simp only [mul_smul,inv_smul_smul]
    exact hc ⟨a,ha⟩ _

end Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
