module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The graph centralizer in the unitary-four extension

The fixed matrices of entrywise Hermitian conjugation descend to the stored
fixed field. Reordering the hyperbolic basis identifies their defining form
with the standard symplectic form. This constructs an actual isomorphism
Sp₄(Fix(σ)) ≃ C_SU₄(σ), preserving the point and plane parabolics. In the
actual degree-two extension the entire centralizer is Sp₄(Fix(σ)) × C₂;
the second factor is the original graph involution.

This is the native graph-fixed group and local marking in Aschbacher–Smith
F.4.37(1–3), printed p.293 of `refs/quasithin.pdf`. No ambient centralizer
Sylow placement, outer transfer or full-normalizer realization is asserted.
The calculation retains every finite characteristic-two field, including q=4.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
open UnitaryFourFlag UnitaryFourOuter
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "U" => SU F (form F σ hσ)
local notation "Sp" => Theory.SpecificGroups.SymplecticFour.Sp K

@[expose] def coordinates : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  invFun := Sum.elim ![0,1] ![3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by rcases i with i | i <;> fin_cases i <;> rfl

private def matrixMap : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K →+*
    Matrix (Fin 4) (Fin 4) F :=
  (Matrix.reindexRingEquiv F coordinates.symm).toRingHom.comp
    ((FixedBy.subfield F σ).subtype.mapMatrix)

omit [CharP F 2] in
private theorem matrixMap_apply (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (i j : Fin 4) : matrixMap F σ A i j = (A (coordinates i) (coordinates j) : F) := by rfl

omit [CharP F 2] in
private theorem matrixMap_injective : Function.Injective (matrixMap F σ) := by
  intro A B h
  ext i j
  simpa only [matrixMap_apply, Equiv.apply_symm_apply] using
    congrArg (fun M => M (coordinates.symm i) (coordinates.symm j)) h

omit [CharP F 2] in
private theorem matrixMap_transpose (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    matrixMap F σ A.transpose = (matrixMap F σ A).transpose := by rfl

private theorem matrixMap_form : matrixMap F σ (Matrix.J (Fin 2) K) = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMap_apply, coordinates, Matrix.J, Matrix.fromBlocks, gram, CharTwo.neg_eq]

omit [CharP F 2] in
private theorem matrixMap_fixed (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (matrixMap F σ A).map σ = matrixMap F σ A := by
  ext i j
  exact (A (coordinates i) (coordinates j)).property

private def linearMap : Sp →* GL (Fin 4) F where
  toFun g := ⟨matrixMap F σ g.val, matrixMap F σ (g⁻¹).val,
    by rw [←map_mul]; exact (congrArg (matrixMap F σ) (congrArg Subtype.val (mul_inv_cancel g))).trans (map_one _),
    by rw [←map_mul]; exact (congrArg (matrixMap F σ) (congrArg Subtype.val (inv_mul_cancel g))).trans (map_one _)⟩
  map_one' := Units.ext (map_one _)
  map_mul' g h := Units.ext (map_mul _ _ _)

private theorem linearMap_unitary (g : Sp) :
    linearMap F σ g ∈ (form F σ hσ).specialSubgroup := by
  constructor
  · have he := congrArg (matrixMap F σ) (SymplecticGroup.mem_iff'.mp g.property)
    rw [map_mul,map_mul,matrixMap_form,matrixMap_transpose] at he
    change (form F σ hσ).conjTranspose (matrixMap F σ g.val) * gram F *
      matrixMap F σ g.val = gram F
    have hc : (form F σ hσ).conjTranspose (matrixMap F σ g.val) =
        (matrixMap F σ g.val).transpose := by
      exact congrArg Matrix.transpose (matrixMap_fixed F σ g.val)
    rw [hc]
    exact he
  · apply Units.ext
    change (matrixMap F σ g.val).det = 1
    change ((g.val.map (FixedBy.subfield F σ).subtype).submatrix coordinates coordinates).det = 1
    rw [Matrix.det_submatrix_equiv_self]
    change ((FixedBy.subfield F σ).subtype.mapMatrix g.val).det = 1
    rw [←RingHom.map_det, SymplecticGroup.det_eq_one g.property, map_one]

/-- The fixed-field symplectic group in the original unitary matrix coordinates. -/
def embedding : Sp →* U :=
  (linearMap F σ).codRestrict _ (linearMap_unitary F σ hσ)

theorem embedding_apply (g : Sp) (i j : Fin 4) :
    (embedding F σ hσ g).val.val i j = (g.val (coordinates i) (coordinates j) : F) := by rfl

theorem embedding_injective : Function.Injective (embedding F σ hσ) := by
  intro g h he
  apply Subtype.ext
  exact matrixMap_injective F σ (congrArg (fun u : U => u.val.val) he)

theorem embedding_fixed (g : Sp) : matrixAut F σ hσ (embedding F σ hσ g) =
    embedding F σ hσ g := by
  apply Subtype.ext
  apply Units.ext
  exact matrixMap_fixed F σ g.val

omit [CharP F 2] in
/-- Fixedness under the actual graph automorphism is entrywise descent. -/
theorem fixed_iff_entries (g : U) : matrixAut F σ hσ g = g ↔
    ∀ i j, σ (g.val.val i j) = g.val.val i j := by
  constructor
  · intro h i j
    exact congrArg (fun u : U => u.val.val i j) h
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact funext fun i => funext fun j => h i j

private def descendedMatrix (g : U) (hg : matrixAut F σ hσ g = g) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fun i j => ⟨g.val.val (coordinates.symm i) (coordinates.symm j),
    (fixed_iff_entries F σ hσ g).mp hg _ _⟩

omit [CharP F 2] in
private theorem matrixMap_descended (g : U) (hg : matrixAut F σ hσ g = g) :
    matrixMap F σ (descendedMatrix F σ hσ g hg) = g.val.val := by
  ext i j
  simp only [matrixMap_apply, descendedMatrix, Equiv.symm_apply_apply]

private theorem descended_symplectic (g : U) (hg : matrixAut F σ hσ g = g) :
    descendedMatrix F σ hσ g hg ∈ Matrix.symplecticGroup (Fin 2) K := by
  apply SymplecticGroup.mem_iff'.mpr
  apply matrixMap_injective F σ
  rw [map_mul,map_mul,matrixMap_form,matrixMap_transpose,matrixMap_descended]
  have hc : (form F σ hσ).conjTranspose g.val.val = g.val.val.transpose := by
    ext i j
    exact (fixed_iff_entries F σ hσ g).mp hg j i
  rw [←hc]
  exact g.property.1

/-- The graph fixed subgroup is exactly Sp₄ over the fixed field, including q=4. -/
def fixedEquiv : Sp ≃* (matrixAut F σ hσ).fixedSubgroup :=
  MulEquiv.ofBijective ((embedding F σ hσ).codRestrict _ (fun g => (MulAut.mem_fixedSubgroup _ _).mpr (embedding_fixed F σ hσ g)))
    ⟨fun a b h => embedding_injective F σ hσ (congrArg Subtype.val h), by
      intro g
      refine ⟨⟨descendedMatrix F σ hσ g.val ((MulAut.mem_fixedSubgroup _ _).mp g.property),
        descended_symplectic F σ hσ g.val ((MulAut.mem_fixedSubgroup _ _).mp g.property)⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      exact matrixMap_descended F σ hσ g.val ((MulAut.mem_fixedSubgroup _ _).mp g.property)⟩


/-- The embedding retains the native point parabolic. -/
theorem embedding_mem_point [Finite F] (g : Sp) :
    embedding F σ hσ g ∈ pointParabolicSU F (form F σ hσ) ↔
      g ∈ Theory.SpecificGroups.SymplecticFour.pointParabolic := by
  rw [mem_pointParabolicSU, Theory.SpecificGroups.SymplecticFour.mem_pointParabolic_iff]
  simp only [embedding_apply, coordinates]
  constructor
  · rintro ⟨h1,h2,h3⟩
    refine ⟨Subtype.ext h1, fun i => ?_⟩
    fin_cases i
    · exact Subtype.ext h3
    · exact Subtype.ext h2
  · rintro ⟨h1,h2⟩
    exact ⟨congrArg Subtype.val h1, congrArg Subtype.val (h2 1),
      congrArg Subtype.val (h2 0)⟩

/-- The same coordinate map retains the native plane parabolic. -/
theorem embedding_mem_plane [Finite F] (g : Sp) :
    embedding F σ hσ g ∈ planeParabolicSU F (form F σ hσ) ↔
      g ∈ Theory.SpecificGroups.SymplecticFour.planeParabolic := by
  rw [mem_planeParabolicSU, Theory.SpecificGroups.SymplecticFour.mem_planeParabolic_iff]
  simp only [embedding_apply, coordinates]
  constructor
  · rintro ⟨h20,h30,h21,h31⟩ i j
    fin_cases i <;> fin_cases j
    · exact Subtype.ext h30
    · exact Subtype.ext h31
    · exact Subtype.ext h20
    · exact Subtype.ext h21
  · intro h
    exact ⟨congrArg Subtype.val (h 1 0), congrArg Subtype.val (h 0 0),
      congrArg Subtype.val (h 1 1), congrArg Subtype.val (h 0 1)⟩

private theorem action_embedding (c : C2) (g : Sp) :
    action F σ hσ c (embedding F σ hσ g) = embedding F σ hσ g := by
  rcases c2_cases c with rfl | rfl
  · exact DFunLike.congr_fun (map_one (action F σ hσ)) _
  · rw [action_generator, embedding_fixed]

/-- The graph centralizer embedding includes its central graph factor. -/
def centralizerHom : Sp × C2 →* Extension F σ hσ where
  toFun x := ⟨embedding F σ hσ x.1,x.2⟩
  map_one' := SemidirectProduct.ext (map_one _) rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change embedding F σ hσ (x.1*y.1) =
        embedding F σ hσ x.1 * action F σ hσ x.2 (embedding F σ hσ y.1)
      rw [action_embedding,map_mul]
    · rfl

theorem centralizerHom_left (x : Sp × C2) :
    (centralizerHom F σ hσ x).left = embedding F σ hσ x.1 := by rfl

theorem centralizerHom_right (x : Sp × C2) :
    (centralizerHom F σ hσ x).right = x.2 := by rfl

theorem centralizerHom_injective : Function.Injective (centralizerHom F σ hσ) := by
  intro x y h
  exact Prod.ext (embedding_injective F σ hσ (congrArg SemidirectProduct.left h))
    (congrArg SemidirectProduct.right h)

omit [CharP F 2] in
/-- The full extension centralizer is cut out by the original graph fixed equation. -/
theorem mem_graph_centralizer (x : Extension F σ hσ) :
    x ∈ centralizer ({sigma F σ hσ} : Set (Extension F σ hσ)) ↔
      matrixAut F σ hσ x.left = x.left := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro he
    have hh := congrArg SemidirectProduct.left he
    simpa only [sigma, SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, action_generator, one_mul, map_one, mul_one] using hh.symm
  · intro he
    apply SemidirectProduct.ext
    · simpa only [sigma, SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, action_generator, one_mul, map_one, mul_one] using he.symm
    · exact mul_comm _ _

/-- Exact identification of the graph centralizer, rather than only a subgroup. -/
def centralizerEquiv : Sp × C2 ≃*
    centralizer ({sigma F σ hσ} : Set (Extension F σ hσ)) :=
  MulEquiv.ofBijective ((centralizerHom F σ hσ).codRestrict _ (fun x =>
    (mem_graph_centralizer F σ hσ _).mpr (embedding_fixed F σ hσ x.1)))
    ⟨fun a b h => centralizerHom_injective F σ hσ (congrArg Subtype.val h), by
      intro x
      let u : (matrixAut F σ hσ).fixedSubgroup :=
        ⟨x.val.left,(MulAut.mem_fixedSubgroup _ _).mpr
          ((mem_graph_centralizer F σ hσ x.val).mp x.property)⟩
      refine ⟨((fixedEquiv F σ hσ).symm u,x.val.right),?_⟩
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact congrArg Subtype.val ((fixedEquiv F σ hσ).apply_symm_apply u)
      · rfl⟩

theorem centralizerEquiv_coe (x : Sp × C2) :
    (centralizerEquiv F σ hσ x).val = centralizerHom F σ hσ x := by rfl

/-- The point half of the graph fixed amalgam includes the whole central C₂. -/
theorem centralizerHom_mem_point [Finite F] (x : Sp × C2) :
    centralizerHom F σ hσ x ∈ point F σ hσ ↔
      x.1 ∈ Theory.SpecificGroups.SymplecticFour.pointParabolic :=
  embedding_mem_point F σ hσ x.1

/-- The plane half is matched by the very same full centralizer isomorphism. -/
theorem centralizerHom_mem_plane [Finite F] (x : Sp × C2) :
    centralizerHom F σ hσ x ∈ plane F σ hσ ↔
      x.1 ∈ Theory.SpecificGroups.SymplecticFour.planeParabolic :=
  embedding_mem_plane F σ hσ x.1

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
