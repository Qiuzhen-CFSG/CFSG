module
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
/-!
# A concrete symplectic subgroup of the fixed U₆(2) carrier

Entrywise scalar extension sends Sp₆(2) into the special unitary group of
the reindexed hyperbolic Hermitian form over GF(4). Orthonormalization
conjugates that form to the identity form used by the actual U₆(2) model.
The projective kernel is central in the faithful symplectic matrix group,
whose center is trivial in characteristic two. The resulting injection has
the literal PSp₆(2) domain and the fixed projective unitary codomain.

This supplies the simple symplectic section used in Aschbacher–Smith A.2.19,
printed pp.40–41, through the Fischer involution-centralizer quotients.
The matrix construction is internal; the exported theorem has no geometry,
order, semisimplicity or comparison assumption.
-/

section
noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.U6Two.SymplecticEmbedding
abbrev Index := Fin 3 ⊕ Fin 3
abbrev Sp := Matrix.symplecticGroup (Fin 3) (ZMod 2)

def reindex : Matrix Index Index U6Two.Field ≃ₐ[U6Two.Field]
    Matrix (Fin 6) (Fin 6) U6Two.Field :=
  Matrix.reindexAlgEquiv U6Two.Field U6Two.Field finSumFinEquiv

def gram : HermitianForm 6 U6Two.Field where
  conj := U6Two.conjugation
  conj_involutive := U6Two.conjugation_involutive
  form := reindex (Matrix.J (Fin 3) U6Two.Field)
  form_hermitian := by
    intro i j
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Index ≃ Fin 6).surjective i
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Index ≃ Fin 6).surjective j
    simp only [reindex, Matrix.reindexAlgEquiv, Matrix.reindexRingEquiv]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, U6Two.conjugation_apply,
        CharTwo.neg_eq, eq_comm]
  form_nondegenerate := by
    change (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.J (Fin 3) U6Two.Field)).det ≠ 0
    rw [Matrix.det_reindex_self]
    exact (Matrix.isUnit_det_J (Fin 3) U6Two.Field).ne_zero

def matrixHom : Sp →* Matrix (Fin 6) (Fin 6) U6Two.Field :=
  reindex.toMonoidHom.comp
    (((algebraMap (ZMod 2) U6Two.Field).mapMatrix).toMonoidHom.comp
      (Matrix.symplecticGroup (Fin 3) (ZMod 2)).subtype)

def ambientHom : Sp →* GL (Fin 6) U6Two.Field := matrixHom.toHomUnits

theorem ambientHom_injective : Function.Injective ambientHom := by
  intro a b hab
  apply Subtype.ext
  have he := congrArg Units.val hab
  apply Matrix.map_injective (algebraMap (ZMod 2) U6Two.Field).injective
  exact reindex.injective he

theorem conjugation_binary (x : ZMod 2) :
    U6Two.conjugation (algebraMap (ZMod 2) U6Two.Field x) =
      algebraMap (ZMod 2) U6Two.Field x := by
  rw [U6Two.conjugation_apply, ← map_pow]
  congr 1
  simp


theorem ambientHom_val (g : Sp) : (ambientHom g).val =
    reindex (g.val.map (algebraMap (ZMod 2) U6Two.Field)) := by rfl

theorem reindex_det (A : Matrix Index Index U6Two.Field) : (reindex A).det = A.det :=
  Matrix.det_reindex_self finSumFinEquiv A

theorem ambient_mem (g : Sp) : ambientHom g ∈ gram.specialSubgroup := by
  rw [gram.mem_specialSubgroup_iff]
  constructor
  · have hadj : gram.conjTranspose (ambientHom g).val =
        reindex ((g.val.map (algebraMap (ZMod 2) U6Two.Field))ᵀ) := by
      ext i j
      exact conjugation_binary _
    rw [hadj]
    change reindex ((g.val.map (algebraMap (ZMod 2) U6Two.Field))ᵀ) *
      reindex (Matrix.J (Fin 3) U6Two.Field) *
      reindex (g.val.map (algebraMap (ZMod 2) U6Two.Field)) =
      reindex (Matrix.J (Fin 3) U6Two.Field)
    rw [← map_mul, ← map_mul]
    exact congrArg reindex (SymplecticGroup.mem_iff'.mp
      (SymplecticGroup.map_mem g.property (algebraMap (ZMod 2) U6Two.Field)))
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, ambientHom_val, reindex_det]
    have hd := (algebraMap (ZMod 2) U6Two.Field).map_det g.val
    rw [SymplecticGroup.det_eq_one g.property, map_one] at hd
    exact hd.symm

def projectiveHom : Sp →* ProjectiveSpecialUnitaryMatrixGroup gram :=
  (Matrix.ProjGenLinGroup.mk.comp ambientHom).codRestrict _
    (fun g => ⟨ambientHom g, ambient_mem g, rfl⟩)

theorem projectiveHom_injective : Function.Injective projectiveHom := by
  apply (injective_iff_map_eq_one projectiveHom).mpr
  intro g hg
  have hz : ambientHom g ∈ center (GL (Fin 6) U6Two.Field) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hg)
  have hgz : g ∈ center Sp := by
    apply mem_center_iff.mpr
    intro x
    apply ambientHom_injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hz (ambientHom x)
  have hbot := SymplecticSix.EvenProjective.center_eq_bot (F := ZMod 2)
  simpa only [hbot, mem_bot] using hgz

public theorem exists_embedding :
    ∃ j : SymplecticSix.PSp (ZMod 2) →* U6Two.Carrier, Function.Injective j := by
  obtain ⟨C,e,ep,_,_,_⟩ := HermitianForm.IdentityGram.exists_identityGram_transport
    gram 2 Nat.prime_two (by simpa using U6Two.field_card) (fun x => rfl)
  have hform : HermitianForm.IdentityGram.identityGram gram = U6Two.form := rfl
  let b : ProjectiveSpecialUnitaryMatrixGroup gram ≃* U6Two.Carrier := by
    exact ep.trans (MulEquiv.subgroupCongr (congrArg ProjectiveSpecialUnitaryMatrixGroup hform))
  let a : SymplecticSix.PSp (ZMod 2) ≃* Sp :=
    (SymplecticSix.EvenProjective.equiv (F := ZMod 2)).symm
  exact ⟨(b.toMonoidHom.comp projectiveHom).comp a.toMonoidHom,
    b.injective.comp (projectiveHom_injective.comp a.injective)⟩

end Theory.SpecificGroups.U6Two.SymplecticEmbedding
