module

public import Theory.Representation.SL2FourProjectiveRecognition.Copies
public import Mathlib.Algebra.Module.ZMod
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry.Standard
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveOrbit.Geometry

/-!
# The projective recognition theorem for SL₂(4)

Every finite binary module satisfying all clauses of the projective
criterion is a direct sum of natural planes. Two opposite projective
images are disjoint. Their sum is invariant under upper roots and the
Weyl element, hence under SL₂(4), so equivariance and spanning make them
complementary. The diagonal torus preserves the first image. The concrete
root-coordinate recognition theorem then gives the required copies with
the original action. Multiplicity zero is included.

This proves the field-four rank-one case of G.1.3 directly; no universal
recognition or representation-classification implication is assumed.
Source: Aschbacher–Smith, G.1.3 and G.1.7, printed pp.327–329.
-/

public noncomputable section
open Representation Representation.SL2FourNatural Representation.SL2FourNatural.ProjectiveRecognition
open scoped MatrixGroups LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition
open Section02.RankOneHigherFields.QuotientAction.Projective
open Section02.AlternatingFive.Recognition.ProjectiveGeometry
universe u
variable {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
variable {σ : Representation (ZMod 2) SL M} {φ : Point F → Submodule (ZMod 2) M}

private theorem point_transitive (P Q : Point F) :
    ∃ g : SL, Q.val = P.val.map (specialLinearNatural 2 g) := by
  let e := Projectivization.equivSubmodule F V
  let : MulAction.IsPretransitive SL (ℙ F V) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL (e.symm P) (e.symm Q)
  have he : translate g P = Q := by
    change e (g • e.symm P) = Q
    rw [hg]
    exact e.apply_symm_apply Q
  exact ⟨g, he ▸ translate_val g P⟩

theorem criterion_rootPair (h : Criterion σ φ) : RootPair σ weyl (φ standardPoint) := by
  have hdim : Module.finrank F standardPoint.val + 1 = Module.finrank F V := by
    rw [standardPoint.property]
    simp
  have hroot (t : F) : upper t ∈ rootGroup F standardPoint.val :=
    ⟨upper_displacement_firstLine t, upper_fixed_firstLine t⟩
  have hm (t : F) (x : M) : σ (upper t) x - x ∈ φ standardPoint :=
    h.root_moved standardPoint standardPoint.val hdim le_rfl _ (hroot t) x
  have hf (t : F) (x : M) (hx : x ∈ φ standardPoint) : σ (upper t) x = x :=
    h.root_fixed standardPoint standardPoint.val hdim le_rfl standardPoint le_rfl _ (hroot t) x hx
  refine ⟨?_, hf, hm⟩
  have he : φ (translate weyl standardPoint) = (φ standardPoint).map (σ weyl) :=
    h.equivariant weyl standardPoint _ (translate_val weyl standardPoint)
  have hd : Disjoint (φ standardPoint) ((φ standardPoint).map (σ weyl)) := by
    rw [← he]
    apply h.disjoint
    intro hp
    apply firstLine_weyl_ne
    exact (congrArg Subtype.val hp).trans (translate_val weyl standardPoint)
  let S := φ standardPoint ⊔ (φ standardPoint).map (σ weyl)
  have hu (t : F) (x : M) (hx : x ∈ S) : σ (upper t) x ∈ S := by
    have hx' : σ (upper t) x - x ∈ S := (show φ standardPoint ≤ S from le_sup_left) (hm t x)
    simpa only [sub_add_cancel] using S.add_mem hx' hx
  have hw (x : M) (hx : x ∈ S) : σ weyl x ∈ S := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hb
    rw [map_add]
    apply S.add_mem
    · exact (show (φ standardPoint).map (σ weyl) ≤ S from le_sup_right)
        (Submodule.mem_map.mpr ⟨a,ha,rfl⟩)
    · have hi : σ weyl (σ weyl y) = y := by
        rw [← Module.End.mul_apply, ← map_mul, weyl_mul_self, map_one, Module.End.one_apply]
      rw [hi]
      exact (show φ standardPoint ≤ S from le_sup_left) hy
  have hall := invariant_of_upper_weyl σ S hu hw
  have ht : S = ⊤ := by
    apply top_unique
    rw [← h.spanning]
    apply iSup_le
    intro P
    obtain ⟨g,hg⟩ := point_transitive standardPoint P
    rw [h.equivariant g standardPoint P hg]
    rintro x ⟨y,hy,rfl⟩
    exact hall g y ((show φ standardPoint ≤ S from le_sup_left) hy)
  exact ⟨hd, codisjoint_iff.mpr ht⟩

theorem criterion_diagonal (h : Criterion σ φ) :
    ∀ x ∈ φ standardPoint, σ diagonalWord x ∈ φ standardPoint := by
  have he := h.equivariant diagonalWord standardPoint standardPoint diagonalWord_firstLine.symm
  intro x hx
  rw [he]
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

theorem naturalCopies [Finite M] (h : Criterion σ φ) : ∃ s : ℕ, NaturalCopies σ s := by
  obtain ⟨s,e,he⟩ := natural_coordinates (criterion_rootPair h) (criterion_diagonal h)
  refine ⟨s, ?_⟩
  unfold NaturalCopies
  let e₀ : M ≃+ (Fin s → Fin 2 → F) := e.toAddEquiv
  have he₀ : ∀ g v i, e₀ (σ g v) i = Matrix.mulVec g.val (e₀ v i) := he
  let : Module (ZMod 2) F := @Algebra.toModule (ZMod 2) F _ _ (ZMod.algebra F 2)
  let e' : M ≃ₗ[ZMod 2] (Fin s → Fin 2 → F) :=
    { e₀ with map_smul' := ZMod.map_smul e₀ }
  exact ⟨e',he₀⟩

end CFSG.Quasithin.ChapterG.Section01.SL2FourRecognition
