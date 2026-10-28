module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioNormalizers
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry

/-!
# Solvability of the native M24 plane centralizer

The three coordinate plane vectors are the tetrad classes of three actual
sextets. Incidence between two of these sextets recovers the octad trio:
two points lie in the same octad exactly when a two-step path joins them
through their two coordinate tetrads. Thus a pointwise plane fixer preserves
the trio. Its permutation of the three octads has a two-group kernel,
since the faithful inverse-transpose action detects the whole linear part
of the native affine quotient. The plane centralizer is therefore solvable.

The small certificates check three six-part partitions and their Golay
messages against the existing native code. No M24 element enumeration is
used. MathieuPlaneResidual transfers this kernel bound to the actual
component normalizer; its Chapter 12 consumer retains the original plane.
Source: Aschbacher--Smith H.15.6(2), 8.2.6(1), printed pp.401,717,
refs/quasithin.pdf. Native coordinates and Golay rows are reused from the
existing attributed Mathieu code implementation.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
public noncomputable section
private def half (k : Fin 3) (i : Fin 3) (b : ZMod 2) : Finset (Fin 24) :=
  Finset.univ.filter (fun x => (coordinates x).1 = i ∧ (coordinates x).2 k = b)
private def halves (k : Fin 3) : Finset (Finset (Fin 24)) :=
  Finset.univ.image (fun p : Fin 3 × ZMod 2 => half k p.1 p.2)
private theorem half_cert : ∀ k : Fin 3,
    (halves k).card = 6 ∧
    (∀ A ∈ halves k, A.card = 4) ∧
    (∀ A ∈ halves k, ∀ B ∈ halves k, A ≠ B → Disjoint A B) ∧
    (halves k).biUnion id = Finset.univ := by
  simp only [halves, Finset.forall_mem_image]
  decide +kernel
private def halfMessage (k : Fin 3) (p : Fin 3 × ZMod 2) : Fin 4096 :=
  (![![0,15,201,521,25,3369],![0,15,131,579,2099,1283],![0,15,197,517,3093,293]] k) ⟨(p.1.val * 2 + p.2.val) % 6, Nat.mod_lt _ (by decide)⟩
private theorem half_union_word : ∀ (k : Fin 3) (p q : Fin 3 × ZMod 2), p ≠ q →
    half k p.1 p.2 ∪ half k q.1 q.2 =
      m24GolayWord (m24GolayMessageXor (halfMessage k p) (halfMessage k q)) := by
  decide +kernel
private theorem half_octad (k : Fin 3) (A : Finset (Fin 24)) (hA : A ∈ halves k)
    (B : Finset (Fin 24)) (hB : B ∈ halves k) (hne : A ≠ B) : A ∪ B ∈ m24Blocks := by
  have hc : (A ∪ B).card = 8 := by
    rw [Finset.card_union_of_disjoint ((half_cert k).2.2.1 A hA B hB hne),
      (half_cert k).2.1 A hA,(half_cert k).2.1 B hB]
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hB
  have hpq : p ≠ q := fun he => hne (he ▸ rfl)
  rw [half_union_word k p q hpq] at hc ⊢
  exact m24GolayWord_mem_blocks_of_card_eq_eight _ hc
private def coordinateSextet (k : Fin 3) : Sextet where
  parts := halves k
  card := (half_cert k).1
  tetrad := (half_cert k).2.1
  disjoint := (half_cert k).2.2.1
  cover := (half_cert k).2.2.2
  octad := half_octad k
private theorem coordinateSextet_vector (k : Fin 3) :
    sextetVector (coordinateSextet k) = standardPlaneMap (Pi.single k 1) := by
  have hm : half k 0 1 ∈ (coordinateSextet k).parts :=
    Finset.mem_image.mpr ⟨(0,1),Finset.mem_univ _,rfl⟩
  rw [sextetVector_eq _ hm]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  revert k
  decide +kernel
private def sameHalf (k : Fin 3) (x y : Fin 24) : Prop :=
  ∃ B ∈ (coordinateSextet k).parts, x ∈ B ∧ y ∈ B
private theorem same_octad (x y : Fin 24) :
    (coordinates x).1 = (coordinates y).1 ↔
      ∃ z : Fin 24, sameHalf 0 x z ∧ sameHalf 1 z y := by
  revert x y
  unfold sameHalf
  simp only [coordinateSextet, halves, Finset.exists_mem_image]
  decide +kernel
private theorem preserves_half (g : M24) (k : Fin 3)
    (hg : cocodeRepresentation g (standardPlaneMap (Pi.single k 1)) =
      standardPlaneMap (Pi.single k 1)) {x y : Fin 24}
    (hxy : sameHalf k x y) : sameHalf k (g.val x) (g.val y) := by
  have hs : g ∈ sextetStabilizer (coordinateSextet k) := by
    rw [←sextetVector_stabilizer]
    change cocodeRepresentation g (sextetVector _) = sextetVector _
    rwa [coordinateSextet_vector]
  obtain ⟨B,hB,hx,hy⟩ := hxy
  refine ⟨g • B,?_,Finset.smul_mem_smul_finset hx,Finset.smul_mem_smul_finset hy⟩
  exact (show g • (coordinateSextet k).parts = _ from hs) ▸ Finset.smul_mem_smul_finset hB

/-- Fixing the plane pointwise preserves its actual octad trio. -/
theorem plane_fixer_mem_trio (g : M24)
    (hg : ∀ v, cocodeRepresentation g (standardPlaneMap v) = standardPlaneMap v) :
    g ∈ trioStabilizer standardTrio := by
  have hc (x y : Fin 24) (hxy : (coordinates x).1 = (coordinates y).1) :
      (coordinates (g.val x)).1 = (coordinates (g.val y)).1 := by
    obtain ⟨z,hxz,hzy⟩ := (same_octad x y).mp hxy
    exact (same_octad _ _).mpr ⟨g.val z,preserves_half g 0 (hg _) hxz,
      preserves_half g 1 (hg _) hzy⟩
  apply (mem_trioStabilizer_iff _ _).mpr
  intro A hA
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
  let j := (coordinates (g.val (point (i,0)))).1
  have he : g • standardTrioOctad i = standardTrioOctad j := by
    apply Finset.eq_of_subset_of_card_le ?_ (by
      simp only [Finset.card_smul_finset]
      rw [standardTrio.part_card (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),
        standardTrio.part_card (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)])
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_smul_finset.mp hx
    have hyi : (coordinates y).1 = i := by
      have hh := hy
      rw [←point_coordinates y] at hh
      exact (point_mem_octad_iff _ _ _).mp hh
    have hh := hc y (point (i,0)) (by rw [coordinates_point,hyi])
    change g.val y ∈ standardTrioOctad j
    rw [←point_coordinates (g.val y)]
    exact (point_mem_octad_iff _ _ _).mpr hh
  rw [he]
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

/-- A pointwise plane fixer acting trivially on the three octads is a translation. -/
theorem plane_fixer_in_core (g : trioStabilizer standardTrio)
    (hfirst : (standardAffineHom g).1 = 1)
    (hfix : ∀ v, cocodeRepresentation g.val (standardPlaneMap v) = standardPlaneMap v) :
    g ∈ pCore 2 (trioStabilizer standardTrio) := by
  let A := (standardAffineHom g).2
  have hq : standardAffineHom g = (1,A) := Prod.ext hfirst rfl
  have hl : Matrix.SpecialLinearGroup.toLin' (A⁻¹).transpose = 1 := by
    apply LinearEquiv.ext
    intro v
    exact standardPlaneMap_injective
      ((standardPlaneMap_action_of_affine g A hq v).symm.trans (hfix v))
  have hm : (A⁻¹).transpose = 1 := Matrix.SpecialLinearGroup.toLin'_injective
    (hl.trans (map_one _).symm)
  have hi : A⁻¹ = 1 := by
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_transpose,Matrix.transpose_transpose,
      Matrix.SpecialLinearGroup.coe_one,Matrix.transpose_one] using
      congrArg Matrix.transpose (congrArg Subtype.val hm)
  rw [←standardAffineHom_ker]
  exact Prod.ext hfirst (inv_eq_one.mp hi)

/-- Every native subgroup fixing the entire plane is solvable. The
permutation of its three octads has a two-group translation kernel. -/
theorem plane_fixer_solvable (A : Subgroup M24)
    (hfix : ∀ a : A, ∀ v,
      cocodeRepresentation a.val (standardPlaneMap v) = standardPlaneMap v) :
    Group.IsSolvable A := by
  let f : A →* trioStabilizer standardTrio := A.subtype.codRestrict _
    (fun a => plane_fixer_mem_trio a.val (hfix a))
  let χ := (MonoidHom.fst _ _).comp (standardAffineHom.comp f)
  let k : χ.ker →* pCore 2 (trioStabilizer standardTrio) :=
    (f.comp χ.ker.subtype).codRestrict _ (fun a =>
      plane_fixer_in_core (f a.val) a.property (hfix a.val))
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 (trioStabilizer standardTrio) =>
      (z.val.val : M24)) he))
  let : Group.IsNilpotent χ.ker := (pCore_isPGroup.of_injective k hk).isNilpotent
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.isSolvable_of_ker_le_range χ.ker.subtype χ (by simp)

end
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
