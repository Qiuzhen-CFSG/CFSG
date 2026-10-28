module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer.FixedWords
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders
public import Theory.GroupTheory.Amalgam.RankTwoCompletion

/-!
# The marked graph centralizer in a faithful binary unitary completion

The fixed binary words are transported through the actual point and plane
endpoint maps. Their double commutator belongs to the marked overlap, and
its commutator with the plane actor is a nonidentity cubic. Consequently the
centralizer of the marked graph involution has a second derived subgroup
which is not a two-group, in every faithful completion and every injective
ambient embedding.

This is the local obstruction used in F.4.36, printed p.292. The independent
binary extended-point calculation identifies the target two-group when the
graph involution is hypothetically fused to the source root involution.
-/
@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.GraphCentralizer
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "P" => Extension.point 1 hn
local notation "R" => Extension.plane 1 hn
local notation "B" => Extension.overlap 1 hn
local notation "α" => Extension.amalgam 1 hn

def modelMap : UnitaryFourFlag.SU F (UnitaryFourFlag.form F σ hσ) →* Extension.ProjectiveExtension 1 hn :=
  SemidirectProduct.inl.comp (projection 1 hn)

theorem modelMap_injective : Function.Injective modelMap :=
  SemidirectProduct.inl_injective.comp (projection_injective 1 hn)

/-- The original common graph involution, with its actual overlap membership. -/
def graphInvolution : B :=
  ⟨Extension.sigma 1 hn, ⟨UnitaryFourOuter.sigma F σ hσ,
    UnitaryFourOuter.sigma_mem_overlap F σ hσ, Extension.extensionProjection_sigma 1 hn⟩⟩

def pointAtom (k : Fin 3) : P :=
  ⟨modelMap (UnitaryFourGraphCentralizer.atom F σ hσ k.castSucc), (Extension.mem_point 1 hn _).mpr
    ⟨UnitaryFourGraphCentralizer.atom F σ hσ k.castSucc, UnitaryFourGraphCentralizer.atom_point F σ hσ k, rfl⟩⟩

def planeAtom : R :=
  ⟨modelMap (UnitaryFourGraphCentralizer.atom F σ hσ 3), (Extension.mem_plane 1 hn _).mpr
    ⟨UnitaryFourGraphCentralizer.atom F σ hσ 3, UnitaryFourGraphCentralizer.atom_plane F σ hσ, rfl⟩⟩

def overlapActor : B :=
  ⟨modelMap (UnitaryFourGraphCentralizer.overlapWord F σ hσ), Extension.binary_mem_overlap _ |>.mpr
    ⟨UnitaryFourGraphCentralizer.overlapWord F σ hσ, UnitaryFourGraphCentralizer.overlapWord_mem F σ hσ, rfl⟩⟩

private theorem atom_commutes_sigma (k : Fin 4) :
    Commute (modelMap (UnitaryFourGraphCentralizer.atom F σ hσ k)) (Extension.sigma 1 hn) := by
  have hf : Extension.projectiveAction 1 hn UnitaryFourOuter.generator
      (projection 1 hn (UnitaryFourGraphCentralizer.atom F σ hσ k)) = projection 1 hn (UnitaryFourGraphCentralizer.atom F σ hσ k) := by
    rw [Extension.projectiveAction_generator]
    change Extension.projectiveAut 1 hn (Extension.projectEquiv 1 hn (UnitaryFourGraphCentralizer.atom F σ hσ k)) =
      Extension.projectEquiv 1 hn (UnitaryFourGraphCentralizer.atom F σ hσ k)
    exact (Extension.projectiveAut_project 1 hn _).trans
      (congrArg (Extension.projectEquiv 1 hn)
        (UnitaryFourGraphCentralizer.atom_fixed F σ hσ k))
  have hc := SemidirectProduct.inl_aut (φ := Extension.projectiveAction 1 hn)
    UnitaryFourOuter.generator (projection 1 hn (UnitaryFourGraphCentralizer.atom F σ hσ k))
  rw [hf, map_inv] at hc
  have hc' : Extension.sigma 1 hn * modelMap (UnitaryFourGraphCentralizer.atom F σ hσ k) * (Extension.sigma 1 hn)⁻¹ =
      modelMap (UnitaryFourGraphCentralizer.atom F σ hσ k) := hc.symm
  exact (mul_inv_eq_iff_eq_mul.mp hc').symm

theorem pointAtom_commutes_graph (k : Fin 3) :
    Commute (pointAtom k) ((Extension.amalgam 1 hn).left graphInvolution) := by
  show pointAtom k * (Extension.amalgam 1 hn).left graphInvolution = (Extension.amalgam 1 hn).left graphInvolution * pointAtom k
  exact Subtype.ext (atom_commutes_sigma k.castSucc).eq

theorem planeAtom_commutes_graph :
    Commute planeAtom ((Extension.amalgam 1 hn).right graphInvolution) := by
  show planeAtom * (Extension.amalgam 1 hn).right graphInvolution = (Extension.amalgam 1 hn).right graphInvolution * planeAtom
  exact Subtype.ext (atom_commutes_sigma 3).eq

/-- The entire double-commutator evaluation occurs in the point endpoint. -/
theorem overlapActor_left :
    (Extension.amalgam 1 hn).left overlapActor = ⁅⁅pointAtom 0, pointAtom 1⁆, ⁅pointAtom 1, pointAtom 2⁆⁆ := by
  apply Subtype.ext
  change modelMap (UnitaryFourGraphCentralizer.overlapWord F σ hσ) =
    ⁅⁅modelMap (UnitaryFourGraphCentralizer.atom F σ hσ 0), modelMap (UnitaryFourGraphCentralizer.atom F σ hσ 1)⁆,
      ⁅modelMap (UnitaryFourGraphCentralizer.atom F σ hσ 1), modelMap (UnitaryFourGraphCentralizer.atom F σ hσ 2)⁆⁆
  simp only [UnitaryFourGraphCentralizer.overlapWord, UnitaryFourGraphCentralizer.firstWord, UnitaryFourGraphCentralizer.secondWord, map_commutatorElement]

def cubicActor : R := ⁅(Extension.amalgam 1 hn).right overlapActor, planeAtom⁆

theorem cubicActor_val :
    cubicActor.val = modelMap (UnitaryFourGraphCentralizer.cubicWord F σ hσ) := by
  change ⁅modelMap (UnitaryFourGraphCentralizer.overlapWord F σ hσ), modelMap (UnitaryFourGraphCentralizer.atom F σ hσ 3)⁆ =
    modelMap ⁅UnitaryFourGraphCentralizer.overlapWord F σ hσ, UnitaryFourGraphCentralizer.atom F σ hσ 3⁆
  exact (map_commutatorElement modelMap _ _).symm

theorem cubicActor_cube : cubicActor ^ 3 = 1 := by
  apply Subtype.ext
  change cubicActor.val ^ 3 = 1
  rw [cubicActor_val, ← map_pow, UnitaryFourGraphCentralizer.cubicWord_cube, map_one]

theorem cubicActor_ne_one : cubicActor ≠ 1 := by
  intro h
  have hh := congrArg Subtype.val h
  rw [cubicActor_val] at hh
  exact UnitaryFourGraphCentralizer.cubicWord_ne_one F σ hσ (modelMap_injective (hh.trans modelMap.map_one.symm))

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion α (G := G0))
  (i : G0 →* G)

def graphCentralizer : Subgroup G := centralizer ({i (c.middle graphInvolution)} : Set G)

private theorem pointAtom_mem_centralizer (k : Fin 3) :
    i (c.left (pointAtom k)) ∈ graphCentralizer c i := by
  apply mem_centralizer_singleton_iff.mpr
  exact ((pointAtom_commutes_graph k).map (i.comp c.left)).eq

private theorem planeAtom_mem_centralizer :
    i (c.right planeAtom) ∈ graphCentralizer c i := by
  apply mem_centralizer_singleton_iff.mpr
  change i (c.right planeAtom) * i (c.middle graphInvolution) =
    i (c.middle graphInvolution) * i (c.right planeAtom)
  rw [DFunLike.congr_fun c.compatible graphInvolution]
  exact (planeAtom_commutes_graph.map (i.comp c.right)).eq

private theorem source_overlapActor :
    ⁅⁅i (c.left (pointAtom 0)), i (c.left (pointAtom 1))⁆,
      ⁅i (c.left (pointAtom 1)), i (c.left (pointAtom 2))⁆⁆ =
      i (c.right ((Extension.amalgam 1 hn).right overlapActor)) := by
  calc
    _ = (i.comp c.left) ⁅⁅pointAtom 0, pointAtom 1⁆, ⁅pointAtom 1, pointAtom 2⁆⁆ := by
      simp only [map_commutatorElement, MonoidHom.comp_apply]
    _ = (i.comp c.left) ((Extension.amalgam 1 hn).left overlapActor) := congrArg (i.comp c.left) overlapActor_left.symm
    _ = _ := congrArg i (DFunLike.congr_fun c.compatible overlapActor)

/-- An explicit cubic survives in the second derived subgroup of the
literal graph-involution centralizer in every faithful completion. -/
theorem graphCentralizer_not_two_group_second_derived
    (hi : Function.Injective i) :
    ¬ IsPGroup 2 (derivedSeries (graphCentralizer c i) 2) := by
  let C := graphCentralizer c i
  let a : C := ⟨i (c.left (pointAtom 0)), pointAtom_mem_centralizer c i 0⟩
  let b : C := ⟨i (c.left (pointAtom 1)), pointAtom_mem_centralizer c i 1⟩
  let d : C := ⟨i (c.left (pointAtom 2)), pointAtom_mem_centralizer c i 2⟩
  let y : C := ⟨i (c.right planeAtom), planeAtom_mem_centralizer c i⟩
  let w : C := ⁅⁅a,b⁆,⁅b,d⁆⁆
  have hw : w ∈ derivedSeries C 2 :=
    commutator_mem_commutator
      (commutator_mem_commutator (mem_top a) (mem_top b))
      (commutator_mem_commutator (mem_top b) (mem_top d))
  have ht : ⁅w,y⁆ ∈ derivedSeries C 2 :=
    (commutator_le_left (derivedSeries C 2) ⊤)
      (commutator_mem_commutator hw (mem_top y))
  let t : derivedSeries C 2 := ⟨⁅w,y⁆, ht⟩
  let f : derivedSeries C 2 →* G := C.subtype.comp (derivedSeries C 2).subtype
  have htf : f t = i (c.right cubicActor) := by
    change ⁅⁅⁅i (c.left (pointAtom 0)), i (c.left (pointAtom 1))⁆,
      ⁅i (c.left (pointAtom 1)), i (c.left (pointAtom 2))⁆⁆, i (c.right planeAtom)⁆ =
      (i.comp c.right) ⁅(Extension.amalgam 1 hn).right overlapActor, planeAtom⁆
    rw [source_overlapActor c i, map_commutatorElement]
    rfl
  have ht3 : t ^ 3 = 1 := by
    apply (Subtype.val_injective.comp Subtype.val_injective)
    change f (t ^ 3) = f 1
    rw [map_pow, map_one, htf, ← map_pow, ← map_pow, cubicActor_cube, map_one, map_one]
  have htne : t ≠ 1 := by
    intro he
    apply cubicActor_ne_one
    apply c.right_injective
    apply hi
    have hh := congrArg f he
    simpa only [htf, map_one] using hh
  intro hp
  have hdiv := (hp.dvd_orderOf htne).trans (orderOf_dvd_of_pow_eq_one ht3)
  norm_num at hdiv

end CFSG.Quasithin.ChapterF.UnitaryTwo.GraphCentralizer
