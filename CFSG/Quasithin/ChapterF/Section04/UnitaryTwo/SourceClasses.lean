module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelClasses
/-!
# Complete long/short involution classes in the ordinary U₄(2) completion

The actual overlap Sylow is an ambient Sylow by the original long-root
centralizer bound. Its involutions move into the plane radical by the point
endpoint. The local class count gives the long and short classes exhaustively;
their centralizer orders 576 and 96 exclude further fusion.
-/

open Subgroup
open Theory.GroupTheory.CentralizerSmallKernelTransport
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.SourceClasses
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion ShortRootCentralizer ModelClasses
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "P" => pointParabolic 1 hn
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

omit [Finite G] in
theorem source_plane_classes (x : G) (hx : x ∈ PlainFusion.planeImage c i) :
    x = 1 ∨ IsConj (i (c.left longPoint)) x ∨ IsConj (sourceShort c i) x := by
  rw [← radical_image] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  rcases local_radical_classes a ha with he | he | he
  · left; rw [he,map_one]
  · right; left
    have hh := (matrixPlaneEmbedding c i).map_isConj he
    rw [show matrixPlaneEmbedding c i modelLong = i (c.left longPoint) from long_image c i] at hh
    exact hh
  · exact Or.inr (Or.inr ((matrixPlaneEmbedding c i).map_isConj he))

theorem source_involution_classes
    (hi : Function.Injective i)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (x : G) (hx : orderOf x = 2) :
    IsConj (i (c.left longPoint)) x ∨ IsConj (sourceShort c i) x := by
  obtain ⟨S,hS⟩ := source_plain_sylow c i hi z hz hzroot hc
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,hx]; exact dvd_rfl)
  obtain ⟨T,hT⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G T S
  have hyS : g * x * g⁻¹ ∈ (S : Subgroup G) := by
    rw [← hg]
    exact ⟨x,hT (mem_zpowers x),rfl⟩
  rw [hS] at hyS
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : (g * x * g⁻¹) ^ 2 = 1 := by
    simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj g) hx2
  obtain ⟨p,hp⟩ := InvolutionFusion.overlap_involution_to_plane c i hi hyS hy2
  let y := i (c.left p) * (g * x * g⁻¹) * (i (c.left p))⁻¹
  have hxy : IsConj x y := (isConj_iff.mpr ⟨g,rfl⟩).trans (isConj_iff.mpr ⟨i (c.left p),rfl⟩)
  rcases source_plane_classes c i y hp with he | he | he
  · have hx1 : x = 1 := isConj_one_left.mp (he ▸ hxy)
    simp [hx1] at hx
  · exact Or.inl (he.trans hxy.symm)
  · exact Or.inr (he.trans hxy.symm)

theorem source_long_centralizer_card
    (hi : Function.Injective i)
    (hc : centralizer ({i (c.left longPoint)} : Set G) ≤ (i.comp c.left).range) :
    Nat.card (centralizer ({i (c.left longPoint)} : Set G)) = 576 := by
  have hz : orderOf (i (c.left longPoint)) = 2 :=
    (orderOf_injective (i.comp c.left) (hi.comp c.left_injective) longPoint).trans longPoint_order
  rw [(source_plain_root_normalizer c i longPoint hz longPoint_mem_root hc).1]
  exact (Nat.card_congr (MonoidHom.ofInjective (f := i.comp c.left) (hi.comp c.left_injective)).symm.toEquiv).trans
    BinaryCompletion.point_card

theorem source_long_short_nonconjugate
    (hi : Function.Injective i)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    ¬ IsConj (i (c.left longPoint)) (sourceShort c i) := by
  have hez := root_eq_longPoint z hz hzroot
  subst z
  intro hh
  obtain ⟨g,hg⟩ := isConj_iff.mp hh
  have he := Nat.card_congr (centralizerEquiv (MulAut.conj g) (i (c.left longPoint))).toEquiv
  change Nat.card (centralizer ({i (c.left longPoint)} : Set G)) =
    Nat.card (centralizer ({g * i (c.left longPoint) * g⁻¹} : Set G)) at he
  rw [hg,source_long_centralizer_card c i hi hc,
    source_short_centralizer_card c i hi longPoint longPoint_order longPoint_mem_root hc hnorm] at he
  omega
end CFSG.Quasithin.ChapterF.UnitaryTwo.SourceClasses