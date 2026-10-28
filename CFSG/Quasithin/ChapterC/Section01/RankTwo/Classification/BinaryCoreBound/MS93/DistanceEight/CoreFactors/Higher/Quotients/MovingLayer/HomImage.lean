module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.CommutatorHom
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Singer

/-!
# The actual quotient of commutator images

Keep Φ(hat W) as the denominator in Φ(X). The canonical surjection from
X to this image quotient has kernel exactly hat W · ker Φ. Its action
retains the original marking through the actual commutator homomorphism.

The Singer calculation is applied to the invariant image of hat W. If the
whole local group fixed X/hat W, the image quotient would be trivial, and
X would equal hat W · ker Φ. This implication alone is not a contradiction:
the kernel consists of elements centralizing hat W modulo Z(G_a).
`NontrivialAction` supplies an independent earlier-source exclusion of
trivial residual action without assuming this kernel lies in hat W.

Source: Meierfrankenfeld--Stellmacher (1993), the commutator sentence in
(4.5.4)(iv), printed p.899. This corrects the first-argument image quotient;
it does not claim the displayed pairing in the paper is well-defined.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}
  (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
  (p : Higher.SourcePath (alpha R))
  (hWQ : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤ Z R (alpha R))
  (d : MarkedPairSection source common
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
    (hatV R (alpha R) (p.walk.getVert 6)) true)

private noncomputable def linearHom :
    orbitMovingGroup p →* Multiplicative ((W × W) →ₗ[ZMod 2] W) where
  toFun x := Multiplicative.ofAdd
    ((AddMonoidHom.toMultiplicative.symm (commutatorHom common earlier p hWQ d x)).toZModLinearMap 2)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    change (commutatorHom common earlier p hWQ d 1 (Multiplicative.ofAdd v)).toAdd = 0
    rw [map_one]
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    change (commutatorHom common earlier p hWQ d (x*y) (Multiplicative.ofAdd v)).toAdd =
      (commutatorHom common earlier p hWQ d x (Multiplicative.ofAdd v)).toAdd +
      (commutatorHom common earlier p hWQ d y (Multiplicative.ofAdd v)).toAdd
    rw [map_mul]
    rfl

private theorem linearHom_ker : (linearHom common earlier p hWQ d).ker =
    (commutatorHom common earlier p hWQ d).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    apply MonoidHom.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact congrArg (fun f : (W × W) →ₗ[ZMod 2] W => f v.toAdd)
      (congrArg Multiplicative.toAdd h)
  · intro h
    apply Multiplicative.toAdd.injective
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Multiplicative (W × W) →* Multiplicative W =>
      (f (Multiplicative.ofAdd v)).toAdd) h

private theorem linearHom_singer (m : M)
    (hm : common.natural.marking (source.projection m) = Singer.singer)
    (x y : orbitMovingGroup p)
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
    Singer.onHom (linearHom common earlier p hWQ d x).toAdd =
      (linearHom common earlier p hWQ d y).toAdd := by
  apply (Singer.onHom_eq_iff _ _).mpr
  intro v
  have he := commutatorHom_action common earlier p hWQ d m x y hy v
  rw [hm] at he
  exact he

private noncomputable def denominatorImage : Submodule (ZMod 2) ((W × W) →ₗ[ZMod 2] W) :=
  AddSubgroup.toZModSubmodule 2 (((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
    (orbitMovingGroup p)).map (linearHom common earlier p hWQ d)).toAddSubgroup'

private theorem denominatorImage_stable (f : (W × W) →ₗ[ZMod 2] W)
    (hf : f ∈ denominatorImage common earlier p hWQ d) :
    Singer.onHom f ∈ denominatorImage common earlier p hWQ d := by
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm Singer.singer)
  have hmark : common.natural.marking (source.projection m) = Singer.singer := by simp [hm]
  obtain ⟨x,hx,he⟩ := hf
  let y : orbitMovingGroup p := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp (orbitMovingGroup_normalized p) _ ⟨m,rfl⟩ _ x.property⟩
  have hyW : (y : FreeAmalgam R) ∈ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
    le_normalizer_iff.mp d.normalized _ ⟨m,rfl⟩ _ hx
  refine ⟨y,hyW,?_⟩
  apply Multiplicative.toAdd.injective
  rw [← linearHom_singer common earlier p hWQ d m hmark x y rfl, he]
  rfl

private theorem image_eq_of_trivial_action
    (hfix : ⁅orbitMovingGroup p,Mbar R⁆ ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) :
    ((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf (orbitMovingGroup p)).map
      (linearHom common earlier p hWQ d) = (linearHom common earlier p hWQ d).range := by
  apply le_antisymm (map_le_range _ _) ?_
  rintro f ⟨x,rfl⟩
  change (linearHom common earlier p hWQ d x).toAdd ∈ denominatorImage common earlier p hWQ d
  apply Singer.mem_of_displacement_mem _ (denominatorImage_stable common earlier p hWQ d)
  obtain ⟨m,hm⟩ := source.projection_surjective (common.natural.marking.symm Singer.singer)
  have hmark : common.natural.marking (source.projection m) = Singer.singer := by simp [hm]
  let y : orbitMovingGroup p := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
    le_normalizer_iff.mp (orbitMovingGroup_normalized p) _ ⟨m,rfl⟩ _ x.property⟩
  have hyW : (y * x⁻¹ : orbitMovingGroup p) ∈
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf (orbitMovingGroup p) := by
    change ⁅embedM R m,(x : FreeAmalgam R)⁆ ∈
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
    rw [commutator_comm] at hfix
    exact hfix (commutator_mem_commutator ⟨m,rfl⟩ x.property)
  refine ⟨y * x⁻¹,hyW,?_⟩
  apply Multiplicative.toAdd.injective
  rw [map_mul, map_inv]
  simp only [sub_eq_add_neg]
  rw [linearHom_singer common earlier p hWQ d m hmark x y rfl]
  rfl

/-- The literal image quotient Φ(X)/Φ(hat W), using the original commutator map. -/
noncomputable abbrev CommutatorImageQuotient :=
  (commutatorHom common earlier p hWQ d).range ⧸
    ((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf (orbitMovingGroup p)).map
      (commutatorHom common earlier p hWQ d).rangeRestrict

/-- The actual surjection onto the image quotient. -/
noncomputable def commutatorImageQuotientMap : orbitMovingGroup p →*
    CommutatorImageQuotient common earlier p hWQ d :=
  (QuotientGroup.mk' _).comp (commutatorHom common earlier p hWQ d).rangeRestrict

/-- Every image-quotient class has an actual preimage in X. -/
theorem commutatorImageQuotientMap_surjective :
    Function.Surjective (commutatorImageQuotientMap common earlier p hWQ d) :=
  (QuotientGroup.mk'_surjective _).comp (commutatorHom common earlier p hWQ d).rangeRestrict_surjective

/-- The kernel is hat W times ker Φ, not hat W without further proof. -/
theorem commutatorImageQuotientMap_ker :
    (commutatorImageQuotientMap common earlier p hWQ d).ker =
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf (orbitMovingGroup p) ⊔
        (commutatorHom common earlier p hWQ d).ker := by
  rw [commutatorImageQuotientMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
    comap_map_eq, MonoidHom.ker_rangeRestrict]

include common earlier hWQ d in
/-- The fixed-action hypothesis forces the literal product X = hat W · ker Φ. -/
theorem trivial_action_factorization
    (hfix : ⁅orbitMovingGroup p,Mbar R⁆ ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) :
    ∀ x : orbitMovingGroup p,
      ∃ w : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
      ∃ k : orbitMovingGroup p,
        (∀ v : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
          ⁅(k : FreeAmalgam R),(v : FreeAmalgam R)⁆ ∈
            (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) ∧
        (x : FreeAmalgam R) = (w : FreeAmalgam R) * (k : FreeAmalgam R) := by
  intro x
  have hx : linearHom common earlier p hWQ d x ∈
      ((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf (orbitMovingGroup p)).map
        (linearHom common earlier p hWQ d) := by
    rw [image_eq_of_trivial_action common earlier p hWQ d hfix]
    exact ⟨x,rfl⟩
  obtain ⟨w,hw,he⟩ := hx
  let k := w⁻¹ * x
  have hk : k ∈ (linearHom common earlier p hWQ d).ker := by
    change linearHom common earlier p hWQ d (w⁻¹ * x) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [linearHom_ker] at hk
  refine ⟨⟨w,hw⟩,k,(mem_commutatorHom_ker common earlier p hWQ d k).mp hk,?_⟩
  change (x : FreeAmalgam R) = (w : FreeAmalgam R) * ((w : FreeAmalgam R)⁻¹ * (x : FreeAmalgam R))
  group

/-- Under trivial local action, the actual image quotient is trivial. -/
theorem trivial_action_imageQuotientMap
    (hfix : ⁅orbitMovingGroup p,Mbar R⁆ ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) :
    commutatorImageQuotientMap common earlier p hWQ d = 1 := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w,k,hk,hx⟩ := trivial_action_factorization common earlier p hWQ d hfix x
  let w' : orbitMovingGroup p := ⟨w,(show hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
      orbitMovingGroup p from le_sup_right) w.property⟩
  have he : x = w' * k := Subtype.ext hx
  have hker : x ∈ (commutatorImageQuotientMap common earlier p hWQ d).ker := by
    rw [commutatorImageQuotientMap_ker,he]
    exact Subgroup.mul_mem _ (mem_sup_left w.property)
      (mem_sup_right ((mem_commutatorHom_ker common earlier p hWQ d k).mpr hk))
  exact hker

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
