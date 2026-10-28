module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagLayer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPointExclusion
public import Theory.Representation.BinaryPermutation.SixCoreComparison

/-!
# The covered normalizer bound on the original first flag core

Assume its Baumann normalizer escapes N_G(L). The genuine MS pair on
L Baum(R₁) has initial moved subgroup exactly the original augmentation
five-space and retains the cubic initial kernel. The full MS cover theorem
gives a second augmentation marking on that same subgroup. Comparing the
two markings by the augmentation normalizer shows that the MS radical is
a conjugate point radical. The proved cubic point-image exclusion now
contradicts this pair and establishes the original normalizer bound.

The proof uses the actual R₁ and full covering kernel throughout. It never
identifies R₁ with O₂(L₁T) or supplies an MS exhaustion premise. The covered
13.3.9 residual argument remains necessary for solvable-cover exclusion.

Source: Aschbacher--Smith 13.2.2(7), p.878, via C.1.37 and C.1.32;
Meierfrankenfeld--Stellmacher (1993), (5.12), pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Exceptional.Exhaustion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem map_subgroupOf_inclusion {J X A : Subgroup G}
    (hJX : J ≤ X) (hAJ : A ≤ J) :
    (A.subgroupOf J).map (inclusion hJX) = A.subgroupOf X := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x.val,hAJ hx⟩,hx,rfl⟩

/-- Covered 13.2.2(7) on the literal source R₁, with the full-image
MS exclusion discharged. -/
theorem covered_firstFlagCore_baumann_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) := by
  by_contra hescape
  let B := ChapterB.baumann (firstFlagCore h structural D m)
  let J := L ⊔ B
  let X := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let W := ⁅centralOmega L B,K⁆
  let hms : SmallMSPair KnownSimple.IsKnownSimple L B :=
    covered_firstFlagCore_smallMSPair_of_escape h structural D m hc z hzT hzL hescape
  let e : CentralMarking L := m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm
  have hk : layerKernel L B = extensionKernel hms :=
    covered_firstFlagCore_initial_kernel_of_escape h structural D m hc z hzT hzL hescape
  have hW : W = V.subgroupOf J :=
    covered_firstFlagCore_initial_moved_of_escape h structural D m hc z hzT hzL hescape
  have hVJ : V ≤ J := D.le_component.trans le_sup_left
  let := hms.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
  let ew : W ≃* V := (MulEquiv.subgroupCongr hW).trans (subgroupOfEquivOfLe hVJ)
  let ec := (ew.trans m.coordinate).toAdditive.trans
    (AddEquiv.additiveMultiplicative (G := BinaryPermutation.core (Fin 6)))
  let E : Additive W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6) :=
    { ec with map_smul' := ZMod.map_smul ec }
  let π := CubicAction.projection hms e hc.2.1 hk
  let ρ := NormalElementaryQuotient.representation W π
    (LargeDistance.CubicEven.projection_surjective hms e hc.2.1 hk)
    (CubicAction.moved_projection_kernel hms e hc.2.1 hk)
  obtain ⟨q,hq,hLq,_,a,_,hBq,_⟩ :=
    covered_firstFlagCore_full_image_of_escape h structural D m hc z hzT hzL hescape
  have hRT : firstFlagCore h structural D m ≤ T := map_subtype_le _
  have hJX : J ≤ X := sup_le le_sup_left
    ((inf_le_left : B ≤ firstFlagCore h structural D m).trans (hRT.trans le_sup_right))
  let qJ := q.comp (inclusion hJX)
  have hKq : K.map qJ = alternatingGroup (Fin 6) := by
    rw [show qJ = q.comp (inclusion hJX) from rfl,←map_map,
      map_subgroupOf_inclusion hJX (show L ≤ J from le_sup_left)]
    exact hLq
  have hBqJ : (B.subgroupOf J).map qJ =
      pointCore.map (MulAut.conj a.val).toMonoidHom := by
    rw [show qJ = q.comp (inclusion hJX) from rfl,←map_map,
      map_subgroupOf_inclusion hJX (show B ≤ J from le_sup_right)]
    exact hBq
  have hE (g : J) (v : Additive W) :
      E (ρ (π g) v) = BinaryPermutation.coreRepresentation (Fin 6) (qJ g) (E v) := by
    change (m.coordinate (ew (ρ (π g) v).toMul)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q (inclusion hJX g)) (m.coordinate (ew v.toMul)).toAdd
    rw [←hq (inclusion hJX g) (ew v.toMul)]
    apply congrArg (fun w : V => (m.coordinate w).toAdd)
    apply Subtype.ext
    change ((ρ (π g) v).toMul.val : G) = g.val * (v.toMul.val : G) * g.val⁻¹
    exact congrArg Subtype.val (NormalElementaryQuotient.representation_apply W π
      (LargeDistance.CubicEven.projection_surjective hms e hc.2.1 hk)
      (CubicAction.moved_projection_kernel hms e hc.2.1 hk) g v)
  have hmodel := LargeDistance.CubicFull.moved_subgroup_cover_model hms e hc.2.1 hk
  change BinaryPermutation.SixCover.IsNaturalOrCore ρ (MonoidHom.id _) at hmodel
  rcases hmodel with ⟨f,hf⟩ | ⟨f,hf⟩
  · have hd := (E.symm.trans f).finrank_eq
    rw [BinaryPermutation.finrank_core,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hd
    norm_num at hd
  · obtain ⟨s,hs⟩ := BinaryPermutation.SixCoreNormalizer.conjugate_of_core_intertwiner
      K qJ π hKq (CubicAction.component_image hms e hc.2.1 hk) (E.symm.trans f) (by
        intro g v
        change f (E.symm (BinaryPermutation.coreRepresentation (Fin 6) (qJ g) v)) = _
        have he : E.symm (BinaryPermutation.coreRepresentation (Fin 6) (qJ g) v) =
            ρ (π g) (E.symm v) := by
          apply E.injective
          rw [E.apply_symm_apply,hE,E.apply_symm_apply]
        rw [he]
        exact hf (π g) (E.symm v))
    have hπ : π = (MulAut.conj s).toMonoidHom.comp qJ := MonoidHom.ext hs
    apply LargeDistance.CubicFull.point_image_impossible hms e hc.2.1 hk (s * a.val)
    change (B.subgroupOf J).map π ≤ _
    rw [hπ,←map_map,hBqJ,map_map]
    have he : (MulAut.conj s).toMonoidHom.comp (MulAut.conj a.val).toMonoidHom =
        (MulAut.conj (s*a.val)).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change s * (a.val*x*a.val⁻¹) * s⁻¹ = (s*a.val)*x*(s*a.val)⁻¹
      group
    rw [he]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
