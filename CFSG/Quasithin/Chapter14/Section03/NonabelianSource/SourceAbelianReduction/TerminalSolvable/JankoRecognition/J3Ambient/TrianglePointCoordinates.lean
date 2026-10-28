module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TrianglePointComplement
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingCentralModule
public import Theory.GroupTheory.SplitExtensionGivenComplement
public import Theory.Representation.BinaryAlternatingFiveExtension.TriangleTranslation

/-!
# Coordinates retaining the literal point section

The chosen complement already contains the actual point section. Its split
coordinates retain that same complement. Conjugating the alternating quotient
places the order-twelve image at the standard point stabilizer; the full core
image remains the complete translation group. Thus both original subgroups
are marked in a single affine model, ready for the pair-inverter correction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open BinaryPermutation.AlternatingFiveExtension
open BinaryPermutation.AlternatingFiveBorel

variable {G : Type*} [Group G] [Finite G]

set_option maxHeartbeats 800000 in
/-- One affine marking sends the full original core image to translations
and the actual point section to the standard four-point actor subgroup. -/
theorem literal_triangle_point_coordinates
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    let f := j SingerField.fieldElement
    let H := Janko23.involutionCentralizer f
    let q := QuotientGroup.mk' (center H)
    ∃ E : (H ⧸ center H) ≃* TriangleTranslation.Model,
      ((Janko23.localCore f).map q).map E.toMonoidHom =
        (SemidirectProduct.inl : V →* TriangleTranslation.Model).range ∧
      (((j.range ⊓ H).subgroupOf H).map q).map E.toMonoidHom =
        B.map (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model) := by
  let f := j SingerField.fieldElement
  let H := Janko23.involutionCentralizer f
  let Q := Janko23.localCore f
  let X := (j.range ⊓ H).subgroupOf H
  let q := QuotientGroup.mk' (center H)
  let U := X.map q
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨⟨eQ⟩,_,⟨eA⟩⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  obtain ⟨_hZ,K,hK,hUK,_hpre⟩ := literal_triangle_point_complement P hc A C a j hj
  obtain ⟨_hZ,_hcZ,_hcQ,hUc,hd,_hi,_hcomp⟩ :=
    literal_triangle_quotient_splitting P hc A C a j hj
  obtain ⟨_d,p,hp,_hrep,hpker,eV,_hVrep,heV⟩ :=
    MinusExtraspecial.AlternatingCentralModule.exists_marked_module Q eQ
      (centralizer_generalizedFitting_le H) eA
  have hK' : p.ker.IsComplement' K := hpker.symm ▸ hK
  obtain ⟨E₀,hEr,hEv,hEk,_hEK⟩ := exists_marked_semidirect_equiv_of_given_complement
    p hp eV TriangleTranslation.action (fun w v => heV w v) K hK'
  have hU₀ : U.map E₀.toMonoidHom = (U.map p).map
      (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model) := by
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨p u,mem_map_of_mem p hu,(hEk ⟨u,hUK hu⟩).symm⟩
    · rintro ⟨d,⟨u,hu,rfl⟩,rfl⟩
      exact ⟨u,hu,hEk ⟨u,hUK hu⟩⟩
  have hV₀ : p.ker.map E₀.toMonoidHom =
      (SemidirectProduct.inl : V →* TriangleTranslation.Model).range := by
    ext z
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨eV ⟨v,hv⟩,(hEv ⟨v,hv⟩).symm⟩
    · rintro ⟨v,rfl⟩
      exact ⟨eV.symm v,(eV.symm v).property,
        (hEv (eV.symm v)).trans (congrArg SemidirectProduct.inl (eV.apply_symm_apply v))⟩
  have hUi : Function.Injective (p.subgroupMap U) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp (hpker.symm ▸ hd) (congrArg Subtype.val hx) x.property
  have hD : Nat.card (U.map p) = 12 :=
    (Nat.card_congr (MulEquiv.ofBijective (p.subgroupMap U)
      ⟨hUi,p.subgroupMap_surjective U⟩).toEquiv).symm.trans hUc
  obtain ⟨g,hg⟩ := MinusExtraspecial.PointComplementRetention.twelve_conjugate_borel (U.map p) hD
  let c := MulAut.conj (SemidirectProduct.inr g : TriangleTranslation.Model)
  let E := E₀.trans c
  have hmap (L : Subgroup (H ⧸ center H)) : L.map E.toMonoidHom =
      (L.map E₀.toMonoidHom).map c.toMonoidHom := by
    change L.map (c.toMonoidHom.comp E₀.toMonoidHom) = _
    exact (map_map L c.toMonoidHom E₀.toMonoidHom).symm
  refine ⟨E,?_,?_⟩
  · rw [hmap,←hpker,hV₀,SemidirectProduct.range_inl_eq_ker_rightHom]
    exact Subgroup.Normal.map_conj_eq _ _
  · change U.map E.toMonoidHom = _
    rw [hmap,hU₀,map_map]
    have hm : c.toMonoidHom.comp
        (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model) =
        (SemidirectProduct.inr : alternatingGroup (Fin 5) →* TriangleTranslation.Model).comp
          (MulAut.conj g).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change SemidirectProduct.inr g * SemidirectProduct.inr x *
        (SemidirectProduct.inr g : TriangleTranslation.Model)⁻¹ = SemidirectProduct.inr (g*x*g⁻¹)
      rw [map_mul,map_mul,map_inv]
    rw [hm,←map_map,hg]

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
