module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.CoreFixed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.Source
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.NormalElementaryQuotient.FullyMoved
public import Theory.Representation.NormalElementaryQuotient.FixedIndex

/-!
# Native edge bounds for the entire moved cover

The faithful natural central quotient identifies the centralizer of the whole
moved subgroup with the replacement two-core. Once the favorable orbit forces
the six-letter projection to be onto, the actual moved subgroup is either the
natural module or its augmentation cover, equivariantly for that projection.
The augmentation fixed-space bound gives an edge index at most eight in both
cases, without a natural subgroup complement.

The final theorem applies this bound to the literal selected OrderedOrbit.
The lower displacement bound, radical-derived containment and plane
intersection remain obligations of the distance-two exhaustion owner.
Source: MS93 (3.6), printed p.871; the whole-cover classification is
Aschbacher--Smith I.1.5--6.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
open LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h in
theorem moved_elementary : IsElementaryAbelian 2 (replacementMoved d) :=
  IsElementaryAbelian.of_le (replacementMoved_le_omegaCenter h d)

include h e hz hn in
/-- The entire moved subgroup has exactly the replacement two-core as its
centralizer, as detected by the faithful natural central quotient. -/
theorem moved_centralizer :
    centralizer (replacementMoved d : Set d.overgroup) = pCore 2 d.overgroup := by
  apply le_antisymm
  · intro g hg
    rw [←replacementAction_kernel h e hz hn d]
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    have hfix : (w : d.overgroup) = g * w * g⁻¹ := by
      rw [←hg w w.property,mul_inv_cancel_right]
    have he := coverProjection_conjugate h e hz hn d g w w hfix
    have hv : (coverProjection h e hz hn d w).toAdd = v :=
      congrArg Multiplicative.toAdd hw
    rw [hv] at he
    exact he.symm
  · intro g hg w hw
    exact (((mem_omegaCenterIn_iff _ _).mp
      (replacementMoved_le_omegaCenter h d hw)).2.1 g hg).symm

include h e hz hn in
private theorem source_onto
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    Function.Surjective (Recognition.sourceProjection h e hz hn d) := by
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hb
  let a := PairEstimates.earlyPair (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) hl hb hlarge o
  let := a.quotient_elementary
  exact (PairEstimates.sourceImageModel h e hz hn d a).onto
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)

include h e hz hn in
/-- Construct natural-or-augmentation coordinates on the whole moved cover
for the literal six-letter projection; the component fixed line is retained. -/
theorem moved_cover_model
    (hq : Function.Surjective (Recognition.sourceProjection h e hz hn d)) :
    letI := replacementMoved_normal h d
    letI := moved_elementary h d
    let q := Recognition.sourceProjection h e hz hn d
    let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
    SixCover.IsNaturalOrCore
      (NormalElementaryQuotient.representation (replacementMoved d) q hq hk)
      (MonoidHom.id (Equiv.Perm (Fin 6))) := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let K := replacementComponent d
  let q := Recognition.sourceProjection h e hz hn d
  let hk : q.ker = centralizer (W : Set d.overgroup) :=
    (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let p : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
    (coverProjection h e hz hn d).toAdditiveLeft.toZModLinearMap 2
  have hp : ∀ g v, p (ρ g v) = naturalRepresentation (Fin 6) g (p v) := by
    intro g v
    obtain ⟨x,rfl⟩ := hq g
    have hw := NormalElementaryQuotient.representation_apply W q hq hk x v
    have he := coverProjection_conjugate h e hz hn d x v.toMul (ρ (q x) v).toMul hw
    change p (ρ (q x) v) = replacementAction h e hz hn d x (p v) at he
    rw [Recognition.sourceProjection_action]
    exact he
  have hsur : Function.Surjective p := by
    intro v
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w,congrArg Multiplicative.toAdd hw⟩
  have hK : K.map q = alternatingGroup (Fin 6) := by
    change ((L.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map q = alternatingGroup (Fin 6)
    rw [←replacement_residual h d]
    exact Recognition.sourceProjection_component h e hz hn d
  have hfix : p.ker ≤ fixedSpace ρ (alternatingGroup (Fin 6)) := by
    intro v hv a
    obtain ⟨k,hkK,he⟩ := hK.ge a.property
    change ρ a.val v = v
    rw [←he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    have hvc : v.toMul ∈ (coverProjection h e hz hn d).ker := hv
    rw [coverProjection_kernel] at hvc
    exact mul_inv_eq_iff_eq_mul.mpr (hvc k hkK)
  have hWK : W ≤ K := by
    let := h.relative_normal
    intro w hw
    exact commutator_le_right (centralOmega L R) (L.subgroupOf (L ⊔ R)) hw
  have hc := NormalElementaryQuotient.coinvariants_image_eq_top W q hq hk K hWK
    (replacementMoved_idempotent h d)
  rw [hK] at hc
  have hgen : subspaceCommutator ρ ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
    rw [subspaceCommutator_top_eq_coinvariants]
    exact hc
  exact SixCover.naturalOrCore_symmetric ρ (MulEquiv.refl _) (alternatingGroup (Fin 6))
    (by simp) p hp hsur hfix hgen

include h e hz hn in
/-- The native edge index is at most eight on the whole central cover.
Local calculations are the authorized input to the favorable orbit selection. -/
theorem native_edge_index_le_eight
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    (omegaCenter d.radical).relIndex
      (replacementMoved d ⊔ omegaCenter d.radical) ≤ 8 := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let q := Recognition.sourceProjection h e hz hn d
  have hq := source_onto h e hz hn d hl hb hlarge
  let hk : q.ker = centralizer (W : Set d.overgroup) :=
    (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let A := d.radical.map q
  have hcod : fixedCodim ρ A ≤ 3 := by
    have hc := core_fixedCodim_le_three A ((replacement_radical_isPGroup h d).map q)
    rcases moved_cover_model h e hz hn d hq with ⟨E,hE⟩ | ⟨E,hE⟩
    · let f := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
      have hf : Function.Surjective f := E.symm.surjective.comp coreToNatural_surjective
      have he : ∀ g v, f (coreRepresentation (Fin 6) g v) = ρ g (f v) := by
        intro g v
        apply E.injective
        rw [hE]
        change E (E.symm (coreToNatural (Fin 6) (coreRepresentation (Fin 6) g v))) =
          naturalRepresentation (Fin 6) g (E (E.symm (coreToNatural (Fin 6) v)))
        rw [E.apply_symm_apply,E.apply_symm_apply,coreToNatural_equivariant]
      exact (fixedCodim_le_of_equivariant_surjection
        (coreRepresentation (Fin 6)) ρ f hf he A).trans hc
    · have he : ∀ g v, E.symm (coreRepresentation (Fin 6) g v) = ρ g (E.symm v) := by
        intro g v
        apply E.injective
        rw [E.apply_symm_apply,hE,E.apply_symm_apply]
        rfl
      exact (fixedCodim_le_of_equivariant_surjection
        (coreRepresentation (Fin 6)) ρ E.symm.toLinearMap E.symm.surjective he A).trans hc
  have hWI : W ≤ d.radical := fun w hw =>
    replacement_core_le_radical h d
      ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hw)).1
  have he : (omegaCenter d.radical).subgroupOf W =
      (centralizer (d.radical : Set d.overgroup)).subgroupOf W := by
    ext w
    change (w : d.overgroup) ∈ omegaCenter d.radical ↔
      (w : d.overgroup) ∈ centralizer (d.radical : Set d.overgroup)
    rw [mem_omegaCenter_iff]
    exact ⟨fun hw => hw.2.2,fun hw => ⟨hWI w.property,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) _ w.property,hw⟩⟩
  have hind : (omegaCenter d.radical).relIndex (W ⊔ omegaCenter d.radical) =
      (omegaCenter d.radical).relIndex W := by
    let S := W ⊔ omegaCenter d.radical
    have hn : W ≤ normalizer (omegaCenter d.radical : Set d.overgroup) := by
      apply le_normalizer_iff_commutator_le_right.mpr
      apply le_trans _ bot_le
      apply le_bot_iff.mpr
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw z hz
      exact ((mem_omegaCenter_iff.mp hz).2.2 w (hWI hw)).symm
    let : ((omegaCenter d.radical).subgroupOf S).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le hn (omegaCenter d.radical).le_normalizer)
    have hh := relIndex_sup_right (W.subgroupOf S) ((omegaCenter d.radical).subgroupOf S)
    rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
      relIndex_subgroupOf le_sup_left] at hh
    exact hh
  rw [hind]
  change ((omegaCenter d.radical).subgroupOf W).index ≤ 8
  rw [he]
  change (centralizer (d.radical : Set d.overgroup)).relIndex W ≤ 8
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim W q hq hk]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hcod : 2 ^ fixedCodim ρ A ≤ 2 ^ 3)

include h e hz hn in
/-- Apply the proved upper edge bound to the actual favorable orbit. Only the
native lower bound and the existing local image/intersection clauses remain. -/
theorem exists_orderedOrbit_with_full_movement_of_native_lower
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (h4 : 4 ≤ (omegaCenter d.radical).relIndex
      (⁅d.radical,replacementMoved d⁆ ⊔ omegaCenter d.radical))
    (hinter : ∀ c b, CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl) →
      Adjacent d.radical (alpha d.radical) b → Adjacent d.radical c b →
      ⁅Q d.radical (alpha d.radical),
        Z d.radical c ⊓ Q d.radical (alpha d.radical)⁆ ≤ Z d.radical b) :
    ∃ o : OrderedOrbit (replacementGeometry h d),
      criticalPlane d.radical o.c o.b ≤
        ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ ⊔
          Z d.radical (alpha d.radical) ∧
      criticalOrbitNative d.radical o.c o.b =
        ⁅pResidual 2 d.overgroup,criticalOrbitNative d.radical o.c o.b⁆ ⊔
          orbitLayer d.radical :=
  exists_orderedOrbit_with_full_movement h e hz d hl hb hlarge hn hder
    (native_edge_index_le_eight h e hz hn d hl hb hlarge) h4 hinter

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
