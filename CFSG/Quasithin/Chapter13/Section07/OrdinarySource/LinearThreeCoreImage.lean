module
public import CFSG.Quasithin.Chapter13.Section07.CoreImage
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeSource
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.LineCoreCard
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Displacement
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeParabolic
public import Theory.SpecificGroups.BinaryLinear.LineRadical
public import Theory.SpecificGroups.BinaryLinear.ThreePointQuotient
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The independent core image in the original binary C₃-system

The natural S₆ action gives [T:O₂(LT)] = 16. The binary three-dimensional
H-action gives [T:O₂(H)] = 8, while the original point-core calculation
has [O₂(H):O₂(H) ∩ O₂(LT)] = 8. Thus the literal image of O₂(LT) in H*
has order four.

That image is normalized by L₁T. If it lay in the two-core of N_H(V₂),
the marked natural three-space would identify it with the four-element
radical fixing V₂/V₁. Its normalizer is the point stabilizer, forcing L₁T
to preserve V₂, contrary to its irreducibility on V₃/V₁. Therefore the
original core has nontrivial image in the S₃ quotient of K₀T=N_H(V₂).
It centralizes V₂, so this supplies the independent first-factor action
needed by the middle vertex, with the literal subgroups retained.

The final source application constructs the full natural action and the
seed noncentrality from the existing binary-three branch and original
plane noncentrality. No independent-factor or parabolic-recognition
hypothesis is added.

Source: Aschbacher--Smith, 13.7.6(1), printed p.940, using 13.5.4(5),
F.9.1 irreducibility and the point-core calculation of 13.7.9(1).
-/

public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

omit [Finite G] in
private theorem starImage_card_eq_core_relIndex (A : Subgroup G) (hAH : A ≤ H) :
    Nat.card (Section08.Source.starImage H A) = (H.pCoreIn 2).relIndex A := by
  have hh := relIndex_map_map_of_injective (pCore 2 H) (A.subgroupOf H) H.subtype_injective
  rw [map_subgroupOf_eq_of_le hAH,←QuotientGroup.ker_mk' (pCore 2 H),relIndex_ker] at hh
  simpa only [QuotientGroup.ker_mk', Section08.Source.starImage, pCoreIn] using hh.symm

/-- The original full S₆ action has a Sylow subgroup of order sixteen. -/
theorem source_local_core_sylow_index_sixteen
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (T : Subgroup G) = 16 := by
  rw [core_relIndex_eq_image_card d h (T : Subgroup G) le_rfl]
  let S := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).mapSurjective
    (nonabelian_permutation_surjective d h hU hV)
  change Nat.card S = 16
  rw [S.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
  decide +kernel

/-- The two original core-index towers give an image of order four in H*. -/
theorem linear_three_local_core_image_card
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,Section08.Source.QH H⁆ ≠ ⊥)
    (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 3 → ZMod 2)) :
    Nat.card (Section08.Source.starImage H ((L ⊔ (T : Subgroup G)).pCoreIn 2)) = 4 := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let QH := H.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := h.sylow_centralizer.symm.le.trans inf_le_left
  have hQHT : QH ≤ (T : Subgroup G) := h.QH_le_T
  have hq : Q.relIndex (T : Subgroup G) = 16 := source_local_core_sylow_index_sixteen d h hU hV
  have hh : QH.relIndex (T : Subgroup G) = 8 := by
    change (H.pCoreIn 2).relIndex (T : Subgroup G) = 8
    rw [←starImage_card_eq_core_relIndex (H := H) (T : Subgroup G) h.T_le_H]
    let S := (T.subtype h.T_le_H).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
    change Nat.card S = 8
    rw [S.card_eq_multiplicity,Nat.card_congr eH.toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).toEquiv,
      Matrix.PSL3Two.card_SL]
    decide +kernel
  have hqh : Q.relIndex QH = 8 := by
    rw [core_relIndex_eq_image_card d h QH hQHT]
    change Nat.card (((Section08.Source.QH H).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d)) = 8
    rw [nonabelian_core_image d h hU hV hne]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.line_core_card _
      (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
  have h₁ := relIndex_inf_mul_relIndex Q QH (T : Subgroup G)
  have h₂ := relIndex_inf_mul_relIndex QH Q (T : Subgroup G)
  rw [inf_eq_left.mpr hQHT,hqh,hh] at h₁
  rw [inf_eq_left.mpr hQT,hq,inf_comm QH Q,←h₁] at h₂
  change Nat.card (Section08.Source.starImage H Q) = 4
  rw [starImage_card_eq_core_relIndex (H := H) Q (hQT.trans h.T_le_H)]
  change QH.relIndex Q = 4
  omega

/-- The original core escapes the two-core of the opposite marked parabolic. -/
theorem linear_three_local_core_not_le_plane_core
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,Section08.Source.QH H⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (heV : ∀ a v, eV (ρ a v) = eH a (eV v)) :
    ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (H ⊓ normalizer (V₂ : Set G)).pCoreIn 2 := by
  intro hsmall
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let B := H ⊓ normalizer (V₂ : Set G)
  have hQT : Q ≤ (T : Subgroup G) := h.sylow_centralizer.symm.le.trans inf_le_left
  have hQH : Q ≤ H := hQT.trans h.T_le_H
  have hPH : P ≤ H := h.local_le
  have hPX : P ≤ X := sup_le
    ((map_subtype_le _).trans (inf_le_left.trans le_sup_left)) le_sup_right
  have hPQ : P ≤ normalizer (Q : Set G) := hPX.trans
    (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  let q := eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    have hker : q.ker = pCore 2 H := by
      dsimp only [q]
      rw [MonoidHom.ker_comp_of_injective _ _ eH.injective,QuotientGroup.ker_mk']
    rw [hker]
    exact pCore_isPGroup
  let R := (Q.subgroupOf H).map q
  have hcardR : Nat.card R = 4 := by
    change Nat.card ((Q.subgroupOf H).map (eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)))) = 4
    rw [←map_map,card_map_of_injective eH.injective]
    exact linear_three_local_core_image_card d h hU hV hne eH
  have hnormal : (P.subgroupOf H).map q ≤ normalizer (R : Set _) :=
    (map_mono ((comap_mono hPQ).trans (le_normalizer_comap H.subtype))).trans (le_normalizer_map q)
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := ModelExclusions.plane_section_finrank d (H := H)
    rw [hz,finrank_bot] at hh
    omega
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hP₂
  let w := eV u
  have hw : w ≠ 0 := fun hz => hu0 (eV.injective (hz.trans (map_zero eV).symm))
  let W := Submodule.span (ZMod 2) {w}
  let S := BinaryNaturalDual.VectorStabilizers.representationStabilizer (linearRepresentation 3) w
  have hS : S = BinaryLinear.parabolic W := by
    change MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) w = _
    exact BinaryLinear.PointStabilizerRank.stabilizer_eq_parabolic w
  have hpre : (S.comap q).map H.subtype = B := by
    apply ModelExclusions.point_stabilizer_preimage_eq_plane_normalizer d le_rfl ρ hρ
      (linearRepresentation 3) eH eV
    · intro a v
      exact heV _ _
    · exact hu
    · exact hu0
  have hBpre : B.subgroupOf H = S.comap q := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (show B ≤ H from inf_le_left),hpre]
  have hBimage : (B.subgroupOf H).map q = S := by
    rw [hBpre,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective q hq]
    exact le_top
  let : Finite (BinaryLinear.GL (Fin 3 → ZMod 2)) := Finite.of_injective
    (fun g : BinaryLinear.GL (Fin 3 → ZMod 2) => (g : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective
  have hRrad : R ≤ BinaryLinear.radical W := by
    have hm : R ≤ ((B.pCoreIn 2).subgroupOf H).map q :=
      map_mono (comap_mono (show Q ≤ B.pCoreIn 2 from hsmall))
    rw [←pCoreIn_subgroupOf 2 B H inf_le_left,
      map_pCoreIn_of_ker_isPGroup q hk,hBimage,hS] at hm
    exact hm.trans_eq (BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical W)
  have heR : R = BinaryLinear.radical W := by
    apply eq_of_le_of_card_ge hRrad
    rw [hcardR,BinaryLinear.LineRadical.card w hw]
    norm_num
  have hPpre : P.subgroupOf H ≤ S.comap q := by
    intro a ha
    have hm := hnormal (mem_map_of_mem q ha)
    rw [heR,BinaryLinear.normalizer_radical (mt Submodule.span_singleton_eq_bot.mp hw),←hS] at hm
    exact hm
  have hPN : P ≤ normalizer (V₂ : Set G) := by
    have hm := map_mono (f := H.subtype) hPpre
    rw [map_subgroupOf_eq_of_le hPH,hpre] at hm
    exact hm.trans inf_le_right
  rcases h.irreducible V₂ d.line_le_plane d.plane_le_seed hPN with he | he
  · change V₂ = V₁ at he
    have hc := d.plane_card
    rw [he,d.line_card] at hc
    omega
  · change V₂ = V₃ at he
    have hc := d.plane_card
    rw [he,d.seed_card] at hc
    omega
/-- The literal original binary-three branch supplies the independent core
image needed for the two S₃ factors of the middle C₃-system vertex. -/
theorem linear_three_core_escape_of_one_le
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    Nat.card (Section08.Source.starImage H ((L ⊔ (T : Subgroup G)).pCoreIn 2)) = 4 ∧
    ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      ((residual (K ⊓ centralizer (V₂ : Set G))) ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hne := seed_noncentral_on_local_core h hH.2.1
    (Section05.AmbientSource.source_seed_noncentral_of_plane_noncentral d hm)
  obtain ⟨eH,eV,_,heV⟩ :=
    ModelExclusions.linear_three_full_action_of_one_le d hH h hKH hK hL₁K ρ hρ eK hs
  refine ⟨linear_three_local_core_image_card d h hU hV hne eH,?_⟩
  rw [(ModelExclusions.linear_three_point_parabolic_of_one_le d hH h hKH hK hL₁K ρ hρ eK hs).1]
  exact linear_three_local_core_not_le_plane_core d h hU hV hne ρ hρ eH eV heV

end CFSG.Quasithin.Chapter13.Section07
