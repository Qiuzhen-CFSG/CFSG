module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.LocalResidues
public import Theory.SpecificGroups.BinaryLinear.LineRadicalNormalizer
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeMiddleQuotient
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeMiddleResidue

/-!
# The actual middle residue in the abelian binary branch

Central duality gives [O₂(H):C_O₂(H)(V₃)] = 4. Together with the two
Sylow indices, this forces O₂(LT) to escape O₂(H). If its nontrivial
natural image lay in the opposite point radical, the line-radical
normalizer theorem would make L₁T preserve V₂, contrary to irreducibility.
Thus O₂(LT) also escapes O₂(N_H(V₂)), without a nonabelian V_H premise.

The literal plane action and the point-edge quotient now give
J/O₂(J) ≃ S₃ × S₃ for J = O²(C_K(V₂)) O²(N_L(V₂)) T. Both actual
edge indices are three and their intersection is T; the maximal-overgroup
calculation gives distinctness, maximality and exhaustion for this residue.
These results discharge the remaining local inputs of C3System.
Source: Aschbacher–Smith 13.7.6(1), printed p.940, and 13.8.19, p.953.
-/

public noncomputable section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem source_binary_seed_centralizer_index
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    (centralizer (V₃ : Set G)).relIndex (Source.QH H) = 4 := by
  have h := c.f9 H c.component.local_overgroup
  obtain ⟨hE,ρ,sU,sQ,hpair,_⟩ := Section07.source_central_duality (localNaturalSetup c.localSetup) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  let := hE
  change (centralizer (V₃ : Set G)).relIndex (H.pCoreIn 2) = 4
  rw [sU.centralizer_index_of_dual_pairing sQ hpair V₃ (le_conjugateSpanBy V₃ H),
    sU.imageSpace_card_eq_relIndex V₃ (le_conjugateSpanBy V₃ H)]
  change (Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)).relIndex V₃ = 4
  rw [source_binary_fixed_core c act e₀]
  have hc := (V₁.subgroupOf V₃).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (c.localSetup.line_le_plane.trans c.localSetup.plane_le_seed)).toEquiv,
    c.localSetup.line_card,c.localSetup.seed_card] at hc
  change 2 * V₁.relIndex V₃ = 8 at hc
  omega

theorem source_binary_local_core_not_le_core
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ Source.QH H := by
  intro hsmall
  have h := c.f9 H c.component.local_overgroup
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQC : Q ≤ centralizer (V₃ : Set G) :=
    (h.sylow_centralizer.symm.le.trans inf_le_right).trans (centralizer_le c.localSetup.seed_le)
  have h4 := relIndex_le_of_le_left (L := Source.QH H) hQC (Q.subgroupOf (Source.QH H)).index_ne_zero_of_finite
  rw [source_binary_seed_centralizer_index c act e₀] at h4
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  have hi : (Source.QH H).relIndex (T : Subgroup G) = 8 := by
    have he := relIndex_map_map_of_injective (pCore 2 H)
      ((T : Subgroup G).subgroupOf H) H.subtype_injective
    rw [map_subgroupOf_eq_of_le hTH,←QuotientGroup.ker_mk' (pCore 2 H),relIndex_ker] at he
    let P := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
    rw [QuotientGroup.ker_mk'] at he
    change (Source.QH H).relIndex (T : Subgroup G) = Nat.card P at he
    rw [he,P.card_eq_multiplicity,Nat.card_congr e₀.toEquiv,Matrix.PSL3Two.card_PSL]
    decide +kernel
  have hm := relIndex_mul_relIndex Q (Source.QH H) (T : Subgroup G) hsmall h.QH_le_T
  rw [hi] at hm
  have hb := source_local_core_index_le_sixteen c
  change Q.relIndex (T : Subgroup G) ≤ 16 at hb
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open TransvectionParabolic.Marking
open Geometry.CoveredProduct.ResidualPlacement
open Section07.OrdinarySource.LinearThreeC3Local
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem source_binary_local_core_escape
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (H ⊓ normalizer (V₂ : Set G)).pCoreIn 2 := by
  let d := localNaturalSetup c.localSetup
  have h := c.f9 H c.component.local_overgroup
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  obtain ⟨eH,eK,eV,heK,heV⟩ := source_binary_component_coordinates c act e₀ hKH
  let ρ := act.representation
  have hρ : IsConjugation H V₃ V₁ ρ := act.conjugation
  intro hsmall
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let F := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H
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
  have hRne : R ≠ ⊥ := by
    intro hz
    apply source_binary_local_core_not_le_core c act e₀
    intro x hx
    have hm : q ⟨x,hQH hx⟩ ∈ R := mem_map_of_mem q hx
    rw [hz,mem_bot] at hm
    have he : QuotientGroup.mk' (pCore 2 H) ⟨x,hQH hx⟩ = 1 :=
      eH.injective (hm.trans (map_one eH).symm)
    exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp he)
  have hnormal : (P.subgroupOf H).map q ≤ normalizer (R : Set _) :=
    (map_mono ((comap_mono hPQ).trans (le_normalizer_comap H.subtype))).trans (le_normalizer_map q)
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := Section07.ModelExclusions.plane_section_finrank d (H := H)
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
    apply Section07.ModelExclusions.point_stabilizer_preimage_eq_plane_normalizer d le_rfl ρ hρ
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
  have hnorm : normalizer (R : Set _) ≤ S := by
    rw [hS]
    exact BinaryLinear.LineRadical.normalizer_le_parabolic_of_nontrivial_subgroup w hw R hRrad hRne
  have hPpre : P.subgroupOf H ≤ S.comap q := by
    intro a ha
    have hm := hnormal (mem_map_of_mem q ha)
    exact hnorm hm
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

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open TransvectionParabolic.Marking
open Geometry.CoveredProduct.ResidualPlacement
open Section07.OrdinarySource.LinearThreeC3Local
open Section05.PlaneGeometry.TwoBlocks Section05.AmbientSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem source_plane_noncentral
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
  intro hz
  have hX : one L T V₁ ≤ G₁ := by
    rw [c.localSetup.first_normalizer]
    exact (one_le L (T : Subgroup G) V₁).trans inf_le_right
  have hnorm : one L T V₁ ≤ normalizer (G₁.pCoreIn 2 : Set G) :=
    hX.trans (G₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image G₁ (pCore 2 G₁)))
  have hc : V₂ ≤ centralizer (G₁.pCoreIn 2 : Set G) := by
    rw [c.localSetup.first_normalizer]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  apply c.noncentral_core
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [←Section07.ModelExclusions.plane_orbit_point_residual (localNaturalSetup c.localSetup)]
  exact conjugateSpanBy_le hc (hnorm.trans (normalizer_le_normalizer_centralizer _))

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem source_binary_middle_quotient
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    Nonempty ((middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let d := localNaturalSetup c.localSetup
  have hF9 := c.f9 H c.component.local_overgroup
  have hH := c.component.local_overgroup
  have hm := source_plane_noncentral c
  let := source_plane_isKleinFour d
  obtain ⟨eL⟩ := source_binary_local_ordinary c e₀
  obtain ⟨hA,⟨eA⟩⟩ := source_binary_point_parabolic c act e₀
  let A := pointResidual K V₂ ⊔ (T : Subgroup G)
  let X := planeActor (L := L) (V₂ := V₂)
  let J := A ⊔ X
  let N := normalizer (V₂ : Set G)
  have hJM : J = middle T L K V₂ := by dsimp [J,A,X,middle]; ac_rfl
  have hJN : J ≤ N := hJM ▸ middle_le_plane_normalizer d
  have hAX : A ≤ normalizer (X : Set G) :=
    (show A ≤ J from le_sup_left).trans (hJM ▸ middle_normalizes_planeActor d eL hm)
  have hAH : A ≤ H := hA.le.trans inf_le_left
  let f : A →* Equiv.Perm (Fin 3) := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker = pCore 2 A := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ eA.injective,QuotientGroup.ker_mk']
  have hf2 : IsPGroup 2 f.ker := hfk ▸ pCore_isPGroup
  have hHC : H ≤ centralizer (V₁ : Set G) :=
    (hH.2.1.trans d.first_normalizer.le).trans (normalizer_le_centralizer_of_card_two V₁ d.line_card)
  have hXA2 : IsPGroup 2 (X.subgroupOf A) := by
    apply (planeActor_inf_H_isTwoGroup d eL hHC).comap_subtype.to_le
    intro a ha
    exact ⟨ha,hAH a.property⟩
  have hXA : X.subgroupOf A ≤ f.ker := by
    rw [hfk]
    let : (X.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAX
    exact le_sSup ⟨inferInstance,hXA2⟩
  let g : J →* Equiv.Perm (Fin 3) := (planeAction V₂).comp (inclusion hJN)
  have hg : Function.Surjective g := by
    let P := planeLocal (L := L) (V₂ := V₂)
    let r : P →* Equiv.Perm (Fin 3) := (planeAction V₂).comp (inclusion (show P ≤ N from inf_le_right))
    obtain ⟨q,hq,_,hfix⟩ := Ordinary.exists_planeLocal_quotient d eL
    have hrk : r.ker = q.ker := by
      ext a
      exact (planeAction_eq_one V₂ (inclusion (show P ≤ N from inf_le_right) a)).trans (hfix a).symm
    have hr : Function.Surjective r := by
      apply MonoidHom.range_eq_top.mp
      apply r.range.eq_top_of_card_eq
      rw [←index_ker,hrk,index_ker,MonoidHom.range_eq_top.mpr hq,card_top]
    have hPJ : P ≤ J := by
      have hPB : P ≤ X ⊔ (T : Subgroup G) := by
        rw [planeActor_sup_sylow d]
        exact inf_le_inf_right N le_sup_left
      exact hPB.trans (sup_le le_sup_right (le_sup_right.trans le_sup_left))
    intro b
    obtain ⟨a,ha⟩ := hr b
    exact ⟨inclusion hPJ a,ha⟩
  have hXg : IsPGroup 2 (X.subgroupOf J ⊓ g.ker : Subgroup J) := by
    have he : X.subgroupOf J ⊓ g.ker = (X ⊓ centralizer (V₂ : Set G)).subgroupOf J := by
      ext a
      exact and_congr_right (fun _ => planeAction_eq_one V₂ (inclusion hJN a))
    rw [he]
    exact (Ordinary.planeActor_action_source d eL).2.comap_subtype
  have hXcard : Nat.card ((X.subgroupOf J).map g) = 3 := by
    have he : (X.subgroupOf J).map g = (X.subgroupOf N).map (planeAction V₂) := by
      ext b
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨inclusion hJN a,ha,rfl⟩
      · rintro ⟨a,ha,rfl⟩
        exact ⟨⟨a.val,(show X ≤ J from le_sup_right) ha⟩,ha,rfl⟩
    rw [he]
    exact (Ordinary.planeActor_action_source d eL).1
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := hF9.sylow_centralizer.symm.le.trans inf_le_left
  have hQg : Q.subgroupOf J ≤ g.ker := by
    intro a ha
    exact (planeAction_eq_one V₂ (inclusion hJN a)).mpr
      (centralizer_le (d.plane_le_seed.trans d.seed_le)
        (hF9.sylow_centralizer.symm.le ha).2)
  have hQf : ¬ Q.subgroupOf A ≤ f.ker := by
    intro hh
    rw [hfk] at hh
    have hmapped := map_mono (f := A.subtype) hh
    rw [map_subgroupOf_eq_of_le (hQT.trans le_sup_right)] at hmapped
    apply source_binary_local_core_escape c act e₀
    rwa [←hA]
  have hh := symmetricThree_product_quotient_of_local_maps A X hAX f hf hf2 hXA
    g hg hXg hXcard Q (isPGroup_pCoreIn 2 _) hQg hQf
  change Nonempty ((J ⧸ pCore 2 J) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) at hh
  rwa [hJM] at hh


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

public noncomputable section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition Component
open TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
open Section07.OrdinarySource.LinearThreeC3Local
open Section07.OrdinarySource.LinearThreeMiddleResidue
open Section07.OrdinarySource.LinearThreeFamily Quasithin.I5
open Section05.PlaneGeometry.TwoBlocks
open CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem sylow_index_core_card (S : Sylow 2 G) :
    S.index * 2 ^ (Nat.card (G ⧸ pCore 2 G)).factorization 2 =
      Nat.card (G ⧸ pCore 2 G) := by
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hi : P.index = S.index := (S : Subgroup G).index_map_eq
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
  have hc := (P : Subgroup (G ⧸ pCore 2 G)).index_mul_card
  rw [P.card_eq_multiplicity,hi] at hc
  exact hc

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem source_binary_family_middle_parabolics
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    let F := family (L ⊔ (T : Subgroup G)) (middle T L K V₂) H
    RankTwoParabolics (F 1) ((chamberSubgroup F).subgroupOf (F 1))
      (localParabolic F 1 0) (localParabolic F 1 2) := by
  let d := localNaturalSetup c.localSetup
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hm := source_plane_noncentral c
  have hc := source_binary_chamber c e₀
  obtain ⟨eJ⟩ := source_binary_middle_quotient c act e₀
  let J := middle T L K V₂
  let A := L ⊔ (T : Subgroup G)
  let P := planeActor (L := L) (V₂ := V₂) ⊔ (T : Subgroup G)
  let R := pointResidual K V₂ ⊔ (T : Subgroup G)
  let Ω := A ⊔ H
  have hTJ : (T : Subgroup G).relIndex J = 9 := middle_sylow_index eJ
  obtain ⟨eL⟩ := source_binary_local_ordinary c e₀
  have hTP : (T : Subgroup G).relIndex P = 3 := plane_edge_sylow_index d eL hm
  obtain ⟨_,⟨eR⟩⟩ := source_binary_point_parabolic c act e₀
  have hTR : (T : Subgroup G).relIndex R = 3 := by
    have hi := sylow_index_core_card (T.subtype (show (T : Subgroup G) ≤ R from le_sup_right))
    have hcard : Nat.card (R ⧸ pCore 2 R) = 6 := by
      rw [Nat.card_congr eR.toEquiv,Nat.card_perm,Nat.card_fin]
      decide +kernel
    rw [hcard] at hi
    norm_num [show (Nat.factorization 6) 2 = 1 from by decide +kernel] at hi
    change (T : Subgroup G).relIndex R * 2 = 6 at hi
    omega
  have hPJ : P ≤ J := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hRJ : R ≤ J := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hP : (A.subgroupOf J).index = 3 := by
    have hi := relIndex_mul_relIndex (T : Subgroup G) P J le_sup_right hPJ
    rw [hTP,hTJ] at hi
    change A.relIndex J = 3
    rw [←inf_relIndex_right,inf_comm A J,middle_inf_local d]
    change P.relIndex J = 3
    omega
  have hR : (H.subgroupOf J).index = 3 := by
    have hi := relIndex_mul_relIndex (T : Subgroup G) R J le_sup_right hRJ
    rw [hTR,hTJ] at hi
    change H.relIndex J = 3
    rw [←inf_relIndex_right,inf_comm H J,source_binary_middle_inf_H c act e₀]
    change R.relIndex J = 3
    omega
  have hJΩ : J ≤ Ω := middle_le_generated hKH
  have hinter : A.subgroupOf J ⊓ H.subgroupOf J = (T : Subgroup G).subgroupOf J := by
    ext x
    have hx := congrArg (fun U : Subgroup Ω => (⟨x,hJΩ x.prop⟩ : Ω) ∈ U) hc
    simpa [chamberSubgroup,family,Fin.forall_fin_succ,mem_subgroupOf,A,show x.val ∈ middle T L K V₂ from x.prop] using Iff.of_eq hx
  have hres : RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      (A.subgroupOf J) (H.subgroupOf J) := by
    apply rankTwo_of_prime_indices _ _ _
      (hasTwoMaximalOvergroups_quotient (pCore 2 J) pCore_isPGroup eJ
        hasTwoMaximalOvergroups_product (T.subtype sylow_le_middle))
    · rw [hP]; exact Nat.prime_three
    · rw [hR]; exact Nat.prime_three
    · exact hinter
    · change Nat.card ((T : Subgroup G).subgroupOf J) < Nat.card (A.subgroupOf J)
      have hb := ((T : Subgroup G).subgroupOf J).card_mul_index
      have hp := (A.subgroupOf J).card_mul_index
      change Nat.card ((T : Subgroup G).subgroupOf J) * (T : Subgroup G).relIndex J = Nat.card J at hb
      rw [hTJ] at hb
      rw [hP] at hp
      have hpos := Nat.card_pos (α := (T : Subgroup G).subgroupOf J)
      omega
  dsimp only
  rw [hc]
  exact rankTwo_subgroupOf J A H (T : Subgroup G) Ω hJΩ hres


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
