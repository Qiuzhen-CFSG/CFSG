module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OffenderEntrySource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryNormalizers
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryComponents
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Definitions
public import Theory.Representation.ElementaryPerfectSplit

/-!
# The ordinary selected component in the literal K L₊ T quotient

The faithful C-component selected by reductions (a–d) is normal in H by the
actual 13.3.2 and component-orbit argument. Its image B in G is therefore
normal in J=B L₊ T. The intrinsic module and quasisimple core quotient pass
through the original subtype, and J inherits SQTK from the prescribed point
normalizer H. These facts discharge the selected-component entry into B.5.

Only [B,J(T)]=B, the genuine earlier 3.1.8(3) generation input, remains explicit
beyond the existing selected-component data and 13.3.2. The second theorem
identifies the very W_K used by the ordinary diagonal consumer with the moved
subspace of the actual J/C_J(R₂(J)) action, preserving its elements in G
and intertwining the original J-conjugation action with the quotient action.
All nontrivial B.5 alternatives remain available for the subsequent row sieve.

Source: Aschbacher–Smith, 13.3.14(f–g), printed pp.892–893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterA.Section04
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full B.5 entry on the literal selected K L₊ T. Only Thompson generation
is retained beyond the existing faithful-component and 13.3.2 inputs. -/
theorem ordinary_selected_offender_entry
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : Section08.SourceCompletion.NaturalSetup T L V P E U M H)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hgen : ⁅K.map H.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map H.subtype) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    (B.subgroupOf J).map q ≤ N ∧
      IsComponent N (((B.subgroupOf J).map q).subgroupOf N) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp N.subtype) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hJH : J ≤ H := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  have hcH : (B.subgroupOf H).IsCComponent := by
    change ((K.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hcomp : (B.subgroupOf J).IsCComponent := hcH.subgroupOf_of_le hBJ hJH
  have hnH : (B.subgroupOf H).Normal := by
    have hn := ordinary_component_normal d h1332 K hK hf
    change ((K.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hJN : J ≤ normalizer (B : Set G) := hJH.trans
    ((normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hnH)
  let := hqK
  let eK : K ≃* B := K.equivMapOfInjective H.subtype H.subtype_injective
  have hqB : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))
  have hmB : intrinsicSignalizerModule B ≠ ⊥ :=
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T B).mp hf).2.2
  exact original_component_offender_entry d J B hJH hBJ hJN hcomp hqB hmB
    le_sup_right hgen

omit [Finite G] in
/-- Coordinates on the very moved module used by the ordinary diagonal consumer. -/
theorem localGroup_moved_coordinates (K A T : Subgroup G) :
    let J := Diagonal.localGroup K A T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let Wg := W.map J.subtype
    letI : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map J.subtype
    letI : IsElementaryAbelian 2 (Diagonal.movedModule K A T) :=
      IsElementaryAbelian.of_le
        (reduced_image_commutator_le J K (le_sup_left.trans le_sup_left))
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ e : Additive (Diagonal.movedModule K A T) ≃ₗ[ZMod 2]
        subspaceCommutator ρ ⊤ ((K.subgroupOf J).map q),
      ∀ w, (((e w).val.toMul : J) : G) = (w.toMul : G) :=
  ambient_reduced_moved_coordinates (Diagonal.localGroup K A T) K
    (le_sup_left.trans le_sup_left)

omit [Finite G] in
/-- The original local overgroup normalizes its reduced component commutator. -/
theorem reduced_image_commutator_normalized
    (J K : Subgroup G) (hKJ : K ≤ J) (hJK : J ≤ normalizer (K : Set G)) :
    J ≤ normalizer ((⁅(reducedTwoSubgroup J).map J.subtype,K⁆ : Subgroup G) : Set G) := by
  let K₀ := K.subgroupOf J
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hJK
  let A := ⁅reducedTwoSubgroup J,K₀⁆
  have hn := A.le_normalizer_map J.subtype
  simpa only [A,K₀,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype,map_commutator,
    map_subgroupOf_eq_of_le hKJ] using hn

omit [Finite G] in
/-- The literal W_K coordinates intertwine the actual J-conjugation action. -/
theorem localGroup_moved_coordinates_equivariant (K A T : Subgroup G)
    (hn : Diagonal.localGroup K A T ≤ normalizer (K : Set G)) :
    let J := Diagonal.localGroup K A T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let Wg := W.map J.subtype
    letI : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map J.subtype
    let WK := Diagonal.movedModule K A T
    letI : IsElementaryAbelian 2 WK := IsElementaryAbelian.of_le
      (reduced_image_commutator_le J K (le_sup_left.trans le_sup_left))
    let hJW := reduced_image_commutator_normalized J K (le_sup_left.trans le_sup_left) hn
    let σ := Representation.elementaryRepresentation (p := 2)
      (WK.normalizerMonoidHom.comp (inclusion hJW))
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ e : Additive WK ≃ₗ[ZMod 2] subspaceCommutator ρ ⊤ ((K.subgroupOf J).map q),
      (∀ w, (((e w).val.toMul : J) : G) = (w.toMul : G)) ∧
      ∀ (g : J) w, (e (σ g w)).val = ρ (q g) (e w).val := by
  let J := Diagonal.localGroup K A T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let Wg := W.map J.subtype
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map J.subtype
  let WK := Diagonal.movedModule K A T
  let : IsElementaryAbelian 2 WK := IsElementaryAbelian.of_le
    (reduced_image_commutator_le J K (le_sup_left.trans le_sup_left))
  let hJW := reduced_image_commutator_normalized J K (le_sup_left.trans le_sup_left) hn
  let σ := Representation.elementaryRepresentation (p := 2)
    (WK.normalizerMonoidHom.comp (inclusion hJW))
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨e,he⟩ := localGroup_moved_coordinates K A T
  refine ⟨e,he,?_⟩
  intro g w
  apply Additive.toMul.injective
  apply Subtype.ext
  apply J.subtype_injective
  change (((e (σ g w)).val.toMul : J) : G) = (((ρ (q g) (e w).val).toMul : J) : G)
  rw [he (σ g w), NormalElementaryQuotient.representation_apply]
  change ((σ g w).toMul : G) = (g : G) * (((e w).val.toMul : J) : G) * (g : G)⁻¹
  rw [he w]
  exact normalizerMonoidHom_apply_apply_coe WK (inclusion hJW g) w.toMul

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
