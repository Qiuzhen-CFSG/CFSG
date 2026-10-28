module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.Representation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection


/-!
# Preparing the literal SL₃ action for flag-type exclusion

The source Thompson-commutator relation descends from the star quotient to
K⁺. Since W_K lies in the actual Sylow Tᵥ, B.2.5 places the Thompson plus
image in the offender subgroup of the published plus representation.
Normality of that offender subgroup then places K⁺ itself there. This
also removes the trivial alternative from the adequate B.5.6 application.

Normality of K⁺ constructs the canonical section
[W_K,K⁺] / C_[W_K,K⁺](K⁺), with its action of the entire plus group.
The original Tᵥ model action is conjugation on this normal component and
preserves the literal marked unipotent subgroup. No flag preservation or
natural-module identification is assumed or proved here. Extracting the
component action from the full classifier and excluding graph interchange
remain with the FlagTypes assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.2.5, printed p.76, and the paragraph before 13.6.14 and proof of 13.6.19,
printed pp.929–931.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection
universe u
variable {G : Type u} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The invariant component has normal image in the entire plus actor. -/
theorem plus_component_normal (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    (plusImage K L T z v hL hz K).Normal := by
  have hs := starImage_Kminus_normal_in_actor K L T z v hK
  rw [Kminus_eq_of_invariant K T v hn] at hs
  let := hs
  have hm := Subgroup.Normal.map hs (starToPlus K L T z v hK.1.1 hL hz)
    (starToPlus_surjective K L T z v hK.1.1 hL hz)
  rwa [starToPlus_image K L T z v hK.1.1 hL hz K (K_le_plusActor K L T v)] at hm

/-- The source star commutator descends through the actual star-to-plus map. -/
theorem plus_component_thompson_commutator (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        plusImage K L T z v hL hz K := by
  let A := starImage z v (plusActor K L T v)
  let J := Stellmacher.elementaryAbelianMaxJ (Tv T v)
  have hJ : J ≤ plusActor K L T v :=
    (sSup_le fun _ h => h.1).trans le_sup_right
  have hCA : starImage z v K ≤ A := map_mono (comap_mono (K_le_plusActor K L T v))
  have hJA : starImage z v J ≤ A := map_mono (comap_mono hJ)
  have hc : ⁅(starImage z v K).subgroupOf A, (starImage z v J).subgroupOf A⁆ =
      (starImage z v K).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hCA,
      map_subgroupOf_eq_of_le hJA]
    exact (invariant_component_consequences K L T z v hK hn).1.1.2.2.2
  have hm := congrArg (map (starToPlus K L T z v hK.1.1 hL hz)) hc
  simpa only [A, map_commutator,
    starToPlus_image K L T z v hK.1.1 hL hz K (K_le_plusActor K L T v),
    starToPlus_image K L T z v hK.1.1 hL hz J hJ] using hm

private theorem thompson_le_offender_of_internal [Finite G]
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) :
    plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤
      offenderSubgroup (plusRepresentation K L T z v hL hz) := by
  let A := plusActor K L T v
  let W := (WK K L T z v).subgroupOf A
  let S := (Tv T v).subgroupOf A
  have hWA : WK K L T z v ≤ A := hWT.trans le_sup_right
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (plusActor_normalizes_WK K L T z v hL hz)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWA
  let q := plusMk K L T z v hL hz
  have hker : q.ker = centralizer (W : Set A) := by
    rw [plusMk_ker]
    ext a
    change (a : G) ∈ centralizer (WK K L T z v : Set G) ↔ a ∈ centralizer (W : Set A)
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro h w hw
      apply Subtype.ext
      exact h (w : G) hw
    · intro h w hw
      exact congrArg (fun x : A => (x : G)) (h ⟨w, hWA hw⟩ hw)
  let σ := NormalElementaryQuotient.representation W q
    (plusMk_surjective K L T z v hL hz) hker
  let ea : Additive W ≃+ Additive (WK K L T z v) :=
    (subgroupOfEquivOfLe hWA).toAdditive
  let E : Additive W ≃ₗ[ZMod 2] Additive (WK K L T z v) := ea.toLinearEquiv (fun c w => ZMod.map_smul ea.toAddMonoidHom c w)
  have hE (g : Gplus K L T z v hL hz) (w : Additive W) :
      E (σ g w) = plusRepresentation K L T z v hL hz g (E w) := by
    obtain ⟨a, rfl⟩ := plusMk_surjective K L T z v hL hz g
    apply Additive.toMul.injective
    apply Subtype.ext
    change (((σ (q a) w).toMul : A) : G) = _
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  have hweight (B : Subgroup (Gplus K L T z v hL hz)) :
      weight σ B = weight (plusRepresentation K L T z v hL hz) B := by
    have he := fixedSpace_map_equivariant σ (plusRepresentation K L T z v hL hz)
      (MonoidHom.id _) E hE B
    simp only [map_id] at he
    have hd := (E.ofSubmodules _ _ he).finrank_eq
    exact congrArg (fun n => rank B + n) hd
  have hbest {B : Subgroup (Gplus K L T z v hL hz)} (hB : IsBestOffender σ B) :
      IsBestOffender (plusRepresentation K L T z v hL hz) B := by
    refine ⟨hB.1, fun C hC => ?_⟩
    rw [← hweight C, ← hweight B]
    exact hB.2 C hC
  have hj := CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.thompson_image_le_internal_offenderSubgroup
    S W (comap_mono hWT) q (plusMk_surjective K L T z v hL hz) hker
  have hg : offenderSubgroup σ ≤ offenderSubgroup (plusRepresentation K L T z v hL hz) := by
    apply iSup_le
    intro B
    apply iSup_le
    rintro ⟨hB, _⟩
    exact le_iSup_of_le B (le_iSup_of_le ⟨hbest hB, le_top⟩ le_rfl)
  have hS : S.map A.subtype = Tv T v := map_subgroupOf_eq_of_le le_sup_right
  have he : (Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf A =
      Stellmacher.elementaryAbelianMaxJ S := by
    rw [← hS, Stellmacher.elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  change ((Stellmacher.elementaryAbelianMaxJ (Tv T v)).subgroupOf A).map q ≤ _
  rw [he]
  exact hj.trans hg

/-- The genuine ambient core and Sylow hypotheses put the Thompson image in the offender actor. -/
theorem plus_thompson_le_offender [Finite G]
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ≤ Gv v) (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤
      offenderSubgroup (plusRepresentation K L T z v hL hz) := by
  obtain ⟨S, hS⟩ := hSyl
  apply thompson_le_offender_of_internal K L T z v hL hz
  exact (WK_le_Uv K L T z v hK).trans
    (hU.trans ((pCoreIn_le_sylow (Gv v) S).trans_eq hS))

/-- The Thompson commutator places the component in the classifier's actual actor. -/
theorem plus_component_le_offender [Finite G]
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    plusImage K L T z v hL hz K ≤
      offenderSubgroup (plusRepresentation K L T z v hL hz) := by
  let := offenderSubgroup_normal (plusRepresentation K L T z v hL hz)
  rw [← plus_component_thompson_commutator K L T z v hL hz hK hn]
  exact (commutator_mono le_rfl
    (plus_thompson_le_offender K L T z v hL hz hK.1.1 hU hSyl)).trans
      (commutator_le_right _ _)

/-- The canonical component section retains the action of the whole plus group. -/
def plusComponentSection [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    ChapterB.QuasisimpleSource.MovedSection (plusRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K) := by
  let := plus_component_normal K L T z v hL hz hK hn
  exact ChapterB.QuasisimpleSource.MovedSection.ofNormal _ _

/-- The actual component forces the nontrivial alternative of B.5.6. -/
theorem plus_nontrivial_offender_classification [Finite G]
    [IsElementaryAbelian 2 (WK K L T z v)]
    {𝒦 : GroupClass.{u}}
    (source : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v)) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ (Gv v).pCoreIn 2)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    ChapterB.SourceInduction.NontrivialAdequateAlternative
      ((plusRepresentation K L T z v hL hz).comp
        (offenderSubgroup (plusRepresentation K L T z v hL hz)).subtype) := by
  have hCI := plus_component_le_offender K L T z v hL hz hK hn hU hSyl
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  let : Nontrivial (offenderSubgroup (plusRepresentation K L T z v hL hz)) :=
    Function.Injective.nontrivial (inclusion_injective hCI)
  exact (plus_offender_classification K L T z v hL hz source hSQ hK hcore).of_nontrivial _

/-- The model automorphism is conjugation on the normal component in the plus group. -/
theorem modelAction_eq_conjugation {D : Type*} [Group D]
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) (t : Tv T v) :
    let _ := plus_component_normal K L T z v hL hz hK hn
    modelAction K L T z v hL hz hn e t =
      MulAut.congr e (MulAut.conjNormal (plusTvMap K L T z v hL hz t)) := by
  rfl

/-- Tᵥ conjugation preserves the image of its literal intersection with K. -/
theorem modelAction_marked_subgroup {D : Type*} [Group D]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* D) (t : Tv T v) :
    (((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz))).map
        (modelAction K L T z v hL hz hn e t).toMonoidHom =
      ((Tv T v).subgroupOf K).map
        (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) := by
  let S := ((Tv T v).subgroupOf K).map
    (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz))
  have hle (t : Tv T v) : S.map (modelAction K L T z v hL hz hn e t).toMonoidHom ≤ S := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    change modelAction K L T z v hL hz hn e t
      (e (componentPlusMap K L T z v hL hz k)) ∈ S
    rw [modelAction_componentPlusMap]
    exact mem_map.mpr ⟨K.normalizerMonoidHom (inclusion hn t) k,
      (Tv T v).mul_mem ((Tv T v).mul_mem t.property hk) ((Tv T v).inv_mem t.property), rfl⟩
  apply le_antisymm (hle t)
  intro x hx
  refine mem_map.mpr ⟨modelAction K L T z v hL hz hn e t⁻¹ x,
    hle t⁻¹ (mem_map_of_mem _ hx), ?_⟩
  change ((modelAction K L T z v hL hz hn e t) *
    (modelAction K L T z v hL hz hn e t⁻¹)) x = x
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

open scoped MatrixGroups
/-- The specified Sylow marking is preserved by the published model action. -/
theorem modelAction_unipotentSL {F : Type*} [Field F] [Finite F]
    (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) =
        Matrix.PSL3.LinearThree.unipotentSL F) (t : Tv T v) :
    (Matrix.PSL3.LinearThree.unipotentSL F).map
      (modelAction K L T z v hL hz hn e t).toMonoidHom =
        Matrix.PSL3.LinearThree.unipotentSL F := by
  rw [← hmark]
  exact modelAction_marked_subgroup K L T z v hL hz hn e t

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
