module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.CommonBorel
public import Theory.Representation.FrattiniAction
public import Theory.GroupTheory.QuotientIntersection

/-!
# The faithful ambient action of the original first radical

For R₁=O₂(L₁T), the Sylow-overgroup argument identifies O₂(N_G(R₁)) with
R₁. The original condition E makes this nontrivial two-local characteristic
two, so C_G(R₁)≤R₁. Burnside's basis-kernel theorem now gives kernel
exactly R₁ for the literal conjugation action on R₁/Φ(R₁).

Apply that same map to a hypothetical outside H with n(H)>1 and to L₁T.
Their actual A₅/S₅ core quotients are distinct subgroups of the automorphism
group of R₁/Φ(R₁). Their intersection is the image of the original common
Borel, has index five in both, and contains the common original Sylow image.
That image remains Sylow in the full normalizer image, whose two-core is
trivial. These ambient conditions are retained for the remaining model step.
Thus no abstract A₅-overgroup uniqueness is used, and no central-cover kernel
is discarded. The remaining exclusion must use the field-four structure of
this actual radical; universal 11.4.4 remains unfinished.

Earlier geometry, full 11.3.2, the surviving list and Kz=K retain the producers
listed in CommonBorel. OddKernelNormalizer remains with
qt-d-1222-natural-odd-kernel-normalizer, with final discharge by
qt-d-1222-shadow-components. This module introduces no additional premise.
Source: Aschbacher–Smith 1.1.4(6), 11.1.5 and 11.4.4,
printed pp.501,765–766 and778 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

/-- The literal conjugation action on the full radical's Frattini quotient. -/
@[expose] def radicalFrattiniAction {G : Type*} [Group G] (R : Subgroup G) :
    normalizer (R : Set G) →* MulAut (R ⧸ frattini R) :=
  (quotientAut (frattini R)).comp R.normalizerMonoidHom

/-- The image of an original actor under the same full-normalizer action. -/
@[expose] def radicalFrattiniImage {G : Type*} [Group G] (R A : Subgroup G) :
    Subgroup (MulAut (R ⧸ frattini R)) :=
  (A.subgroupOf (normalizer (R : Set G))).map (radicalFrattiniAction R)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- The full ambient normalizer has exactly the original first radical as its two-core. -/
theorem ofFlag_radical_normalizer_core :
    (normalizer (f.Ri 0 : Set G)).pCoreIn 2 = f.Ri 0 := by
  let A := f.Li 0 ⊔ (T : Subgroup G)
  let R := f.Ri 0
  let N := normalizer (R : Set G)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hTN : (T : Subgroup G) ≤ N := le_sup_right.trans hAN
  have hNT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using
      pCoreIn_le_sylow N (T.subtype hTN)
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N)
      (hNT.trans le_sup_right)
      (hAN.trans (N.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) R.le_normalizer le_rfl

/-- Condition E makes the actual first radical self-centralizing in G. -/
theorem ofFlag_radical_selfCentralizing :
    centralizer (f.Ri 0 : Set G) ≤ f.Ri 0 := by
  let R := f.Ri 0
  let N := normalizer (R : Set G)
  have hcore : N.pCoreIn 2 = R := ofFlag_radical_normalizer_core S f
  have hR : R ≠ ⊥ := fun hz => D.ne_bot (bot_unique (hz ▸ f.seed_le_Ri S 0))
  have hTN : (T : Subgroup G) ≤ N :=
    le_sup_right.trans ((f.Li 0 ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hchar : HasCharacteristicTwo N := Chapter1.mem_He_iff.mp
    (Chapter1.twoLocal_mem_He_of_sylow_le T (S.source.simpleQTKE.evenCharacteristic T)
      ⟨R,hR,isPGroup_pCoreIn 2 (f.Li 0 ⊔ (T : Subgroup G)),rfl⟩ hTN)
  have hc := (inf_centralizer_pCoreIn_le_iff 2 N).mpr hchar
  rw [hcore] at hc
  exact (le_inf (Subgroup.centralizer_le_normalizer _) le_rfl).trans hc

/-- The full normalizer acts on the literal Frattini quotient with kernel exactly R₁. -/
theorem ofFlag_radical_frattini_kernel :
    (radicalFrattiniAction (f.Ri 0)).ker =
      (f.Ri 0).subgroupOf (normalizer (f.Ri 0 : Set G)) := by
  let R := f.Ri 0
  let N := normalizer (R : Set G)
  have hR : IsPGroup 2 R := isPGroup_pCoreIn 2 (f.Li 0 ⊔ (T : Subgroup G))
  have hc : R.normalizerMonoidHom.ker ≤ R.subgroupOf N := by
    rw [normalizerMonoidHom_ker]
    exact comap_mono (ofFlag_radical_selfCentralizing S f)
  have hk : IsPGroup 2 (radicalFrattiniAction R).ker :=
    (isPGroup_quotientAut_frattini_kernel hR).comap_of_ker_isPGroup
      R.normalizerMonoidHom ((hR.comap_subtype).to_le hc)
  have hcore : pCore 2 N = R.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le R.le_normalizer]
    exact ofFlag_radical_normalizer_core S f
  apply le_antisymm (hcore ▸ (show (radicalFrattiniAction R).ker ≤ pCore 2 N from
    le_sSup ⟨inferInstance,hk⟩))
  intro x hx
  change quotientAut (frattini R) (R.normalizerMonoidHom x) = 1
  have he : R.normalizerMonoidHom x = MulAut.conj (⟨x,hx⟩ : R) := by
    ext r
    rfl
  rw [he]
  exact Representation.FrattiniAction.quotientAut_conj_eq_one hR _


omit [Finite G] in
private theorem radicalFrattiniImage_core_equiv
    {R A : Subgroup G} (hAN : A ≤ normalizer (R : Set G))
    (hk : (radicalFrattiniAction R).ker = R.subgroupOf (normalizer (R : Set G)))
    (hcore : A.pCoreIn 2 = R) :
    Nonempty ((A ⧸ pCore 2 A) ≃* radicalFrattiniImage R A) := by
  let N := normalizer (R : Set G)
  let e : A.subgroupOf N ≃* A := subgroupOfEquivOfLe hAN
  let q := (radicalFrattiniAction R).subgroupMap (A.subgroupOf N)
  let π := q.comp e.symm.toMonoidHom
  have hπ : Function.Surjective π :=
    ((radicalFrattiniAction R).subgroupMap_surjective _).comp e.symm.surjective
  have hker : π.ker = pCore 2 A := by
    ext a
    change π a = 1 ↔ a ∈ pCore 2 A
    rw [Subtype.ext_iff]
    change radicalFrattiniAction R (⟨a,hAN a.property⟩ : N) = 1 ↔ a ∈ pCore 2 A
    change (⟨a,hAN a.property⟩ : N) ∈ (radicalFrattiniAction R).ker ↔ a ∈ pCore 2 A
    rw [hk]
    change (a : G) ∈ R ↔ a ∈ pCore 2 A
    rw [←hcore]
    exact mem_map_iff_mem A.subtype_injective
  exact ⟨QuotientGroup.liftEquiv (pCore 2 A) hπ hker.symm⟩

omit [Finite G] in
private theorem radicalFrattiniImage_relIndex
    {R A B : Subgroup G} (hAN : A ≤ normalizer (R : Set G))
    (hBN : B ≤ normalizer (R : Set G))
    (hk : (radicalFrattiniAction R).ker = R.subgroupOf (normalizer (R : Set G)))
    (hRA : R ≤ A) (hRB : R ≤ B) :
    (radicalFrattiniImage R A).relIndex (radicalFrattiniImage R B) = A.relIndex B := by
  let N := normalizer (R : Set G)
  have hka : (radicalFrattiniAction R).ker ≤ A.subgroupOf N := by
    rw [hk]
    exact comap_mono hRA
  have hkb : (radicalFrattiniAction R).ker ≤ B.subgroupOf N := by
    rw [hk]
    exact comap_mono hRB
  change ((A.subgroupOf N).map (radicalFrattiniAction R)).relIndex
    ((B.subgroupOf N).map (radicalFrattiniAction R)) = _
  rw [relIndex_map_map,sup_of_le_left hka,sup_of_le_left hkb]
  have hi := relIndex_map_map_of_injective (A.subgroupOf N) (B.subgroupOf N) N.subtype_injective
  have hAm : (A.subgroupOf N).map N.subtype = A := map_subgroupOf_eq_of_le hAN
  have hBm : (B.subgroupOf N).map N.subtype = B := map_subgroupOf_eq_of_le hBN
  rw [hAm,hBm] at hi
  exact hi.symm

private theorem radicalFrattiniImage_sylow
    {R A : Subgroup G} (hAN : A ≤ normalizer (R : Set G))
    (hTA : (T : Subgroup G) ≤ A) :
    Chapter1.IsSylowIn 2 (radicalFrattiniImage R (T : Subgroup G))
      (radicalFrattiniImage R A) := by
  let N := normalizer (R : Set G)
  let P := (T.subtype (hTA.trans hAN)).subtype
    (show (T : Subgroup G).subgroupOf N ≤ A.subgroupOf N from comap_mono hTA)
  let q := (radicalFrattiniAction R).subgroupMap (A.subgroupOf N)
  let U := P.mapSurjective (f := q) ((radicalFrattiniAction R).subgroupMap_surjective _)
  refine ⟨U,?_⟩
  change (U : Subgroup ((A.subgroupOf N).map (radicalFrattiniAction R))).map
    ((A.subgroupOf N).map (radicalFrattiniAction R)).subtype = _
  rw [Sylow.coe_mapSurjective,Subgroup.map_map]
  change ((P : Subgroup (A.subgroupOf N)).map
    ((radicalFrattiniAction R).comp (A.subgroupOf N).subtype)) = _
  rw [←Subgroup.map_map]
  change ((((T : Subgroup G).subgroupOf N).subgroupOf (A.subgroupOf N)).map
    (A.subgroupOf N).subtype).map (radicalFrattiniAction R) = _
  have hm : (((T : Subgroup G).subgroupOf N).subgroupOf (A.subgroupOf N)).map
      (A.subgroupOf N).subtype = (T : Subgroup G).subgroupOf N :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G).subgroupOf N ≤ A.subgroupOf N from comap_mono hTA)
  rw [hm]
  rfl


variable (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The remaining pair is realized by the literal Frattini action of N_G(R₁).
Both sides have their original core quotients, their intersection has index
five in each image, and the same Sylow image is retained in the full ambient
image, whose two-core is trivial. -/
theorem ofFlag_large_generation_frattini_pair
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    let R := f.Ri 0
    let A := f.Li 0 ⊔ (T : Subgroup G)
    let U := radicalFrattiniImage R H
    let W := radicalFrattiniImage R A
    Nonempty ((H ⧸ pCore 2 H) ≃* U) ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* W) ∧
      (Nonempty (U ≃* alternatingGroup (Fin 5)) ∨ Nonempty (U ≃* Equiv.Perm (Fin 5))) ∧
      (Nonempty (W ≃* alternatingGroup (Fin 5)) ∨ Nonempty (W ≃* Equiv.Perm (Fin 5))) ∧
      U ≠ W ∧
      radicalFrattiniImage R (H ⊓ A) = U ⊓ W ∧
      (U ⊓ W).relIndex U = 5 ∧ (U ⊓ W).relIndex W = 5 ∧
      Chapter1.IsSylowIn 2 (radicalFrattiniImage R (T : Subgroup G)) U ∧
      Chapter1.IsSylowIn 2 (radicalFrattiniImage R (T : Subgroup G)) W ∧
      Chapter1.IsSylowIn 2 (radicalFrattiniImage R (T : Subgroup G))
        (radicalFrattiniImage R (normalizer (R : Set G))) ∧
      pCore 2 (radicalFrattiniImage R (normalizer (R : Set G))) = ⊥ := by
  let R := f.Ri 0
  let A := f.Li 0 ⊔ (T : Subgroup G)
  let N := normalizer (R : Set G)
  obtain ⟨hinter,hiH,hiA,_,_,hjoin⟩ := ofFlag_large_generation_paired_borel
    S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn
  have hHN : H ≤ N := le_sup_left.trans hjoin
  have hAN : A ≤ N := le_sup_right.trans hjoin
  have hcoreH : H.pCoreIn 2 = R := ofFlag_large_generation_core_eq_radical
    S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn
  have hcoreA : A.pCoreIn 2 = R := rfl
  have hk := ofFlag_radical_frattini_kernel S f
  obtain ⟨eH⟩ := radicalFrattiniImage_core_equiv hHN hk hcoreH
  obtain ⟨eA⟩ := radicalFrattiniImage_core_equiv hAN hk hcoreA
  obtain ⟨eN⟩ := radicalFrattiniImage_core_equiv (le_rfl : N ≤ N) hk
    (ofFlag_radical_normalizer_core S f)
  have hNcore : pCore 2 (radicalFrattiniImage R N) = ⊥ := by
    rw [←pCore_map_iso 2 eN,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
  obtain ⟨hfour,_,_,hmodels,_⟩ := ofFlag_large_generation_two_core_models
    S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn
  have hmodelsA : Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 5)) := by
    obtain ⟨f₀,hu,_,hq,_⟩ := LocalGeometry.exists_unique_marked_flag D S c
    have hh : f.Li 0 = f₀.Li 0 := congrArg
      (fun U => LocalGeometry.localResidual L (c.preimage U))
      (hu 0 _ (f.dimension 0) (f.invariant 0))
    have hseed : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃*
        Theory.PSL2.Group S.field.Carrier) := hh.symm ▸ hq 0
    obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (S.field.card_eq.trans (by rw [hfour]; rfl))
    exact Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
      (f.Li 0) (T : Subgroup G) (f.sylow_normalizes_Li 0) T.isPGroup'
      (hseed.some.trans e5)
  have hRH : R ≤ H := hcoreH ▸ H.pCoreIn_le 2
  have hRA : R ≤ A := A.pCoreIn_le 2
  have hRC : R ≤ H ⊓ A := le_inf hRH hRA
  have hCN : H ⊓ A ≤ N := inf_le_left.trans hHN
  have hi : radicalFrattiniImage R (H ⊓ A) =
      radicalFrattiniImage R H ⊓ radicalFrattiniImage R A := by
    change ((H ⊓ A).subgroupOf N).map (radicalFrattiniAction R) = _
    change ((H.subgroupOf N) ⊓ (A.subgroupOf N)).map (radicalFrattiniAction R) = _
    exact map_inf_of_ker_le _ _ _ (by rw [hk]; exact comap_mono hRA)
  refine ⟨⟨eH⟩,⟨eA⟩,?_,?_,?_,hi,?_,?_,
    radicalFrattiniImage_sylow hHN hH.1.1.2,
    radicalFrattiniImage_sylow hAN le_sup_right,
    radicalFrattiniImage_sylow (le_rfl : N ≤ N) (hH.1.1.2.trans hHN),hNcore⟩
  · exact hmodels.elim
      (fun hh => Or.inl (hh.map fun e => eH.symm.trans e))
      (fun hh => Or.inr (hh.map fun e => eH.symm.trans e))
  · exact hmodelsA.elim
      (fun hh => Or.inl (hh.map fun e => eA.symm.trans e))
      (fun hh => Or.inr (hh.map fun e => eA.symm.trans e))
  · intro hh
    have hsub : H.subgroupOf N = A.subgroupOf N := by
      have heq := congrArg (comap (radicalFrattiniAction R)) hh
      change (((H.subgroupOf N).map (radicalFrattiniAction R)).comap
        (radicalFrattiniAction R)) =
        (((A.subgroupOf N).map (radicalFrattiniAction R)).comap
        (radicalFrattiniAction R)) at heq
      rwa [comap_map_eq_self (show (radicalFrattiniAction R).ker ≤ H.subgroupOf N from
          by rw [hk]; exact comap_mono hRH),
        comap_map_eq_self (show (radicalFrattiniAction R).ker ≤ A.subgroupOf N from
          by rw [hk]; exact comap_mono hRA)] at heq
    have heq := congrArg (map N.subtype) hsub
    rw [map_subgroupOf_eq_of_le hHN,map_subgroupOf_eq_of_le hAN] at heq
    apply hH.1.2
    rw [heq]
    exact sup_le ((LocalGeometry.localResidual_le _).trans (inf_le_left.trans L.le_normalizer))
      D.sylow_normalizes_component
  · rw [←hi,radicalFrattiniImage_relIndex hCN hHN hk hRC hRH]
    exact hiH
  · rw [←hi,radicalFrattiniImage_relIndex hCN hAN hk hRC hRA]
    exact hiA

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
