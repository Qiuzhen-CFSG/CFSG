module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Parabolics
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding

/-!
# Transport of invariant binary parabolics to the component quotient

The model inclusion intertwines the actual binary action with ambient
conjugation. This transports preservation of the Sylow intersection and
parabolic invariance without replacing any subgroup by its isomorphism type.
The full quotient preimage is the model subgroup joined with the two-core
of the component extension. Since that core lies in Q, adjoining Q gives
exactly the original model subgroup adjoined to Q. Relative component
normality then supplies characteristic two by the component-orbit theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), with the relative local-component
centralizer calculation of 2.3.9(7), printed p.526.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
variable {G : Type*} [Group G] {Q L : Subgroup G} {n : ℕ}

noncomputable def modelInclusion (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2) :
    LinearGroup n →* G := L.subtype.comp (binaryEquiv hn hm).symm.toMonoidHom

theorem modelInclusion_injective (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2) :
    Function.Injective (modelInclusion hn hm) :=
  L.subtype_injective.comp (binaryEquiv hn hm).symm.injective

theorem modelInclusion_action (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (g : (L ⊔ Q : Subgroup G)) (x : LinearGroup n) :
    modelInclusion hn hm (binaryAction hn hm hN g x) =
      (g : G) * modelInclusion hn hm x * (g : G)⁻¹ := by
  have he := binaryAction_apply hn hm hN g ((binaryEquiv hn hm).symm x)
  rw [(binaryEquiv hn hm).apply_symm_apply] at he
  have hh := congrArg (fun y => ((binaryEquiv hn hm).symm y : G)) he
  simpa only [(binaryEquiv hn hm).symm_apply_apply,
    normalizerMonoidHom_apply_apply_coe, coe_inclusion, modelInclusion,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype] using hh

theorem modelInclusion_action_hom (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (g : (L ⊔ Q : Subgroup G)) :
    (modelInclusion hn hm).comp (binaryAction hn hm hN g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp (modelInclusion hn hm) := by
  ext x
  exact modelInclusion_action hn hm hN g x

/-- Preservation by the actual binary action gives ambient normalization. -/
theorem modelSubgroup_normalized (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (P : Subgroup (LinearGroup n))
    (hinv : ∀ g : (L ⊔ Q : Subgroup G), (g : G) ∈ Q →
      P.map (binaryAction hn hm hN g).toMonoidHom = P) :
    Q ≤ normalizer (P.map (modelInclusion hn hm) : Set G) := by
  intro q hq
  let g : (L ⊔ Q : Subgroup G) := ⟨q, (show Q ≤ L ⊔ Q from le_sup_right) hq⟩
  rw [mem_normalizer_iff_map_conj_eq, map_map]
  change P.map ((MulAut.conj (g : G)).toMonoidHom.comp (modelInclusion hn hm)) = _
  rw [← modelInclusion_action_hom hn hm hN g, ← map_map, hinv g hq]

/-- The Sylow intersection supplies a flag preserved by the entire Q action. -/
theorem binaryAction_preserves_sylow (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (g : (L ⊔ Q : Subgroup G)) (hg : (g : G) ∈ Q) :
    ((S : Subgroup L).map (binaryEquiv hn hm).toMonoidHom).map
      (binaryAction hn hm hN g).toMonoidHom =
        (S : Subgroup L).map (binaryEquiv hn hm).toMonoidHom := by
  apply map_injective (modelInclusion_injective hn hm)
  rw [map_map, modelInclusion_action_hom, ← map_map]
  have he : ((S : Subgroup L).map (binaryEquiv hn hm).toMonoidHom).map
      (modelInclusion hn hm) = L ⊓ Q := by
    rw [map_map]
    convert hS using 1
    congr 1
    ext x
    exact congrArg Subtype.val ((binaryEquiv hn hm).symm_apply_apply x)
  rw [he]
  apply mem_normalizer_iff_map_conj_eq.mp
  exact inf_normalizer_le_normalizer_inf ⟨hN hg, Q.le_normalizer hg⟩

/-- Inclusion into the component extension retains the concrete model map. -/
noncomputable def modelExtensionMap (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) : LinearGroup n →* componentExtension Q L :=
  (inclusion (show L ≤ componentExtension Q L from le_sup_left)).comp
    (binaryEquiv hn hm).symm.toMonoidHom

/-- The full quotient preimage is the model subgroup joined with the actual core. -/
theorem quotientPreimage_parabolic (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) (P : Subgroup (LinearGroup n)) :
    quotientPreimage Q L (quotientParabolic Q hn hm P) =
      P.map (modelInclusion hn hm) ⊔ (componentExtension Q L).pCoreIn 2 := by
  unfold quotientPreimage quotientParabolic modelQuotientMap
  rw [← map_map]
  change (((P.map (modelExtensionMap Q hn hm)).map (quotientMap Q L)).comap
    (quotientMap Q L)).map (componentExtension Q L).subtype = _
  rw [comap_map_eq, Subgroup.map_sup, map_map, quotientMap, QuotientGroup.ker_mk']
  rfl

/-- Actual model normalization descends to the prescribed quotient subgroup. -/
theorem quotientParabolic_normalized (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (P : Subgroup (LinearGroup n))
    (hinv : Q ≤ normalizer (P.map (modelInclusion hn hm) : Set G)) :
    sylowImage Q L ≤ normalizer (quotientParabolic Q hn hm P : Set (ComponentQuotient Q L)) := by
  let E := componentExtension Q L
  let F := P.map (modelExtensionMap Q hn hm)
  have hFE : F.map E.subtype = P.map (modelInclusion hn hm) := by
    rw [map_map]
    rfl
  have hF : F = (P.map (modelInclusion hn hm)).subgroupOf E := by
    rw [← hFE, ← comap_subtype]
    exact (comap_map_eq_self_of_injective E.subtype_injective F).symm
  have hle : P.map (modelInclusion hn hm) ≤ E := by rw [← hFE]; exact map_subtype_le _
  have hnorm : (componentNormalizer Q L).subgroupOf E ≤ normalizer (F : Set E) := by
    rw [hF, ← subgroupOf_normalizer_eq hle]
    intro x hx
    exact hinv hx.1
  have hqp : quotientParabolic Q hn hm P = F.map (quotientMap Q L) := by
    rw [quotientParabolic, modelQuotientMap, ← map_map]
    rfl
  rw [hqp]
  exact (map_mono (f := quotientMap Q L) hnorm).trans (le_normalizer_map _)

variable [Finite G] {K : GroupClass} {T : Sylow 2 G} {M V U : Subgroup G}

/-- Lifting the specified quotient image adds only a core already in Q. -/
theorem quotientPreimage_parabolic_join (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (P : Subgroup (LinearGroup n)) :
    quotientPreimage Q L (quotientParabolic Q hn hm P) ⊔ Q =
      P.map (modelInclusion hn hm) ⊔ Q := by
  rw [quotientPreimage_parabolic, sup_assoc,
    sup_eq_right.mpr (extension_core_le_Q h hU hL hQ hN)]

/-- Characteristic two passes from the literal invariant model subgroup to its lifted join. -/
theorem quotientParabolic_join_characteristicTwo (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (P : Subgroup (LinearGroup n))
    (hinv : Q ≤ normalizer (P.map (modelInclusion hn hm) : Set G))
    (hc : HasCharacteristicTwo P) :
    HasCharacteristicTwo ↥(quotientPreimage Q L (quotientParabolic Q hn hm P) ⊔ Q) := by
  rw [quotientPreimage_parabolic_join h hU hL hQ hN hn hm]
  apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
  have hp : P.map (modelInclusion hn hm) ≤ L := by
    rw [modelInclusion, ← map_map]
    exact map_subtype_le _
  apply hL.2.relative_local_adjoin_centralizer hL.1 hp
    (show Q ≤ centralizer (U : Set G) by
      rw [hQ]; exact inf_le_right.trans (centralizer_le hU.1))
    (show IsPGroup 2 Q by rw [hQ]; exact T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans hinv)
  rw [← map_pCoreIn_of_injective 2 P _ (modelInclusion_injective hn hm)]
  apply (inf_centralizer_map_le_iff P (P.pCoreIn 2) _ (modelInclusion_injective hn hm)).mpr
  exact (inf_centralizer_pCoreIn_le_iff 2 _).mpr hc

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
