module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.HexadFixedBounds
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadDuality

/-!
# The Q-image centralizer bounds in the Thompson argument

The actual H→H/Q native action transports the checked hexad translation
bounds to the original fixed preimage in Q. A nontrivial quotient actor
has fixed preimage of order at most 512; a subgroup whose image has more
than two elements fixes exactly E₁ modulo the original center.

Thus a subgroup A≤Q of order greater than 512 has C_E(A)≤E₁.
Commutator duality gives the exact index |E:C_E(A)|=16|A*| in the
literal quotient G₁,₃/E. If |A|=512, the centralizer modulo the original
center has image of order at most two; consequently |E:C_E(A)E₁|≥8.
These discharge both Q-image bounds in the last paragraph of AS91 (4.6).
The preceding mixed-actor bounds, E=J(T), and full normalizer/module
recognition remain separate duties; no cocode marking is assumed here.

Source: Aschbacher–Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.6), printed p.598, DOI 10.1007/BF01232280.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu LocalGeometry M22TripleCover M22TripleCover.Ambient InvariantPoint
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

private theorem block_mem (b : m22DesignAut) (B : Finset (Fin 22))
    (hB : B ∈ m22Blocks) : b • B ∈ m22Blocks := by
  have hb := b.property
  change b.val ∈ m22WittDesign.aut at hb
  rw [SteinerSystem.mem_aut_iff] at hb
  have hB' : B ∈ (m22WittDesign.blocks : Set (Finset (Fin 22))) := by
    simpa [m22WittDesign] using hB
  have hi := Set.smul_mem_smul_set (a := b.val) hB'
  rw [hb] at hi
  simpa [m22WittDesign, Subgroup.smul_def] using hi

include h in
private theorem center_le_fixedPreimage (D : Subgroup (centralizer z)) :
    center (centralizer z) ≤ commutatorPreimage (core z) D (center (centralizer z)) := by
  apply le_commutatorPreimage
  · rw [←core_center_eq_centralizer_center h]
    exact map_subtype_le _
  · rw [commutator_eq_bot_iff_le_centralizer.mpr (center_le_centralizer _)]
    exact bot_le

omit [Finite G] in
private theorem fixedPreimage_comm (D : Subgroup (centralizer z)) :
    ⁅D,commutatorPreimage (core z) D (center (centralizer z))⁆ ≤ center (centralizer z) := by
  rw [commutator_comm]
  exact commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal

include h X in
/-- One nontrivial original hexad two-core actor bounds its fixed preimage in Q by 512. -/
theorem originalHexad_noncore_fixed_card_le {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (D : Subgroup (centralizer z)) (hD : D ≤ (originalPlaneHexad e B).pCoreIn 2)
    (hDQ : ¬ D ≤ core z) :
    Nat.card (commutatorPreimage (core z) D (center (centralizer z))) ≤ 512 := by
  let := h.extraspecial
  obtain ⟨b,hb⟩ := originalPlaneHexad_native_image h e X
  obtain ⟨g,hg,hgQ⟩ := Set.not_subset.mp hDQ
  have hgn : coreNativeProjection h e X g ∈ (nativeHexadStabilizer (b • B)).pCoreIn 2 :=
    (originalPlaneHexad_twoCore_native_image h e X B (b • B) (hb B)).le
      (mem_map_of_mem _ (hD hg))
  have hg1 : coreNativeProjection h e X g ≠ 1 := by
    intro he
    apply hgQ
    exact (coreNativeProjection_ker h e X).le he
  let C := commutatorPreimage (core z) D (center (centralizer z))
  have hCQ : C ≤ core z := commutatorPreimage_le _ _ _
  let f := corePointProjection h e X
  let V := (C.subgroupOf (core z)).map f
  have hv (w : V) : w.val.toAdd ∈ nativeHexadElementFixed (coreNativeProjection h e X g) := by
    obtain ⟨q,hq,he⟩ := w.property
    rw [←he]
    apply (nativeHexadElementFixed_mem _ _).mpr
    exact (coreNativeProjection_fixed_iff h e X g q).mpr
      (fixedPreimage_comm D (commutator_mem_commutator hg hq))
  let j (w : V) : nativeHexadElementFixed (coreNativeProjection h e X g) := ⟨w.val.toAdd,hv w⟩
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact congrArg (fun u : nativeHexadElementFixed (coreNativeProjection h e X g) => u.val) he
  have hVc : Nat.card V ≤ 256 := (Nat.card_le_card_of_injective j hj).trans
    (nativeHexadElementFixed_card_le (block_mem b B hB) _ hgn hg1)
  have hk : f.ker ≤ C.subgroupOf (core z) := by
    rw [corePointProjection_ker]
    intro q hq
    apply center_le_fixedPreimage h D
    rw [←core_center_eq_centralizer_center h]
    exact mem_map_of_mem _ hq
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map (C.subgroupOf (core z)) f
  rw [inf_eq_right.mpr hk,corePointProjection_ker,
    IsExtraspecial.center_order_p 2 (core z),
    Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv] at hc
  change 2 * Nat.card V = Nat.card C at hc
  change Nat.card C ≤ 512
  omega

/-- Two independent original quotient actors already cut out exactly E1 in Q/Z. -/
theorem originalHexad_large_actor_fixed_eq {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (D : Subgroup (centralizer z)) (hD : D ≤ (originalPlaneHexad e B).pCoreIn 2)
    (hc : 2 < Nat.card (D.map (QuotientGroup.mk' (core z)))) :
    commutatorPreimage (core z) D (center (centralizer z)) = originalHexadFixedCore h e X B := by
  let := h.extraspecial
  obtain ⟨b,hb⟩ := originalPlaneHexad_native_image h e X
  let P := D.map (coreNativeProjection h e X)
  have hP : P ≤ (nativeHexadStabilizer (b • B)).pCoreIn 2 :=
    (map_mono hD).trans_eq (originalPlaneHexad_twoCore_native_image h e X B (b • B) (hb B))
  have hPc : 2 < Nat.card P := by
    change 2 < Nat.card (D.map ((coreAmbientHom h e X).comp (QuotientGroup.mk' (core z))))
    rw [←map_map,card_map_of_injective (coreAmbientHom_injective h e X)]
    exact hc
  apply le_antisymm
  · intro q hq
    have hqQ := commutatorPreimage_le (core z) D (center (centralizer z)) hq
    apply (originalHexadFixedCore_native_mem h e X B (b • B) (hb B) ⟨q,hqQ⟩).mpr
    apply nativeHexadFixedSpace_of_large_subgroup (block_mem b B hB) P hP hPc
    rintro _ ⟨d,hd,rfl⟩
    exact (coreNativeProjection_fixed_iff h e X d ⟨q,hqQ⟩).mpr
      (fixedPreimage_comm D (commutator_mem_commutator hd hq))
  · apply le_commutatorPreimage (originalHexadFixedCore_le h e X B)
    apply (commutator_mono le_rfl hD).trans
    rw [originalHexadFixedCore_source]
    exact commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal

/-- The large Q-actor branch of AS91 (4.6): its centralizer in E lies entirely in E1. -/
theorem originalHexad_large_core_centralizer_le {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (centralizer z)) (hAQ : A ≤ core z) (hAc : 512 < Nat.card A) :
    originalHexadElementary h e X B ⊓ Subgroup.centralizer (A : Set (centralizer z)) ≤
      originalHexadFixedCore h e X B := by
  intro x hx
  by_contra hxU
  have hxQ : x ∉ core z := fun hq => hxU
    ((originalHexadElementary_data h e X hB).2.2.2.2.2.le ⟨hx.1,hq⟩)
  have hxR : x ∈ (originalPlaneHexad e B).pCoreIn 2 := by
    rw [originalPlaneHexad_twoCore h e X B]
    exact (sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl) hx.1
  have hD : zpowers x ≤ (originalPlaneHexad e B).pCoreIn 2 := zpowers_le.mpr hxR
  have hnot : ¬ zpowers x ≤ core z := fun hn => hxQ (hn (mem_zpowers x))
  have hbound := originalHexad_noncore_fixed_card_le h e X hB (zpowers x) hD hnot
  have hAC : A ≤ Subgroup.centralizer (zpowers x : Set (centralizer z)) :=
    le_centralizer_iff.mp (zpowers_le.mpr hx.2)
  have hAP : A ≤ commutatorPreimage (core z) (zpowers x) (center (centralizer z)) :=
    le_commutatorPreimage hAQ (by
      rw [commutator_eq_bot_iff_le_centralizer.mpr hAC]
      exact bot_le)
  have ha := card_le_of_le hAP
  omega
/-- The large Q-image case has the exact source gap of four binary dimensions. -/
theorem originalHexad_large_core_index {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (centralizer z)) (hAQ : A ≤ core z) (hAc : 512 < Nat.card A) :
    letI := originalHexadElementary_normal h e X hB
    let L := originalPlaneHexad e B
    let E := originalHexadElementary h e X B
    let f := QuotientGroup.mk' (E.subgroupOf L)
    let C := E ⊓ Subgroup.centralizer (A : Set (centralizer z))
    (C.subgroupOf E).index = 16 * Nat.card ((A.subgroupOf L).map f) := by
  let := originalHexadElementary_normal h e X hB
  let L := originalPlaneHexad e B
  let E := originalHexadElementary h e X B
  let U := originalHexadFixedCore h e X B
  let f := QuotientGroup.mk' (E.subgroupOf L)
  let C := E ⊓ Subgroup.centralizer (A : Set (centralizer z))
  have hCU : C = U ⊓ Subgroup.centralizer (A : Set (centralizer z)) :=
    le_antisymm (le_inf (originalHexad_large_core_centralizer_le h e X hB A hAQ hAc) inf_le_right)
      (inf_le_inf_right _ le_sup_left)
  have hd := originalHexadQuotient_core_centralizer_card h e X hB A hAQ
  change Nat.card ((A.subgroupOf L).map f) *
    Nat.card (U ⊓ Subgroup.centralizer (A : Set (centralizer z)) : Subgroup (centralizer z)) = 128 at hd
  rw [←hCU] at hd
  have hc := (C.subgroupOf E).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ E from inf_le_left)).toEquiv,
    show Nat.card E = 2048 from (originalHexadElementary_data h e X hB).2.2.2.1] at hc
  have hp : 0 < Nat.card C := Nat.card_pos
  change (C.subgroupOf E).index = 16 * Nat.card ((A.subgroupOf L).map f)
  nlinarith
/-- The rank-two Q-image boundary has codimension at least three after adjoining E1. -/
theorem originalHexad_core_boundary_index {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (centralizer z)) (hAQ : A ≤ core z) (hAc : Nat.card A = 512) :
    let E := originalHexadElementary h e X B
    let U := originalHexadFixedCore h e X B
    (((E ⊓ Subgroup.centralizer (A : Set (centralizer z))) ⊔ U).subgroupOf E).index ≥ 8 := by
  let E := originalHexadElementary h e X B
  let U := originalHexadFixedCore h e X B
  let C := commutatorPreimage E A (center (centralizer z))
  have hCE : C ≤ E := commutatorPreimage_le _ _ _
  have hER : E ≤ (originalPlaneHexad e B).pCoreIn 2 := by
    rw [originalPlaneHexad_twoCore h e X B]
    exact sup_le_sup (originalHexadFixedCore_le h e X B) le_rfl
  have hUC : U ≤ C := le_commutatorPreimage le_sup_left
    ((commutator_mono (originalHexadFixedCore_le h e X B) hAQ).trans
      (originalHexadFixedCore_configuration h e X hB).commutator_le)
  have hi : C ⊓ core z = U := by
    apply le_antisymm
    · exact (inf_le_inf_right _ hCE).trans (originalHexadElementary_data h e X hB).2.2.2.2.2.le
    · exact le_inf hUC (originalHexadFixedCore_le h e X B)
  have hm : Nat.card (C.map (QuotientGroup.mk' (core z))) ≤ 2 := by
    by_contra hn
    have he := originalHexad_large_actor_fixed_eq h e X hB C (hCE.trans hER) (by omega)
    have hAC : A ≤ commutatorPreimage (core z) C (center (centralizer z)) := by
      apply le_commutatorPreimage hAQ
      rw [commutator_comm]
      exact commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal
    rw [he] at hAC
    have hc := card_le_of_le hAC
    rw [hAc,(originalHexadFixedCore_data h e X hB).2] at hc
    omega
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map C (QuotientGroup.mk' (core z))
  rw [QuotientGroup.ker_mk',hi,show Nat.card U=128 from (originalHexadFixedCore_data h e X hB).2] at hc
  have hCc : Nat.card C ≤ 256 := by omega
  let F := (E ⊓ Subgroup.centralizer (A : Set (centralizer z))) ⊔ U
  have hFC : F ≤ C := sup_le
    (le_commutatorPreimage inf_le_left (by
      rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_right]
      exact bot_le)) hUC
  have hFc : Nat.card F ≤ 256 := (card_le_of_le hFC).trans hCc
  have hf := (F.subgroupOf E).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (hFC.trans hCE)).toEquiv,
    show Nat.card E=2048 from (originalHexadElementary_data h e X hB).2.2.2.1] at hf
  have hb := Nat.mul_le_mul_right (F.subgroupOf E).index hFc
  rw [hf] at hb
  change 8 ≤ (F.subgroupOf E).index
  omega
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
