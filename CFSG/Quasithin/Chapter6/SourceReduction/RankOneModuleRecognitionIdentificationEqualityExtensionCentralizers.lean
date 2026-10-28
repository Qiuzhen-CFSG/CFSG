module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionPairAssembly
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionPreparation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanks
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel

/-!
# The kernel of the equality core action

Let H = C_G(z), K = ⟨V^H⟩ and P = O₂(K), with V the actual natural
layer. The natural hyperplane bound implies C_H(P) = C_H(K). The
extraspecial automorphism kernel then gives C_H(P/Z(P)) = P C_H(K).
Inside P the centralizer of V is its elementary eight P ∩ V; consequently
the centralizer of V in the outer-action kernel is (P ∩ V) C_H(K).

These are the literal subgroup and action identities used by the extension
argument. The quaternion-product premise is supplied by the canonical
equality-pair theorem in the source application below.
Source: Aschbacher–Smith, proof of 6.2.13, printed p.687.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private theorem natural_eight_centralizer
    {B E C : Subgroup G} [IsElementaryAbelian 2 B]
    (hnatural : IsNaturalModule L B 2)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (hEB : E ≤ B) (hE : Nat.card E = 8)
    (hCN : C ≤ normalizer (B : Set G)) (hCE : C ≤ centralizer (E : Set G)) :
    C ≤ centralizer (B : Set G) := by
  have hcor : ChapterE.subgroupCorank B E = 1 := by
    have hi := relIndex_mul_relIndex (⊥ : Subgroup G) E B bot_le hEB
    rw [relIndex_bot_left, relIndex_bot_left, hE, hnatural.card] at hi
    have he : E.relIndex B = 2 := by omega
    simp only [ChapterE.subgroupCorank, he]
    decide
  apply (ChapterE.inducedAutomizer_eq_bot_iff hCN).mp
  apply eq_bot_iff.mpr
  intro a ha
  by_contra hn
  have hane : a ≠ 1 := by simpa only [mem_bot] using hn
  have hlo := natural_automizer_fixedCodim_ge hnatural hNL hane
  have hmid := ChapterE.fixedCodim_mono (ChapterE.automizerRepresentation B)
    (zpowers_le.mpr ha)
  have hhi : Representation.BinaryOffender.fixedCodim (ChapterE.automizerRepresentation B)
      (ChapterE.inducedAutomizer B C) ≤ ChapterE.subgroupCorank B E := by
    rw [ChapterE.fixedCodim_inducedAutomizer B C hCN]
    exact ChapterE.Section06.subgroupCorank_antitone
      (le_inf hEB (le_centralizer_iff.mpr hCE))
  omega

omit [Finite G] in
/-- The core of the normal layer closure is its intersection with O₂(H). -/
theorem equalityCore_eq_intersection :
    equalityCore L R z = equalityLayerClosure L R z ⊓
      pCore 2 (centralizer ({z} : Set G)) := by
  apply le_antisymm
  · exact le_inf (pCoreIn_le 2 _) (le_sSup ⟨inferInstance, isPGroup_pCoreIn 2 _⟩)
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.to_le inf_le_right) inf_le_left
      (by rw [normalizer_eq_top]; exact le_top)

/-- The actual layer has the same eight-group intersection with P and O₂(H). -/
theorem equality_layer_inf_core
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    layer L R ⊓ (equalityCore L R z).map (centralizer ({z} : Set G)).subtype =
      layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2 := by
  rw [equalityCore_eq_intersection, map_inf _ _ _ (centralizer ({z} : Set G)).subtype_injective]
  rw [← inf_assoc, inf_eq_left.mpr (equality_layer_le_closure h611 hz)]
  rfl

/-- Centralizing P forces centralizing K, using the natural hyperplane bound. -/
theorem LocalAnalysis.equality_core_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    centralizer (equalityCore L R z : Set (centralizer ({z} : Set G))) =
      centralizer (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let C := centralizer (P : Set H)
  let E := layer L R ⊓ H.pCoreIn 2
  have hCP : C.map H.subtype ≤ H.pCoreIn 2 := by
    rintro _ ⟨x, hx, rfl⟩
    apply (A.action_kernel x x.property).mp
    intro u hu
    obtain ⟨uH, huU, rfl⟩ := hu
    have hp := A.equalityClosure_le_equalityCore h611 hz huU
    change ⁅(x : G), (uH : G)⁆ ∈ zpowers z
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mem_centralizer_iff.mp hx uH hp)).symm]
    exact one_mem _
  have hCE : C.map H.subtype ≤ centralizer (E : Set G) := by
    rw [show E = layer L R ⊓ H.pCoreIn 2 from rfl, ← equality_layer_inf_core h611 hz]
    rintro _ ⟨c, hc, rfl⟩ e he
    obtain ⟨p, hp, rfl⟩ := he.2
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc p hp)
  have hCV : C.map H.subtype ≤ centralizer (layer L R : Set G) := by
    let := h611.layer_elementary
    exact natural_eight_centralizer hnatural.2.1
      (A.normalizer_layer.trans ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal))
      inf_le_left A.layer_core_card (hCP.trans (A.equalityCoreH_normalizes_layer h611 hz)) hCE
  have hVC : (layer L R).subgroupOf H ≤ centralizer (C : Set H) := by
    intro v hv c hc
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hCV (mem_map_of_mem _ hc)) v hv).symm
  have hKC : equalityLayerClosure L R z ≤ centralizer (C : Set H) :=
    normalClosure_le_normal hVC
  exact le_antisymm (le_centralizer_iff.mp hKC) (centralizer_le (pCoreIn_le 2 _))

/-- Conjugation on the canonical core modulo its intrinsic center. -/
noncomputable def equalityOuterAction (L R : Subgroup G) (z : G) :
    centralizer ({z} : Set G) →*
      MulAut ((equalityCore L R z) ⧸ center (equalityCore L R z)) :=
  (quotientAut (center (equalityCore L R z))).comp MulAut.conjNormal

omit [Finite G] in
@[simp] theorem equalityOuterAction_apply (L R : Subgroup G) (z : G)
    (x : centralizer ({z} : Set G)) :
    equalityOuterAction L R z x =
      quotientAut (center (equalityCore L R z)) (MulAut.conjNormal x) := by rfl

/-- The source kernel R is the product P C_H(K), with no splitting assertion. -/
theorem LocalAnalysis.equalityOuterAction_ker
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    (equalityOuterAction L R z).ker =
      equalityCore L R z ⊔ centralizer
        (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let f : H →* MulAut P := MulAut.conjNormal
  have hf (p : P) : f (p : H) = MulAut.conj p := by
    ext q
    rfl
  rw [← A.equality_core_centralizer h611 hnatural hz]
  apply le_antisymm
  · intro x hx
    obtain ⟨p, hp⟩ := (hplus.some.quotientAut_eq_one_iff_inner (f x)).mp hx
    have hc : (p : H)⁻¹ * x ∈ centralizer (P : Set H) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      change f ((p : H)⁻¹ * x) = 1
      rw [map_mul, map_inv, hf, hp, inv_mul_cancel]
    have hm := (P ⊔ centralizer (P : Set H)).mul_mem
      (mem_sup_left p.property) (mem_sup_right hc)
    simpa only [mul_inv_cancel_left] using hm
  · apply sup_le
    · intro p hp
      apply (hplus.some.quotientAut_eq_one_iff_inner (f p)).mpr
      exact ⟨⟨p, hp⟩, (hf ⟨p, hp⟩).symm⟩
    · intro x hx
      have he : f x = 1 := by
        change x ∈ (MulAut.conjNormal : H →* MulAut P).ker
        rwa [MulAut.conjNormal_ker_eq_centralizer]
      change quotientAut (center P) (f x) = 1
      rw [he, map_one]

/-- The central-quotient action kernel lies in the actual involution two-core. -/
theorem LocalAnalysis.equalityOuterAction_ker_le
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    (equalityOuterAction L R z).ker ≤ pCore 2 (centralizer ({z} : Set G)) := by
  rw [A.equalityOuterAction_ker h611 hnatural hz hplus]
  apply sup_le (equalityCore_eq_intersection.le.trans inf_le_right)
  intro c hc
  obtain ⟨x, hx, he⟩ := A.equality_centralizer_le_involution_core (mem_map_of_mem _ hc)
  exact (Subtype.ext he : x = c) ▸ hx

/-- Inside P, the centralizer of V is precisely the actual eight P ∩ V. -/
theorem LocalAnalysis.equality_core_layer_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    equalityCore L R z ⊓ centralizer
        ((layer L R).subgroupOf (centralizer ({z} : Set G)) :
          Set (centralizer ({z} : Set G))) =
      equalityCore L R z ⊓ (layer L R).subgroupOf (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let V := (layer L R).subgroupOf H
  let E := P ⊓ V
  have hVH : layer L R ≤ H := layer_le_involution_centralizer h611 hz
  have hc : Nat.card E = 8 := by
    rw [← card_map_of_injective H.subtype_injective]
    change Nat.card ((P ⊓ V).map H.subtype) = 8
    rw [map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hVH,
      inf_comm, equality_layer_inf_core h611 hz]
    exact A.layer_core_card
  let := h611.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_injective
    (inclusion (show E ≤ V from inf_le_right)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (E.subgroupOf P) := IsElementaryAbelian.subgroupOf inf_le_left
  obtain ⟨d⟩ := hplus
  have hself := inf_centralizer_elementary_eight_of_quaternion_factors
    d.left d.right (E.subgroupOf P) d.left_model d.right_model d.intersection_card
    d.commute ((Nat.card_congr (subgroupOfEquivOfLe (show E ≤ P from inf_le_left)).toEquiv).trans hc)
    (by rw [d.span]; exact le_top)
  rw [d.span, top_inf_eq] at hself
  apply le_antisymm
  · intro p hp
    have hm : (⟨p, hp.1⟩ : P) ∈ centralizer (E.subgroupOf P : Set P) := by
      intro e he
      exact Subtype.ext (hp.2 e he.2)
    rw [hself] at hm
    exact hm
  · exact le_inf inf_le_left (inf_le_right.trans (le_centralizer V))

/-- The kernel centralizer is C_R(V) = (P ∩ V) C_H(K), with literal embeddings. -/
theorem LocalAnalysis.equality_outer_kernel_layer_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    (equalityOuterAction L R z).ker ⊓ centralizer
        ((layer L R).subgroupOf (centralizer ({z} : Set G)) :
          Set (centralizer ({z} : Set G))) =
      (equalityCore L R z ⊓ (layer L R).subgroupOf (centralizer ({z} : Set G))) ⊔
        centralizer (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let V := (layer L R).subgroupOf H
  let D := centralizer (equalityLayerClosure L R z : Set H)
  let := h611.layer_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf
    (layer_le_involution_centralizer h611 hz)
  have hDV : D ≤ centralizer (V : Set H) := centralizer_le le_normalClosure
  rw [A.equalityOuterAction_ker h611 hnatural hz hplus]
  change (P ⊔ D) ⊓ centralizer (V : Set H) = (P ⊓ V) ⊔ D
  apply le_antisymm
  · intro x hx
    have hprod : x ∈ (P : Set H) * (D : Set H) := by
      rw [← coe_mul_of_left_le_normalizer_right P D le_normalizer_of_normal]
      exact hx.1
    obtain ⟨p, hp, d, hd, rfl⟩ := hprod
    have hpc : p ∈ centralizer (V : Set H) := by
      have hh := (centralizer (V : Set H)).mul_mem hx.2
        ((centralizer (V : Set H)).inv_mem (hDV hd))
      simpa only [mul_inv_cancel_right] using hh
    have hpV : p ∈ P ⊓ V := by
      rw [← A.equality_core_layer_centralizer h611 hz hplus]
      exact ⟨hp, hpc⟩
    exact ((P ⊓ V) ⊔ D).mul_mem (mem_sup_left hpV) (mem_sup_right hd)
  · apply sup_le
    · exact le_inf (inf_le_left.trans le_sup_left)
        (inf_le_right.trans (le_centralizer V))
    · exact le_inf le_sup_right hDV

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
