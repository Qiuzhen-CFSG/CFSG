module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionResidual
public import CFSG.Quasithin.Chapter6.Section01.QuotientA5
public import Theory.GroupTheory.Commutator.QuasisimpleTwoEscape
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The commutator layer in the equality extension

The canonical extraspecial core P escapes the elementary group Q = O₂(LT),
while [Q,P] lies in V. Quasisimple two-generation then gives [Q,L] = V.
Since Q = O₂(M) and L is normal in M, this identifies V as an M-normal
subgroup. The earlier-source upper bound gives N_G(V) = M and hence
N_G(Q) ≤ N_G(V), discharging the normalizer premise of the transfer step.
No equality V = O₂(L), marked S₅ quotient, or fusion premise is assumed.

Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private theorem natural_local_quotient_quasisimple
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n) :
    IsQuasisimple ((L.subgroupOf (L ⊔ (T : Subgroup G))) ⧸
      pCore 2 (L.subgroupOf (L ⊔ (T : Subgroup G)))) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  obtain ⟨e⟩ := h611.quotient_a5_of_n_eq_two hnatural.1
  let c := subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e).symm

/-- The canonical core moves Q only inside the natural layer. -/
theorem LocalAnalysis.equality_core_local_commutator
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L R z))) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,
      (equalityCore L R z).map (centralizer ({z} : Set G)).subtype⁆ ≤ layer L R := by
  let H := centralizer ({z} : Set G)
  let P := (equalityCore L R z).map H.subtype
  let D := equalityCentralizer L R z
  have hQ : (L ⊔ (T : Subgroup G)).pCoreIn 2 = layer L R ⊔ D := by
    rw [← equality_sylow_centralizer_eq_core h611 hnatural]
    exact A.equality_sylow_layer_centralizer h611 hnatural hz hTH hplus
  have hDP : D ≤ centralizer (P : Set G) := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨p, hp, rfl⟩
    exact congrArg Subtype.val (hd p (pCoreIn_le 2 _ hp))
  rw [hQ]
  apply commutator_sup_le_of_relative_normal (T : Subgroup G) (layer L R) D P
    (layer L R) h611.sylow_normalizes_layer h611.layer_le_T
    (A.equality_centralizer_le_sylow hTH)
  · exact le_normalizer_iff_commutator_le_left.mp
      ((equalityCore_le_sylow hTH).trans h611.sylow_normalizes_layer)
  · exact (commutator_eq_bot_iff_le_centralizer.mpr hDP).le.trans bot_le

/-- The natural layer is exactly the commutator of the local core with L. -/
theorem LocalAnalysis.equality_local_core_commutator
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, L⁆ = layer L R := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let V := layer L R
  let H := centralizer ({z} : Set G)
  let P := (equalityCore L R z).map H.subtype
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  let : IsElementaryAbelian 2 Q :=
    A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  have hPX : P ≤ X := (equalityCore_le_sylow hTH).trans le_sup_right
  have hVX : V ≤ X := h611.layer_le_L.trans le_sup_left
  have hXV : X ≤ normalizer (V : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural.2.1
    exact sup_le hmodel.normalizes h611.sylow_normalizes_layer
  have hPQ : ¬ P ≤ Q := by
    intro hh
    let f : equalityCore L R z →* Q :=
      (H.subtype.comp (equalityCore L R z).subtype).codRestrict Q
        (fun p => hh (mem_map_of_mem H.subtype p.property))
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun q : Q => (q : G)) hab))
    let : IsElementaryAbelian 2 (equalityCore L R z) := IsElementaryAbelian.of_injective f hf
    have hc : center (equalityCore L R z) = ⊤ := Subgroup.center_eq_top
    have hd := hp.plusType.some.center_card
    rw [hc, card_top, hp.plusType.some.card] at hd
    norm_num at hd
  let LX := L.subgroupOf X
  let TX := (T : Subgroup G).subgroupOf X
  let VX := V.subgroupOf X
  let PX := P.subgroupOf X
  let : LX.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h611.sylow_normalizes_L)
  let : VX.Normal := normal_subgroupOf_of_le_normalizer hXV
  let : IsQuasisimple (LX ⧸ pCore 2 LX) := natural_local_quotient_quasisimple h611 hnatural
  have hgen : LX ⊔ TX = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right)]
    exact subgroupOf_self _
  have hne : ¬ PX ≤ pCore 2 X := by
    intro hh
    apply hPQ
    have hm := map_mono (f := X.subtype) hh
    rwa [map_subgroupOf_eq_of_le hPX] at hm
  have hQQ : ⁅pCore 2 X, pCore 2 X⁆ ≤ VX := by
    intro x hx
    have hm := mem_map_of_mem X.subtype hx
    rw [map_commutator] at hm
    change (x : G) ∈ ⁅Q, Q⁆ at hm
    rw [commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative Q)] at hm
    change (x : G) ∈ V
    exact (mem_bot.mp hm) ▸ V.one_mem
  have hQP : ⁅pCore 2 X, PX⁆ ≤ VX := by
    intro x hx
    apply A.equality_core_local_commutator h611 hnatural hz hTH hp.plusType
    have hm := mem_map_of_mem X.subtype hx
    rwa [map_commutator, map_subgroupOf_eq_of_le hPX] at hm
  have hh := commutator_le_of_quasisimple_two_escape LX TX VX PX
    h611.local_mem.1.prop.1 T.isPGroup'.comap_subtype hgen
    ((isPGroup_pCoreIn 2 (equalityLayerClosure L R z)).map H.subtype).comap_subtype hne hQQ hQP
  have hm := map_mono (f := X.subtype) hh
  rw [map_commutator, map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left),
    map_subgroupOf_eq_of_le hVX] at hm
  exact le_antisymm hm (commutator_mono (reduced_le_core h611.V_mem) le_rfl)

/-- The equality layer is normal in the maximal local subgroup, before
the order-four centralizer alternative is excluded. -/
theorem LocalAnalysis.equality_maximal_normalizes_layer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    M ≤ normalizer (layer L R : Set G) := by
  rw [← A.equality_local_core_commutator h611 hnatural hz horder hTH hbranch,
    A.equality_local_core_eq_maximal_core h611 hnatural hz horder hTH hbranch]
  have hMQ : M ≤ normalizer (M.pCoreIn 2 : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hML := (normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal
  intro m hm
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hMQ hm),
    mem_normalizer_iff_map_conj_eq.mp (hML hm)]

/-- The layer normalizer is exactly M, with the earlier-source upper bound. -/
theorem LocalAnalysis.equality_layer_normalizer_eq
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    normalizer (layer L R : Set G) = M :=
  le_antisymm A.normalizer_layer
    (A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch)

/-- Relative normality of the literal recognition layer follows from its
commutator characterization, without assuming V = O₂(L). -/
theorem LocalAnalysis.equality_layer_normal
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ((layer L R).subgroupOf M).Normal :=
  normal_subgroupOf_of_le_normalizer
    (A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch)

/-- This discharges the normalizer premise of elementary-four transfer
directly from the equality source hypotheses. -/
theorem LocalAnalysis.equality_core_normalizer_normalizes_layer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
      normalizer (layer L R : Set G) := by
  rw [equality_local_core_normalizer h611
    (A.equality_local_core_normal h611 hnatural hz horder hTH hbranch)]
  exact A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
