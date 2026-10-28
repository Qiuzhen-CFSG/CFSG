module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionMarkedQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCoreImage
public import Theory.GroupTheory.QuaternionCentralProductSymmetricFiveImage

/-!
# The canonical outer four-group in the marked quotient

If P had image inside the image of L, its Sylow containment would force it
to centralize Z_S. This contradicts C_V(P)=⟨z⟩. Thus its image is outer.
The quotient kills Z(P), so the image is elementary of order at most four.
Its kernel is elementary inside Q and has order at most eight. Since
|P|=32, both bounds are attained. The output retains a surjective map
from M, its exact kernel Q, and the image of L under that same map.

These source inputs remove the order and outer-image assumptions from
the subsequent Sylow and centralizer calculation; that calculation remains
with the equality-geometry owner.
Source: Aschbacher–Smith, proof of 6.2.13, printed p.687.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The canonical core has an outer image already modulo the local core:
an inner image would fix the natural plane instead of the central line. -/
theorem LocalAnalysis.equality_core_not_le_local_core_join
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ¬ (equalityCore L R z).map (centralizer ({z} : Set G)).subtype ≤
      L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let P := (equalityCore L R z).map (centralizer ({z} : Set G)).subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  intro hP
  have hPT : P ≤ (T : Subgroup G) := equalityCore_le_sylow hTH
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [← equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hLQ : L ≤ normalizer (Q : Set G) :=
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hZP : ZS (T : Subgroup G) L R ≤ centralizer (P : Set G) := by
    intro v hv p hp
    have hprod : p ∈ (L : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right L Q hLQ]
      exact hP hp
    obtain ⟨l, hl, q, hq, rfl⟩ := hprod
    have hlT : l ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem (hPT hp) ((T : Subgroup G).inv_mem (hQT hq))
      simpa only [mul_inv_cancel_right] using hh
    have hlv : l * v = v * l := hv.2 l ⟨hlT, hl⟩
    have hqv : q * v = v * q := (local_core_centralizes_layer h611 hq v hv.1).symm
    calc
      (l * q) * v = l * (q * v) := mul_assoc _ _ _
      _ = l * (v * q) := congrArg (l * ·) hqv
      _ = (l * v) * q := (mul_assoc _ _ _).symm
      _ = (v * l) * q := congrArg (· * q) hlv
      _ = v * (l * q) := mul_assoc _ _ _
  have hZ : ZS (T : Subgroup G) L R ≤ zpowers z := by
    rw [← A.equality_layer_core_centralizer h611 hnatural hz horder hTH hbranch]
    exact le_inf inf_le_left hZP
  have hc := card_le_of_le hZ
  rw [(h611.natural_ZS_geometry hnatural).2.1, Nat.card_zpowers, horder] at hc
  omega


/-- The literal embedding of the canonical core into the maximal local group. -/
noncomputable def equalityCoreToMaximal
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hTM : (T : Subgroup G) ≤ M) : equalityCore L R z →* M :=
  ((centralizer ({z} : Set G)).subtype.comp (equalityCore L R z).subtype).codRestrict M
    (fun p => hTM (equalityCore_le_sylow hTH (mem_map_of_mem _ p.property)))

omit [Finite G] in
/-- Evaluation of the literal embedding, without exposing its implementation. -/
@[simp] theorem equalityCoreToMaximal_coe
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hTM : (T : Subgroup G) ≤ M) (p : equalityCore L R z) :
    (equalityCoreToMaximal hTH hTM p : G) = (p.val : G) := by rfl

/-- The marked quotient carries the actual extraspecial core to an outer
four-group, with elementary kernel of order eight. -/
theorem LocalAnalysis.equality_core_permutation_image
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    ∃ f : M →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M ∧
      (L.subgroupOf M).map f = alternatingGroup (Fin 5) ∧
      let fP := f.comp (equalityCoreToMaximal hTH h611.sylow_le (L := L) (R := R))
      IsElementaryAbelian 2 fP.range ∧ Nat.card fP.ker = 8 ∧ Nat.card fP.range = 4 ∧
        ¬ fP.range ≤ alternatingGroup (Fin 5) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
  let := A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  obtain ⟨e, he⟩ := A.equality_marked_local_core_quotient h611 hnatural hz horder hTH hbranch
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf M))
  have hf : f.ker = Q.subgroupOf M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let j : P →* M := equalityCoreToMaximal hTH h611.sylow_le
  let fP := f.comp j
  have hk (p : P) : fP p = 1 ↔ (p.val : G) ∈ Q := by
    change j p ∈ f.ker ↔ _
    rw [hf]
    rfl
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hZ : center P ≤ fP.ker := by
    intro p hpZ
    have hzP : p.val ∈ M22Recognition.CentralizerExtension.coreCenter P :=
      mem_map_of_mem P.subtype hpZ
    rw [hp.core_center] at hzP
    apply (hk p).mpr
    exact (h611.layer_le_V.trans (reduced_le_core h611.V_mem))
      ((zpowers_le.mpr hz.1) hzP)
  have hker : IsElementaryAbelian 2 fP.ker := by
    let g : fP.ker →* Q :=
      (H.subtype.comp (P.subtype.comp fP.ker.subtype)).codRestrict Q
        (fun p => (hk p.val).mp p.property)
    apply IsElementaryAbelian.of_injective g
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : Q => (q : G)) hab
  obtain ⟨hE, h8, h4⟩ := hp.plusType.some.symmetricFive_image fP hZ hker
  refine ⟨f, e.surjective.comp (QuotientGroup.mk'_surjective _), hf, he, hE, h8, h4, ?_⟩
  intro hin
  apply A.equality_core_not_le_local_core_join h611 hnatural hz horder hTH hbranch
  rintro p ⟨pH, hpP, rfl⟩
  have hi : j ⟨pH, hpP⟩ ∈ ((L.subgroupOf M).map f).comap f := by
    change fP ⟨pH, hpP⟩ ∈ (L.subgroupOf M).map f
    rw [he]
    exact hin (MonoidHom.mem_range.mpr ⟨⟨pH, hpP⟩, rfl⟩)
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans (sup_le h611.L_le h611.sylow_le)
  rw [comap_map_eq, hf, ← subgroupOf_sup h611.L_le hQM] at hi
  exact hi

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
