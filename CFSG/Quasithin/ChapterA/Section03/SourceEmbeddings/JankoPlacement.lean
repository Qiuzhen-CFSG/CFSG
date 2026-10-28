module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoSmallAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement

/-!
# Involution-centralizer placement of the original J₄ plane pair

The nontrivial intrinsic two-core gives a maximal two-local containing
both the plane image and its normalizing full Sylow. The native
normal-elementary catalogue places this pair in max1 or gives a common
invariant elementary subgroup of order at most eight. The literal Mathieu
comparison excludes max1 under the original plane-model exclusions.
Small-image rigidity makes the larger component fix the small subgroup,
so its centralizer is even. The original Sylow then fixes an involution
in that centralizer. All transports use actual ambient equivalences.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859 and A.3.12,
printed pp.47--48. The imported native catalogue retains its matrix
certificate and ATLAS provenance.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
open FiveLocalFF.SolvableQuotients Janko4 Janko4.Cardinality Janko4.LocalStructure
open Janko4.OuterReduction.OddIndex
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four

private noncomputable def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_placement (hsq : IsSQTK KnownSimple.IsKnownSimple Model)
    {A B : Subgroup Model}
    (ha : A ∈ localCComponents markedSylow) (hb : B ∈ localCComponents markedSylow)
    (hlt : A < B)
    (hna : twoSubgroup ≤ normalizer (A : Set Model))
    (hnb : twoSubgroup ≤ normalizer (B : Set Model))
    (ha3 : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (hc : pCore 2 B ≠ ⊥)
    (hno4 : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hnoM : ¬ Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24)) :
    ∃ z : Model, orderOf z = 2 ∧ B ⊔ twoSubgroup ≤ centralizer ({z} : Set Model) := by
  obtain ⟨N,hN,hBN,hSN⟩ := exists_maximal_two_local markedSylow B hnb hc
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  let E := R.map (markedSylow : Subgroup Model).subtype
  have he : IsElementaryAbelian 2 E := by
    let := heR
    exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  have hBE : B ≤ normalizer (E : Set Model) := hNR ▸ hBN
  have hSE : twoSubgroup ≤ normalizer (E : Set Model) := hNR ▸ hSN
  have htwo : 2 ∣ Nat.card (centralizer (B : Set Model)) := by
    rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative (B ⊔ twoSubgroup) E
        (map_subtype_le R) hne he le_sup_right (sup_le hBE hSE) with hm | ⟨U,hu,hUE,hel,hcard,hn⟩
    · rcases strict_three_pair_map_le_max1_models (MulEquiv.refl _) hsq markedSylow
        ha hb hlt hnb hquasi ha3 (by simpa using le_sup_left.trans hm)
        (by change (markedSylow : Subgroup Model).map (MonoidHom.id Model) ≤ M; rw [Subgroup.map_id]; exact le_sup_right.trans hm) with hm | hm
      · exact (hno4 hm).elim
      · exact (hnoM hm).elim
    · have hBU := strict_three_centralizes_small markedSylow ha hb hlt hna hnb ha3
        hquasi hel hcard (le_sup_left.trans hn)
      have hUC : U ≤ centralizer (B : Set Model) := le_centralizer_iff.mp hBU
      let := hel
      obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
      have hk0 : k ≠ 0 := by
        intro hz
        rw [hz,pow_zero] at hk
        exact hu (U.eq_bot_of_card_eq hk)
      have h2 : 2 ∣ Nat.card U := by rw [hk]; exact dvd_pow_self 2 hk0
      exact h2.trans (card_dvd_of_le hUC)
  exact exists_involution_centralizing_normalizing_two_group B twoSubgroup
    markedSylow.isPGroup' hnb htwo

/-- The original strict plane pair in J4 lies in an actual involution centralizer.
The native normal-elementary catalogue, literal Mathieu quotient and small
image rigidity discharge the placement; no classifier callback is assumed. -/
theorem involution_centralizer_placement {G : Type*} [Group G] [Finite G]
    (e : G ≃* Model) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) {A B : Subgroup G}
    (ha : A ∈ localCComponents S) (hb : B ∈ localCComponents S) (hlt : A < B)
    (hna : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hnb : (S : Subgroup G) ≤ normalizer (B : Set G))
    (ha3 : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (hc : pCore 2 B ≠ ⊥)
    (hno4 : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hnoM : ¬ Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24)) :
    ∃ z : G, orderOf z = 2 ∧ B ⊔ (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model Q markedSylow
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = twoSubgroup := by
    have he := congrArg (fun P : Sylow 2 Model => (P : Subgroup Model)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
    rw [hf,←map_map]
    exact he
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have ha' := Chapter1.Section02.localCComponents_map_of_solvable_ker ha f.toMonoidHom
  have hb' := Chapter1.Section02.localCComponents_map_of_solvable_ker hb f.toMonoidHom
  have hna' := (map_mono (f := f.toMonoidHom) hna).trans (A.le_normalizer_map f.toMonoidHom)
  have hnb' := (map_mono (f := f.toMonoidHom) hnb).trans (B.le_normalizer_map f.toMonoidHom)
  rw [hS] at ha' hb' hna' hnb'
  let da := f.subgroupMap A
  let db := f.subgroupMap B
  let a := QuotientGroup.congr _ _ da (pCore_map_iso 2 da)
  let b := QuotientGroup.congr _ _ db (pCore_map_iso 2 db)
  have hlt' : A.map f.toMonoidHom < B.map f.toMonoidHom :=
    lt_of_le_of_ne (map_mono hlt.le) (fun h => hlt.ne ((map_injective f.injective) h))
  have hc' : pCore 2 (B.map f.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := db.toMonoidHom) _ db.injective).mp
    rw [pCore_map_iso 2 db]
    exact hz
  obtain ⟨z,hz,hpair⟩ := fixed_placement (hsq.knownSimple_of_equiv f)
    ha' hb' hlt' hna' hnb' (ha3.of_mulEquiv a.symm) (hquasi.of_mulEquiv b) hc'
    (fun hm => hno4 (hm.of_mulEquiv b)) (fun hm => hnoM ⟨b.trans hm.some⟩)
  refine ⟨f.symm z,by rw [MulEquiv.orderOf_eq]; exact hz,?_⟩
  have hh := map_mono (f := f.symm.toMonoidHom) hpair
  rw [Subgroup.map_sup,←hS,map_map,map_map] at hh
  have hid : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [hid,map_id,map_id,map_centralizer_equiv,Set.image_singleton] at hh
  exact hh
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
