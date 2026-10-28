module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuNestedQuotients
public import CFSG.Quasithin.MainConverse.Transport
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults

/-!
# The Mathieu local comparison inside J₄

The literal quotient of the native J₄ max1 subgroup is M₂₄ with a
binary kernel. Restriction and that quotient preserve the original local
components and their intrinsic two-core quotients. The complete Mathieu
comparison bounds a local seven-section by 168, or identifies its quotient
as PSL₄(2) or M₂₄. Strict containment of the original PSL₃(2) section
excludes the bound by local-component rigidity.

The source application in Section09/NaturalSource/Components/JankoMathieu
uses the original plane action to exclude both remaining quotients.
Placement outside this Mathieu local subgroup is a separate obligation.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859, and A.3.12,
printed pp.47--48. The actual matrix subgroup and quotient retain the
certificate provenance of the imported J₄ carrier modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
open FiveLocalFF.SolvableQuotients

/-- The complete core-quotient alternatives needed for a local seven-section in M24. -/
theorem mathieu_local_models {G : Type*} [Group G] [Finite G]
    (e : G ≃* Sporadic.Mathieu.M24) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hq : IsQuasisimple (B ⧸ pCore 2 B)) (h7 : 7 ∣ Nat.card (B ⧸ pCore 2 B)) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 ∨
      Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24) := by
  by_cases hc : pCore 2 B = ⊥
  · let a : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    let := hq.of_mulEquiv a
    have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S
      (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m24_evenCharacteristic S)
      hl hn
    have ht := MathieuRank.eq_top_of_quasisimple_faithful_sylow e S B (hsq.subgroup B) hc
      ((Nat.card_congr a.toEquiv) ▸ h7) hn hf
    exact Or.inr (Or.inr ⟨a.trans ((MulEquiv.subgroupCongr ht).trans ((topEquiv).trans e))⟩)
  · rcases MathieuNested.local_models_of_core_ne_bot e S B hl hn hc h7 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

open Janko4 Janko4.Cardinality Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four
local notation "K" => localKernel matrixA_mul_self matrixB_pow_four

/-- The literal Mathieu quotient of the native J4 local subgroup preserves the plane section. -/
theorem max1_local_models (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (S : Sylow 2 M) (B : Subgroup M) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup M) ≤ normalizer (B : Set M))
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (h7 : 7 ∣ Nat.card (B ⧸ pCore 2 B)) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 ∨
      Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24) := by
  let q := QuotientGroup.mk' K
  have hp : IsPGroup 2 K := by
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    exact IsElementaryAbelian.isPGroup 2 K
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact hp.comap_subtype
  let a := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := hp.isNilpotent
    infer_instance
  have hm := mathieu_local_models (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four)
    (ChapterE.Structure.sqtk_two_quotient hsq K hp)
    (S.mapSurjective (QuotientGroup.mk'_surjective K)) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono (f := q) hn).trans (B.le_normalizer_map q))
    (hquasi.of_mulEquiv a) ((Nat.card_congr a.toEquiv) ▸ h7)
  rcases hm with hc | hm | hm3
  · exact Or.inl ((Nat.card_congr a.toEquiv).trans_le hc)
  · exact Or.inr (Or.inl (hm.of_mulEquiv a))
  · exact Or.inr (Or.inr ⟨a.trans hm3.some⟩)

/-- Restriction to the actual max1 subgroup retains the supplied full Sylow and original core quotient. -/
theorem pair_le_max1_models (hsq : IsSQTK KnownSimple.IsKnownSimple Model)
    (S : Sylow 2 Model) (B : Subgroup Model) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (h7 : 7 ∣ Nat.card (B ⧸ pCore 2 B))
    (hBM : B ≤ M) (hSM : (S : Subgroup Model) ≤ M) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 ∨
      Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24) := by
  let d := subgroupOfEquivOfLe hBM
  let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hn' : (S.subtype hSM : Subgroup M) ≤ normalizer (B.subgroupOf M : Set M) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hn hs) (b : Model)
  rcases max1_local_models (hsq.subgroup M) (S.subtype hSM) (B.subgroupOf M)
      (local_restrict hl hBM) hn' (hquasi.of_mulEquiv a.symm)
      ((Nat.card_congr a.symm.toEquiv) ▸ h7) with hc | hm | hm3
  · exact Or.inl ((Nat.card_congr a.symm.toEquiv).trans_le hc)
  · exact Or.inr (Or.inl (hm.of_mulEquiv a.symm))
  · exact Or.inr (Or.inr ⟨a.symm.trans hm3.some⟩)

/-- The same comparison along any actual J4 marking, including ambient conjugation. -/
theorem pair_map_le_max1_models {G : Type*} [Group G] [Finite G]
    (e : G ≃* Model) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (h7 : 7 ∣ Nat.card (B ⧸ pCore 2 B))
    (hBM : B.map e.toMonoidHom ≤ M) (hSM : (S : Subgroup G).map e.toMonoidHom ≤ M) :
    Nat.card (B ⧸ pCore 2 B) ≤ 168 ∨
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 ∨
      Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24) := by
  let d := e.subgroupMap B
  let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  rcases pair_le_max1_models (hsq.knownSimple_of_equiv e)
      (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
      (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)
      ((map_mono (f := e.toMonoidHom) hn).trans (B.le_normalizer_map e.toMonoidHom))
      (hquasi.of_mulEquiv a) ((Nat.card_congr a.toEquiv) ▸ h7) hBM hSM with hc | hm | hm3
  · exact Or.inl ((Nat.card_congr a.toEquiv).trans_le hc)
  · exact Or.inr (Or.inl (hm.of_mulEquiv a))
  · exact Or.inr (Or.inr ⟨a.trans hm3.some⟩)
/-- A strict enlargement of the original local PSL3(2) section in a marked
Mathieu local subgroup has quotient PSL4(2) or M24. -/
theorem strict_three_pair_map_le_max1_models {G : Type*} [Group G] [Finite G]
    (e : G ≃* Model) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) {A B : Subgroup G}
    (ha : A ∈ localCComponents S) (hb : B ∈ localCComponents S) (hlt : A < B)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B))
    (ha3 : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (hBM : B.map e.toMonoidHom ≤ M) (hSM : (S : Subgroup G).map e.toMonoidHom ≤ M) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 ∨
      Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24) := by
  have ha168 : Nat.card (A ⧸ pCore 2 A) = 168 := by
    obtain ⟨k,_,_,hk,⟨f⟩⟩ := ha3
    rw [Nat.card_congr f.toEquiv,Matrix.PSL3.LinearThree.card_projective,hk]
    norm_num
  let q := QuotientGroup.mk' (pCore 2 B)
  let A' := A.subgroupOf B
  have hk : IsPGroup 2 (q.subgroupMap A').ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  let d := subgroupOfEquivOfLe hlt.le
  let a := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
    ((q.subgroupMap A').pCoreQuotientEquiv (q.subgroupMap_surjective A') hk)
  have hd := (card_quotient_dvd_card (pCore 2 (A'.map q))).trans
    (A'.map q).card_subgroup_dvd_card
  rw [←Nat.card_congr a.toEquiv,ha168] at hd
  have h7 : 7 ∣ Nat.card (B ⧸ pCore 2 B) := (by decide : 7 ∣ 168).trans hd
  rcases pair_map_le_max1_models e hsq S B hb hn hquasi h7 hBM hSM with hc | hm
  · exact (hlt.ne (BinaryNested.local_eq_of_twoCore_card_le S ha hb hlt.le
      (hc.trans_eq ha168.symm))).elim
  · exact hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
