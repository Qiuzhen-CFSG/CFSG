module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoFirstCentralizer
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# The remaining strict J₄ plane pair is impossible

The native normal-elementary catalogue and small-image rigidity put the
strict plane image and the full Sylow in an actual involution centralizer.
The first centralizer cannot contain the original normalized local
PSL₃(2) section, by its literal M₂₂ projection. The second has insufficient
two-part to contain the full J₄ Sylow. Actual carrier equivalences preserve
all local components, inclusions, normalizers and quotient exclusions.

This closes the finite-model comparison in the J₄ branch of 12.9.3;
Section09/NaturalSource/Components/JankoComplete discharges every premise
from the original flag. Source: Aschbacher--Smith, printed pp.858--859.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
open Janko4 Janko4.InvolutionCentralizers
attribute [local irreducible] modelGroup matrixA matrixB

/-- Neither actual involution centralizer contains a full Sylow and a
normalized local PSL3(2) section. -/
theorem no_centralizing_involution (S : Sylow 2 Model) (A : Subgroup Model)
    (ha : A ∈ localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (A : Set Model))
    (hm : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (z : Model) (hz : orderOf z = 2)
    (hp : A ⊔ (S : Subgroup Model) ≤ Subgroup.centralizer ({z} : Set Model)) : False := by
  let C := Subgroup.centralizer ({z} : Set Model)
  have hAC : A ≤ C := le_sup_left.trans hp
  have hSC : (S : Subgroup Model) ≤ C := le_sup_right.trans hp
  rcases centralizer_equiv_first_or_second z hz with he | he
  · obtain ⟨e⟩ := he
    let d := subgroupOfEquivOfLe hAC
    let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    apply not_three_of_first_equiv e (S.subtype hSC) (A.subgroupOf C)
      (local_restrict ha hAC) _ (hm.of_mulEquiv a)
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : Model)
  · obtain ⟨e⟩ := he
    have hpow : 2^20 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by
      rw [Cardinality.model_card]
      norm_num)
    have hd := hpow.trans (card_dvd_of_le hSC)
    rw [Nat.card_congr e.toEquiv,Second.ambient_card] at hd
    norm_num at hd

/-- Native J4 exclusion of the remaining marked strict plane pair. -/
theorem not_strict_three_pair_native (hsq : IsSQTK KnownSimple.IsKnownSimple Model)
    (S : Sylow 2 Model) {A B : Subgroup Model}
    (ha : A ∈ localCComponents S) (hb : B ∈ localCComponents S) (hlt : A < B)
    (hna : (S : Subgroup Model) ≤ normalizer (A : Set Model))
    (hnb : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (ha3 : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (hc : pCore 2 B ≠ ⊥)
    (hno4 : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hnoM : ¬ Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24)) : False := by
  obtain ⟨z,hz,hp⟩ := involution_centralizer_placement (MulEquiv.refl _) hsq S
    ha hb hlt hna hnb ha3 hquasi hc hno4 hnoM
  exact no_centralizing_involution S A ha hna ha3 z hz ((sup_le_sup_right hlt.le _).trans hp)

/-- Actual equivalences preserve the entire strict pair, both normalizers,
and the intrinsic quotient exclusions. -/
theorem not_strict_three_pair {G : Type*} [Group G] [Finite G]
    (e : G ≃* Model) (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) {A B : Subgroup G}
    (ha : A ∈ localCComponents S) (hb : B ∈ localCComponents S) (hlt : A < B)
    (hna : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hnb : (S : Subgroup G) ≤ normalizer (B : Set G))
    (ha3 : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B)) (hc : pCore 2 B ≠ ⊥)
    (hno4 : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hnoM : ¬ Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24)) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  let da := e.subgroupMap A
  let db := e.subgroupMap B
  let a := QuotientGroup.congr _ _ da (pCore_map_iso 2 da)
  let b := QuotientGroup.congr _ _ db (pCore_map_iso 2 db)
  have hc' : pCore 2 (B.map e.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := db.toMonoidHom) _ db.injective).mp
    rw [pCore_map_iso 2 db]
    exact hz
  exact not_strict_three_pair_native (hsq.knownSimple_of_equiv e) (S.mapSurjective e.surjective)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker ha e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hb e.toMonoidHom)
    (lt_of_le_of_ne (map_mono hlt.le) (fun h => hlt.ne ((map_injective e.injective) h)))
    ((map_mono (f := e.toMonoidHom) hna).trans (A.le_normalizer_map e.toMonoidHom))
    ((map_mono (f := e.toMonoidHom) hnb).trans (B.le_normalizer_map e.toMonoidHom))
    (ha3.of_mulEquiv a.symm) (hquasi.of_mulEquiv b) hc'
    (fun hm => hno4 (hm.of_mulEquiv b)) (fun hm => hnoM ⟨b.trans hm.some⟩)
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
