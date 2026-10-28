module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Containing
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.CoverModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.Quasithin.Rank

/-!
# Containing models for a normalized local A₈ section

First remove the ambient two-core. The containing C-component is then
quasisimple, and the original A₈ section excludes every three-cover row.
Restriction to its intrinsic Sylow reduces the remaining rows to the simple
carrier classification supplied by the caller. The resulting model is
transported through the actual C-component two-core quotient equivalence.

Equality of the quotient images lifts because the ambient two-core normalizes
the smaller subgroup: a perfect subgroup cannot enlarge it by a two-group
supplement. No quasisimplicity of the original smaller subgroup is assumed.

Source: Aschbacher–Smith A.3.6 and A.3.12, printed pp.43–48, as used in
15.3.32(3), printed p.1133. The simple-model dispatcher remains explicit.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
open Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- With trivial ambient two-core, the simple-carrier classification applies to the
actual containing component after excluding the central three-covers. -/
theorem containing_models_of_core_eq_bot
    (hclass : ∀ {H : Type u} [Group H] [Finite H] [IsSimpleGroup H],
      (S : Sylow 2 H) → (B : Subgroup H) → B ∈ localCComponents S →
      (S : Subgroup H) ≤ normalizer (B : Set H) →
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 → TheoremCModel H →
      B = ⊤ ∨ ClassicalGroup.IsPSL H 5 2 ∨
        Nonempty (H ≃* Sporadic.Mathieu.M24) ∨ Nonempty (H ≃* Janko4.Model))
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) :
    B = K ∨ ClassicalGroup.IsPSL K 5 2 ∨
      Nonempty (K ≃* Sporadic.Mathieu.M24) ∨ Nonempty (K ≃* Janko4.Model) := by
  let : IsQuasisimple K := containing_quasisimple hG hO T hB hK hBK hsection
  obtain ⟨S, _, hl, hn⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  have ha : ClassicalGroup.IsPSL ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) 4 2 :=
    hsection.of_mulEquiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK)))
  rcases quasisimple_containing_component_models_knownSimple hG hO hK with
    ⟨hs, hm⟩ | ⟨_, hm⟩
  · let : IsSimpleGroup K := hs
    rcases hclass S (B.subgroupOf K) hl hn ha hm with he | hm
    · exact Or.inl (le_antisymm hBK (subgroupOf_eq_top.mp he))
    · exact Or.inr hm
  · exact (not_threeCover S hl hn ha hm).elim

/-- The restricted A.3.12 alternatives in the original ambient group, retaining
the literal intrinsic two-core quotient of its containing C-component. -/
theorem containing_models
    (hclass : ∀ {H : Type u} [Group H] [Finite H] [IsSimpleGroup H],
      (S : Sylow 2 H) → (B : Subgroup H) → B ∈ localCComponents S →
      (S : Subgroup H) ≤ normalizer (B : Set H) →
      ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 → TheoremCModel H →
      B = ⊤ ∨ ClassicalGroup.IsPSL H 5 2 ∨
        Nonempty (H ≃* Sporadic.Mathieu.M24) ∨ Nonempty (H ≃* Janko4.Model))
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) :
    B = K ∨ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  let N := pCore 2 G
  let q := QuotientGroup.mk' N
  let : Group.IsNilpotent N := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ N) := by
    refine ⟨?_, hG.isKGroup.quotient N⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho N pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective N)
  obtain ⟨hl, hn, ha⟩ := local_section_map hB hTB hsection q
  have hl' : B.map q ∈ localCComponents S := hl
  have hn' : (S : Subgroup (G ⧸ N)) ≤ normalizer (B.map q : Set _) := hn
  have hmodels := containing_models_of_core_eq_bot hclass hQ
    (pCore_quotient_pCore_eq_bot 2) S hl' (hK.map_quotient N) (map_mono hBK) hn' ha
  let e : (K ⧸ pCore 2 K) ≃* K.map q := cComponentTwoCoreQuotientEquiv hK
  rcases hmodels with he | hm
  · left
    let : Group.IsPerfect K := hK.perfect
    have hp : IsPPerfect 2 K := by
      intro R hR hquot
      let := hR
      have hs : Subsingleton (K ⧸ R) := by
        by_contra! hn
        exact Group.IsPerfect.not_isNilpotent (K ⧸ R) hquot.isNilpotent
      apply eq_top_iff.mpr
      intro k _
      exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
    apply le_antisymm hBK
    apply le_of_isPPerfect_of_le_sup_of_normalizes K B N hp
      pCore_isPGroup ((pCore_isPGroup.le_sylow_of_normal T).trans hTB)
    have hsup : B ⊔ N = K ⊔ N := by
      simpa only [q, comap_map_eq, QuotientGroup.ker_mk'] using congrArg (comap q) he
    rw [hsup]
    exact le_sup_left
  · rcases hm with hlin | hm
    · exact Or.inr (Or.inl (hlin.of_mulEquiv e))
    · rcases hm with hm | hj
      · exact Or.inr (Or.inr (Or.inl ⟨e.trans hm.some⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨e.trans hj.some⟩))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
