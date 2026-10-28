module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.MaximalNormalizer
public import Theory.GroupTheory.OddCoreElementaryContainment

/-!
# Excluding the cyclic maximal-W alternative

The full normalizer has trivial odd core. In the normal closure of the
original elementary group U, the normal subgroup W is central, so the
normal closure of U/W also has trivial odd core. The cyclic alternative
of I.8.5 would make U/W equal its normal closure, contradicting the proper
normalizer. The remaining Bender alternative has trivial center, by the
odd-core clause of I.8.5, with the actual Borel and Sylow markings retained.

Source: Aschbacher–Smith F.4.42, printed p.296, and I.8.5, printed p.430.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.UnitarySource
variable {G : Type*} [Group G] [Finite G]

/-- The actual maximal-W quotient has a centerless Bender normal closure;
the order-two/odd-core alternative of I.8.5 is impossible. -/
theorem quotient_bender_of_odd_core
    (U W : Subgroup G) [IsElementaryAbelian 2 U] [W.Normal]
    (hWU : W ≤ U) (hodd : pPrimeCore 2 G = ⊥)
    (Y : Subgroup (G ⧸ W))
    (hVY : U.map (QuotientGroup.mk' W) ≤ Y)
    (hVne : U.map (QuotientGroup.mk' W) ≠ ⊥) (hY : Y ≠ ⊤)
    (hNY : normalizer (U.map (QuotientGroup.mk' W) : Set (G ⧸ W)) = Y)
    (hfix : ∀ v ∈ U.map (QuotientGroup.mk' W), v ≠ 1 → ∃! q : (G ⧸ W) ⧸ Y, v • q = q) :
    let V := U.map (QuotientGroup.mk' W)
    let K := normalClosure (V : Set (G ⧸ W))
    pPrimeCore 2 K = ⊥ ∧ center K = ⊥ ∧ IsQuasisimple K ∧
      BenderSuzuki.IsSimpleBenderGroup (K ⧸ center K) ∧
      Y.comap K.subtype = normalizer (V.subgroupOf K : Set K) ∧
      BenderSuzuki.IsBorelSubgroup (Y.comap K.subtype) ∧
      ∃ S : Sylow 2 K, (S : Subgroup K) ≤ Y.comap K.subtype ∧
        V.subgroupOf K = (omega₁ S (p := 2)).map (S : Subgroup K).subtype := by
  let V := U.map (QuotientGroup.mk' W)
  let K := normalClosure (V : Set (G ⧸ W))
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : (V.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hNY.ge
  have hOK : pPrimeCore 2 K = ⊥ := oddCore_normalClosure_quotient_eq_bot U W hWU hodd
  have hnot : ¬ (Nat.card V = 2 ∧ pPrimeCore 2 K ⊔ V.subgroupOf K = ⊤) := by
    intro hh
    have he : V.subgroupOf K = ⊤ := by simpa only [hOK,bot_sup_eq] using hh.2
    have hVK : V = K := by
      have hm := congrArg (map K.subtype) he
      rw [map_subgroupOf_eq_of_le (show V ≤ K from le_normalClosure),
        ←MonoidHom.range_eq_map,range_subtype] at hm
      exact hm
    apply hY
    rw [←hNY,show U.map (QuotientGroup.mk' W) = K from hVK]
    exact normalizer_eq_top K
  have hstructure := (ChapterI.Section06To08.lemma_I_8_5 V Y hVY hVne hY hfix).1
  have hb := hstructure.resolve_left hnot
  have ho := ChapterI.Section06To08.lemma_I_8_5_oddCore_recognition V Y hVY hVne hY hfix
  have hZ : center K = ⊥ := (ho.resolve_left hnot).2.2.1.symm.trans hOK
  exact ⟨hOK,hZ,hb⟩

end CFSG.Quasithin.ChapterF.UnitarySource
