module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeHeldSix
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeSixCover
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import Theory.Alternating.theorem_5_2_1_2

/-!
# Excluding Held as the original alternating-six container

If the original local section has nontrivial two-core, the literal Held
maximal two-local calculation excludes its A₆ quotient. With trivial
two-core, even characteristic makes the original Sylow act faithfully on
A₆. Its order would divide 1440, whereas Held has two-part at least 1024.

Restriction to a containing C-component and its literal two-core quotient
preserves the same local section, Sylow intersection and normalizer.
`M22CodeHeldExcluded` applies this to the original involution residual.
Source: Aschbacher--Smith A.3.12 and 8.2.2(1), printed pp.47--48,715,
refs/quasithin.pdf; GLS3 Table 5.3p for the native Held locals.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows

private theorem six_automorphism_card :
    Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 := by
  rw [← GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup.card_mul_index,
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index,
    ← Nat.card_congr GLS3.Chapter5.permSixMulEquivNaturalAlternatingAutomorphisms.toEquiv]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

theorem not_held_six_section {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (eG : G ≃* Held.He) : False := by
  have hperf : Group.IsPerfect B := by
    let := hl.perfect
    let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let := hperf
  by_cases hc : pCore 2 B = ⊥
  · let b : B ≃* alternatingGroup (Fin 6) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans eB
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup B := b.isSimpleGroup
    have hz : center B = ⊥ := by
      apply (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      intro he
      exact Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp he)
    let : IsQuasisimple B :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    have hf := ChapterA.Section03.SourceEmbeddings.sylow_centralizer_eq_bot_of_evenCharacteristic
      S (MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv eG S) hl hn
    let f := B.normalizerMonoidHom.comp (inclusion hn)
    have hinj : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply eq_bot_iff.mpr
      intro a ha
      apply Subtype.ext
      apply mem_bot.mp
      rw [←hf]
      refine ⟨a.property,?_⟩
      change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
      rw [normalizerMonoidHom_ker] at ha
      exact ha
    have hd : Nat.card S ∣ 1440 := by
      have hh := card_dvd_of_injective f hinj
      rwa [Nat.card_congr (MulAut.congr b).toEquiv,six_automorphism_card] at hh
    have h1024 : 2^10 ∣ Nat.card G := by
      rw [Nat.card_congr eG.toEquiv]
      exact Held.two_pow_ten_dvd_card
    have hh := (S.pow_dvd_card_of_pow_dvd_card h1024).trans hd
    norm_num at hh
  · let A := B.map eG.toMonoidHom
    let a : B ≃* A := eG.subgroupMap B
    let : Group.IsPerfect A := Group.IsPerfect.map eG.toMonoidHom
    have hcA : pCore 2 A ≠ ⊥ := by
      intro hz
      apply hc
      apply (map_eq_bot_iff_of_injective (f := a.toMonoidHom) _ a.injective).mp
      rw [pCore_map_iso,hz]
    exact MathieuCode.NormalizedShadowRows.HeldSix.held_not_six_section_of_core_ne_bot
      (S.mapSurjective (f := eG.toMonoidHom) eG.surjective) A
      ((map_mono hn).trans (B.le_normalizer_map eG.toMonoidHom)) hcA
      ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eB)

/-- Restrict the original local section to its containing component and use
the full original two-core quotient map. -/
theorem not_held_containing_six {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (eK : (K ⧸ pCore 2 K) ≃* Held.He) : False := by
  obtain ⟨T,_,hl,hnA⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_normalizing
    S hB hK.subnormal hBK hn
  let A := B.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let a : A ≃* B := subgroupOfEquivOfLe hBK
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := (q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := K)
    infer_instance
  exact not_held_six_section (T.mapSurjective (QuotientGroup.mk'_surjective _)) (A.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono hnA).trans (A.le_normalizer_map q)) (b.symm.trans (aq.trans eB)) eK

end CFSG.Quasithin.Chapter8.MathieuShadowRows
