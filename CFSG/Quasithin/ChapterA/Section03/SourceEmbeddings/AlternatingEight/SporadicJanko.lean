module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.SporadicLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenFaithfulSylow
public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.EvenCharacteristic
public import Theory.SpecificGroups.SymmetricEight.SylowNormalElementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
/-!
# Excluding the Hall–Janko containing row

A nontrivial two-core is excluded by the checked local normalizer orders.
If the core is trivial, B is A₈ and even characteristic makes the original
Sylow act faithfully through Aut(A₈)=S₈. Both Sylow groups have order 128,
so the resulting image is a full S₈ Sylow. Its normal elementary subgroup
of order greater than four contradicts the actual J₂ Sylow calculation.

Source: Aschbacher–Smith A.3.12, pp.47–48, used in 15.3.32(3), p.1133;
GLS3 Table 5.3g. No quasisimplicity of the original B is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]
private theorem not_janko_two_faithful (S : Sylow 2 G) (B : Subgroup G)
    (eB : B ≃* alternatingGroup (Fin 8))
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (S : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (e : G ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property, ?_⟩
    change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let eA : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  let j := eA.symm.toMonoidHom.comp ((MulAut.congr eB).toMonoidHom.comp f)
  have hj : Function.Injective j := eA.symm.injective.comp ((MulAut.congr eB).injective.comp hf)
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let eST : S ≃* T := e.subgroupMap (S : Subgroup G)
  have hS : Nat.card S = 128 := by
    rw [Nat.card_congr eST.toEquiv,
      Nat.card_congr (T.equiv (Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.sylow
        Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁)).toEquiv]
    exact Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_s
  have hr : Nat.card j.range = 128 := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hS
  let P : Sylow 2 (Equiv.Perm (Fin 8)) := Sylow.ofCard j.range (by
    rw [hr,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide +kernel)
  let a : P ≃* T := (MonoidHom.ofInjective hj).symm.trans eST
  obtain ⟨E,hEn,hEe,hEcard⟩ := Theory.SpecificGroups.SymmetricEight.exists_large_normal_elementary P
  let : IsElementaryAbelian 2 E := hEe
  have hDnormal := hEn.map a.toMonoidHom a.surjective
  have hDelem : IsElementaryAbelian 2 (E.map a.toMonoidHom) := IsElementaryAbelian.map _
  have hbound := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four T
    (E.map a.toMonoidHom) hDnormal hDelem
  rw [card_map_of_injective a.injective] at hbound
  omega

/-- The full original local A₈ section excludes J₂, including a trivial two-core. -/
theorem not_janko_two (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (e : G ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  by_cases hc : pCore 2 B = ⊥
  · obtain ⟨a⟩ := quotient_equiv h
    let eB : B ≃* alternatingGroup (Fin 8) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans a
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup B := eB.isSimpleGroup
    let := local_perfect hB
    have hz : center B = ⊥ :=
      (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
    let : IsQuasisimple B :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    have hE := MainConverse.SporadicLocal.J2Even.evenCharacteristic_of_equiv e
    exact not_janko_two_faithful S B eB hn
      (sylow_centralizer_eq_bot_of_evenCharacteristic S (hE S) hB hn) e
  · exact not_janko_two_of_core_ne_bot S B hn h hc e
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
