module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import Theory.GroupTheory.PCoreFrattiniQuotient
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The D.2.13 prime restriction for a genuine prime-by-two action group

In a faithful binary action with cubic ratio at most two, choose an
actual Qhat-star actor. If O₂(G)=1 and G/O_p(G) is a two-group, the odd
core is self-centralizing. Every nontrivial elementary two-actor must
therefore move it. The original D.2.13(1) then gives p=3 or p=5.

Source: Aschbacher--Smith D.2.13(1), pp.184--185, in 3.2.14, p.585.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The original D.2.13 actor moves the actual odd core of a prime-by-two
action group; neither core movement nor a chosen actor is an input. -/
theorem prime_restriction_of_prime_by_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hcore : pCore 2 G = ⊥) (hq : IsPGroup 2 (G ⧸ pCore p G))
    (hratio : cubicRatio ρ ≤ 2) : p = 3 ∨ p = 5 := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hratio
  have hc := centralizer_pCore_le_of_quotient_isPGroup p 2 hcore hq
  have hm : ⁅pCore p G,A⁆ ≠ ⊥ := by
    intro he
    have hle : A ≤ pCore p G :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans hc
    have hdis : Disjoint A (pCore p G) :=
      IsPGroup.disjoint_of_ne 2 p (by intro he; rw [← he] at ho; norm_num at ho)
        _ _ (by let := hA.1.2.1.2; exact IsElementaryAbelian.isPGroup 2 A) pCore_isPGroup
    exact hA.1.2.1.1 (bot_unique ((le_inf le_rfl hle).trans hdis.le_bot))
  exact (source_lemma_D_2_13_one_two ρ hf hA ho hm).1


/-- The original reduced module and prime-by-two extension supply the
literal conjugation quotient used by D.2.13. The odd image and its
self-centralizer are constructed from the actual quotient map. -/
theorem prime_restriction_of_reduced_extension
    (I T : Subgroup G) [I.Normal] (hgen : I ⊔ T = ⊤)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hI : IsPGroup p (I ⧸ pCore 2 I)) (hT : IsPGroup 2 T)
    (W : Subgroup G) (hW : IsPReduced 2 W)
    (hratio : letI := hW.normal
      letI := hW.elementary
      cubicRatio (Representation.NormalElementaryQuotient.representation W
        (QuotientGroup.mk' (centralizer (W : Set G))) (QuotientGroup.mk'_surjective _)
          (QuotientGroup.ker_mk' _)) ≤ 2) : p = 3 ∨ p = 5 := by
  let := hW.normal
  let := hW.elementary
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let f := q.comp I.subtype
  have hk : pCore 2 I ≤ f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ((normal_pCore_le_centralizer_reducedPSubgroup 2 I).trans
      (centralizer_le hW.le_reducedPSubgroup)) (mem_map_of_mem I.subtype hx)
  let fq := QuotientGroup.lift (pCore 2 I) f.rangeRestrict hk
  have hfs : Function.Surjective fq := by
    intro y
    obtain ⟨x,hx⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk x,hx⟩
  have hP : IsPGroup p (I.map q) := by
    have he : f.range = I.map q := by rw [MonoidHom.range_comp,range_subtype]
    rw [← he]
    exact hI.of_surjective fq hfs
  have hIP : I.map q ≤ pCore p (G ⧸ C) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective _),hP⟩
  have hs : I.map q ⊔ T.map q = ⊤ := by
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 ((G ⧸ C) ⧸ pCore p (G ⧸ C)) :=
    isPGroup_quotient_of_sup_eq_top _ (T.map q) (hT.map q)
      (top_unique (hs ▸ sup_le_sup_right hIP (T.map q)))
  let ρ := Representation.NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  exact prime_restriction_of_prime_by_two ρ
    (Representation.NormalElementaryQuotient.representation_injective _ _ _ _)
    ho hW.quotient_pCore_eq_bot hquot hratio

end CFSG.Quasithin.ChapterD
