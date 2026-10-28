module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpRank
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import Theory.GroupTheory.PerfectCentralCoverPrimeRank
public import Theory.GroupTheory.Commutator.PerfectCoreKernel

/-!
# The original nonbinary quotient survives in the actual component action

Normality of the covering residual in M identifies its conjugate span with
itself. The nontrivial action on the escaping component has proper kernel.
Quasisimplicity puts that kernel in the preimage of the full quotient center,
so the original simple central quotient is a quotient of the action image.

Transfer for perfect central covers preserves odd rank at least two, including
the cubic scalar center of SL₃. Thus the actual action has odd rank at least two
and order at least 20160. These bounds are consumed by ConstrainedModels;
the odd-normalizer task retains the remaining pushing-up exclusions.

Source: Aschbacher--Smith C.4.3--8, printed pp.152--154, applied to
the nonbinary covering residual in 4.4.6, printed p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem nontrivial_image_central_quotient {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]
    (f : X →* Y) (hne : f ≠ 1) :
    ∃ g : f.range →* (X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X),
      Function.Surjective g := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hproper : f.ker ≠ ⊤ := fun ht => hne (MonoidHom.ker_eq_top_iff.mp ht)
  have hc : f.ker.map q ≤ center (X ⧸ pCore 2 X) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (f.ker.map q) with hc | ht
    · exact hc
    · have hsup : f.ker ⊔ pCore 2 X = ⊤ := by
        have hm := congrArg (Subgroup.comap q) ht
        simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
      have hp := isPGroup_quotient_of_sup_eq_top f.ker (pCore 2 X) pCore_isPGroup hsup
      let : Group.IsNilpotent (X ⧸ f.ker) := hp.isNilpotent
      exact (hproper (top_unique (by simpa only [solvableResidual_eq_top] using
        solvableResidual_le_of_solvable_quotient f.ker))).elim
  let c := (QuotientGroup.mk' (center (X ⧸ pCore 2 X))).comp q
  have hk : f.ker ≤ c.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (q x)).mpr (hc (mem_map_of_mem q hx))
  let g := QuotientGroup.lift f.ker c hk
  have hcSur : Function.Surjective c :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective f.ker c hcSur hk
  let e := QuotientGroup.quotientKerEquivRange f
  exact ⟨g.comp e.symm.toMonoidHom,hg.comp e.symm.surjective⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

include D S
/-- Every escaping component action retains the original simple central quotient. -/
theorem constrained_natural_action_quotient {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ g : coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H) →*
        coreCentralQuotient L, Function.Surjective g := by
  let := hN
  have hn : M ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hN
  have hs : conjugateSpanBy B M = B :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  let X := (conjugateSpanBy B M).subgroupOf H
  have hXH : conjugateSpanBy B M ≤ H :=
    (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let ex := subgroupOfEquivOfLe hXH
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := ex.symm.toMonoidHom) ex.symm.surjective
  let ec : (X ⧸ pCore 2 X) ≃* (L ⧸ pCore 2 L) :=
    (QuotientGroup.congr _ _ ex (pCore_map_iso 2 ex)).trans
      ((QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hs)
        (pCore_map_iso 2 (MulEquiv.subgroupCongr hs))).trans e)
  let := S.source.toHypothesis1221.quasisimple
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv ec.symm
  have hnorm := h.constrained_span_normalizes_intrinsic K hK hq
  let j := inclusion hnorm
  let f := (normalizerCoreCentralAction K).comp j
  have he : f.range = coreCentralActorImage K X := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem _ (show j x ∈ X.subgroupOf _ from x.property)
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨(x : H),hx⟩,rfl⟩
  have hne : f ≠ 1 := by
    intro hf
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [←he,hf,MonoidHom.range_one]
  obtain ⟨g,hg⟩ := nontrivial_image_central_quotient f hne
  let es := QuotientGroup.congr _ _ ec (FixedElementary.map_center ec)
  let er := MulEquiv.subgroupCongr he
  exact ⟨es.toMonoidHom.comp (g.comp er.symm.toMonoidHom),
    es.surjective.comp (hg.comp er.symm.surjective)⟩

/-- Some odd prime has rank at least two in the literal component action. -/
theorem constrained_natural_action_rank {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      2 ≤ primeRank p (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) := by
  obtain ⟨g,hg⟩ := constrained_natural_action_quotient D S h hN e K hK hq hout
  obtain ⟨p,hp,ho,hr⟩ := exists_odd_rank_two D S
  let : Fact p.Prime := ⟨hp⟩
  let := S.source.toHypothesis1221.quasisimple
  have hl := PerfectCentralCovering.two_le_primeRank_central_quotient ho hr
  change 2 ≤ primeRank p (coreCentralQuotient L) at hl
  refine ⟨p,hp,ho,?_⟩
  by_contra! hrank
  let P : Sylow p (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) :=
    Classical.choice inferInstance
  have hu := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one ho (by omega)) g hg
  omega

/-- The action has order at least the least nonbinary simple central quotient. -/
theorem constrained_natural_action_card {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    20160 ≤ Nat.card (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) := by
  obtain ⟨g,hg⟩ := constrained_natural_action_quotient D S h hN e K hK hq hout
  have hl := quotient_card_ge D S
  have hz := Nat.le_of_dvd (by decide : 0 < 3) (quotient_center_card_dvd_three D S)
  have hc := card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))
  have hb : 20160 ≤ Nat.card (coreCentralQuotient L) := by
    change 20160 ≤ Nat.card ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L))
    nlinarith
  exact hb.trans (Nat.card_le_card_of_surjective g hg)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
