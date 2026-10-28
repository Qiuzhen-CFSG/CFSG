module
public import Theory.SpecificGroups.BinaryLinear.RadicalFlagClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Held
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction

/-!
# Closing both invariant binary-linear normalizer enlargements

On the actual quotient K/O₂(K), the original Sylow and odd complement form
an irreducible pair. The intrinsic inner-pair calculations force an outer
pair actor. Transport through the actual PSL₄(2) or PSL₅(2) model identifies
the pair's Sylow overgroup with a symmetric partial flag. The proved radical
interval theorem then shows that every quotient actor normalizing the image
of R=T₁∩K preserves the embedded two-residual.

The source parabolic-core bound supplies the required radical interval.
The residual identity and kernel normalization lift the result to the
original O²(H). Thus both invariant binary-linear rows are fully excluded;
the strict normalizer enlargement now has only the two rank-one model rows.
No flag placement, weak-closure, outer-action or recognition callback remains
in either binary-linear theorem.

Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748. The intrinsic
Chapter 15 imports prove only earlier local pair mathematics and contain
no Chapter 10 normalizer premise. Final rank-one assembly stays with
qt-d-10-nona5-half-sylow-unique.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding InvariantThree
open Chapter15.Section04.LocalSetup.EmbeddingReduction

private theorem exists_outer_pair {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (P : Subgroup Q)
    (hirr : ¬ PairReducible (S : Subgroup Q) P)
    (hinv : Terminal.LinearFourActions.InnerPairInvariant (S : Subgroup Q) P) :
    ∃ a : MulAut Q, (S : Subgroup Q).map a.toMonoidHom = S ∧
      P.map a.toMonoidHom = P ∧ a ∉ MulAut.innerSubgroup Q := by
  classical
  by_contra hn
  push Not at hn
  apply hirr
  intro E hE _
  obtain ⟨A,hAb,hAt,hA⟩ := hinv
  refine ⟨A,hAb,hAt,?_⟩
  intro c hc
  obtain ⟨a,haS,haP⟩ := hE hc
  have hSmap : (S : Subgroup Q).map a.toMonoidHom = S := by
    change a ∈ MulAction.stabilizer (MulAut Q) (S : Subgroup Q)
    exact (mem_automorphism_stabilizer_iff _ _).mpr haS
  have hPmap : P.map a.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      exact haP ⟨x,hx⟩ ▸ (c ⟨x,hx⟩).property
    · exact (Nat.card_congr (a.subgroupMap P).toEquiv).le
  obtain ⟨q,hq⟩ := hn a hSmap hPmap
  exact hA c ⟨q,by simpa only [hq] using haS,by simpa only [hq] using haP⟩

private theorem binary_pair_outer {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {P : Subgroup Q} (h : PairInput S P)
    (hirr : ¬ PairReducible (S : Subgroup Q) P)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2) :
    ∃ a : MulAut Q, (S : Subgroup Q).map a.toMonoidHom = S ∧
      P.map a.toMonoidHom = P ∧ a ∉ MulAut.innerSubgroup Q := by
  apply exists_outer_pair S P hirr
  rcases hn with rfl | rfl
  · exact Terminal.LinearFourActions.InnerPairCalculation.linearFourInnerPairTheorem
      Q hm S P h.oddComplement h.permutes
  · exact BinaryAction.FiveOuter.five_innerPairInvariant hm S P h.oddComplement h.permutes

private theorem binary_preserves_residual {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {P X U : Subgroup Q} (h : PairInput S P)
    (hirr : ¬ PairReducible (S : Subgroup Q) P)
    {m : ℕ} (hm₀ : 3 ≤ m) (hm₁ : m ≤ 4)
    (hm : ClassicalGroup.IsPSL Q (m+1) 2)
    (hres : (pResidual 2 (P ⊔ (S : Subgroup Q) : Subgroup Q)).map
      (P ⊔ (S : Subgroup Q)).subtype = X)
    (hcore : (P ⊔ (S : Subgroup Q)).pCoreIn 2 ≤ U) (hUS : U ≤ (S : Subgroup Q))
    (a : MulAut Q) (ha : U.map a.toMonoidHom = U) : X.map a.toMonoidHom = X := by
  obtain ⟨e⟩ := BinaryAction.binary_linear_equiv (by omega : 0 < m+1) hm
  obtain ⟨o,hoS,hoP,hout⟩ := binary_pair_outer h hirr (by omega : m+1 = 4 ∨ m+1 = 5) hm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let B := P ⊔ (S : Subgroup Q)
  let B' := B.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  have he (c : MulAut Q) : (MulAut.congr e c).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp c.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change e (c (e.symm (e x))) = e (c x)
    rw [e.symm_apply_apply]
  have hmap (A : Subgroup Q) (c : MulAut Q) (hc : A.map c.toMonoidHom = A) :
      (A.map e.toMonoidHom).map (MulAut.congr e c).toMonoidHom = A.map e.toMonoidHom := by
    rw [Subgroup.map_map,he,← Subgroup.map_map,hc]
  have hoB : B.map o.toMonoidHom = B := by rw [Subgroup.map_sup,hoS,hoP]
  have hout' : MulAut.congr e o ∉ MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup (m+1)) := by
    rw [← MulAut.map_innerSubgroup_congr e,Subgroup.mem_map_equiv,MulEquiv.symm_apply_apply]
    exact hout
  have hc : B'.pCoreIn 2 ≤ U' := by
    rw [← map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective]
    exact map_mono hcore
  have hx := BinaryLinear.InvariantNodeActions.map_residual_of_outer_invariant_sylow_overgroup
    (by omega : 2 ≤ m) hm₁ S' B' U' (map_mono (show (S : Subgroup Q) ≤ B from le_sup_right))
    hc (map_mono hUS) (MulAut.congr e o) hout' (hmap _ _ hoS) (hmap _ _ hoB)
    (MulAut.congr e a) (hmap _ _ ha)
  have hres' : (pResidual 2 B').map B'.subtype = X.map e.toMonoidHom := by
    rw [← map_embedded_pResidual]
    exact congrArg (Subgroup.map e.toMonoidHom) hres
  rw [hres',Subgroup.map_map,he,← Subgroup.map_map] at hx
  exact Subgroup.map_injective e.injective hx

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- The actual binary rank-four/five enlargement preserves O²(H). Its full
Sylow, irreducibility, outer actor, symmetric flag, radical bound and quotient
action are all constructed from the original parabolic input. -/
theorem Data.normalizes_residual_of_binary_linear (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hq : IsQuasisimple (XiQuotient (enlargedResidual T L H)))
    {n : ℕ} (hnmodel : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (XiQuotient (enlargedResidual T L H)) n 2) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  by_contra hN
  obtain ⟨S,P,hS,hpair,hirr,hres⟩ := h.exists_quotient_pair hn hq hN
  let X := quotientImage (enlargedResidual T L H) (residual H)
  let U := quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)
  have hUS : U ≤ (S : Subgroup (XiQuotient (enlargedResidual T L H))) := by
    rw [hS]
    exact map_mono (subgroupOf_mono _ (inf_le_left.trans inf_le_left))
  have hsup : X ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H))) = P ⊔ S := by
    have he := embedded_pResidual_sup_of_common_sylow
      (P ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))) (S : Subgroup _) (S.subtype le_sup_right)
      (by simpa only [Sylow.coe_subtype] using
        map_subgroupOf_eq_of_le (show (S : Subgroup _) ≤ P ⊔ S from le_sup_right))
    rwa [hres] at he
  have hcore : (P ⊔ (S : Subgroup (XiQuotient (enlargedResidual T L H)))).pCoreIn 2 ≤ U := by
    rw [← hsup,hS]
    exact h.quotient_parabolic_core_le_intersection
  apply hN
  apply h.normalizes_residual_of_quotientAction
  intro g
  rcases hnmodel with rfl | rfl
  · exact binary_preserves_residual hpair hirr (m := 3) (by decide) (by decide) hm hres hcore hUS
      (quotientAction T L H g) (h.quotientAction_preserves_intersection g)
  · exact binary_preserves_residual hpair hirr (m := 4) (by decide) (by decide) hm hres hcore hUS
      (quotientAction T L H g) (h.quotientAction_preserves_intersection g)

/-- The two invariant binary models are excluded from the actual strict
normalizer enlargement. Only the even rank-one and odd prime rank-one rows remain. -/
theorem Data.strict_rank_one_models (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) :
    residual H < enlargedResidual T L H ∧ ∃ I : Subgroup G,
      I ∈ cComponentsIn (enlargement T L H) ∧ IsQuasisimple (XiQuotient I) ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      ((∃ n : ℕ, 2 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 (2 ^ n)) ∨
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p)) := by
  obtain ⟨hlt,I,hI,hq,hK,hm⟩ := h.strict_classical_models hn hN
  refine ⟨hlt,I,hI,hq,hK,?_⟩
  rcases hm with hm | hm | ⟨hi,k,hk,hm,_⟩
  · exact Or.inl hm
  · exact Or.inr hm
  · have horbit : componentOrbit I (T : Subgroup G) = I :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer I T I le_rfl hi)
        (le_componentOrbit I T)
    have hKI := hK.trans horbit
    have hqK : IsQuasisimple (XiQuotient (enlargedResidual T L H)) := hKI.symm ▸ hq
    have hmK : ClassicalGroup.IsPSL (XiQuotient (enlargedResidual T L H)) k 2 := hKI.symm ▸ hm
    exact (hN (h.normalizes_residual_of_binary_linear hn hqK hk hmK)).elim

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
