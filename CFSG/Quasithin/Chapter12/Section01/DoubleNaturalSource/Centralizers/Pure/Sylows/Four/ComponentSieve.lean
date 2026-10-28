module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Quotient
public import Theory.SpecificGroups.BinaryLinear.RadicalFlagClosure
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction
public import Theory.GroupTheory.PCoreNormalizerAction.Residual
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.NormalizerCore
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Normalizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairSource
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection

/-!
# Component exclusions for the original pure-point Sylow obstruction

Let T1 be the marked pure-point centralizer in T and suppose it is not
Sylow in its ambient centralizer. The original escaping Sylow P, residual
X and overgroup H = <P,XT> then supply a faithful component K.

If T normalizes K, the literal quotient two-core bound and the binary
parabolic normalizer calculation force H to normalize X, contradicting
its strict normal closure. The actual wreath automizer excludes the other
original invariant rows. The corrected Held row is separately eliminated
by its interval-normalizer theorem, using the proved index-two bound.
Thus T must interchange two rank-one components. For a non-A5 quotient,
the moved-component maximality theorem constructs the genuine Fundamental
Setup for K. The A5 branch remains explicit.

The binary automorphism argument adapts the intrinsic proofs in Chapter10/
SourceLinearThreeReduction/PointControl/HalfUniqueness/NormalizerSource/
BinaryThreeAction/Linear.lean to the exact Xi complement hypotheses here.
All quotient maps and core bounds refer to the original source subgroups.

The fixed-subgroup nontriviality premise remains for the actual ambient MS
specialization. Its discharge, the swapped-component contradiction and
final fusion/abelian-closure assembly remain with
`qt-d-double-natural-pure-fusion`; `qt-rank-two-ms93` owns the shared MS
input and `qt-d-double-natural-centralizers` supplies the earlier inputs.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791, using the corrected
1.3.4 alternatives and moved-component maximality 1.2.8(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding InvariantThree
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
    {S : Sylow 2 Q} {P : Subgroup Q} (hodd : XiOddQuotient 3 P)
    (hperm : (P : Set Q) * (S : Set Q) = (S : Set Q) * (P : Set Q))
    (hirr : ¬ PairReducible (S : Subgroup Q) P)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL Q n 2) :
    ∃ a : MulAut Q, (S : Subgroup Q).map a.toMonoidHom = S ∧
      P.map a.toMonoidHom = P ∧ a ∉ MulAut.innerSubgroup Q := by
  apply exists_outer_pair S P hirr
  rcases hn with rfl | rfl
  · exact Terminal.LinearFourActions.InnerPairCalculation.linearFourInnerPairTheorem
      Q hm S P hodd hperm
  · exact BinaryAction.FiveOuter.five_innerPairInvariant hm S P hodd hperm

private theorem binary_preserves_residual {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {P X U : Subgroup Q} (hodd : XiOddQuotient 3 P)
    (hperm : (P : Set Q) * (S : Set Q) = (S : Set Q) * (P : Set Q))
    (hirr : ¬ PairReducible (S : Subgroup Q) P)
    {m : ℕ} (hm₀ : 3 ≤ m) (hm₁ : m ≤ 4)
    (hm : ClassicalGroup.IsPSL Q (m+1) 2)
    (hres : (pResidual 2 (P ⊔ (S : Subgroup Q) : Subgroup Q)).map
      (P ⊔ (S : Subgroup Q)).subtype = X)
    (hcore : (P ⊔ (S : Subgroup Q)).pCoreIn 2 ≤ U) (hUS : U ≤ (S : Subgroup Q))
    (a : MulAut Q) (ha : U.map a.toMonoidHom = U) : X.map a.toMonoidHom = X := by
  obtain ⟨e⟩ := BinaryAction.binary_linear_equiv (by omega : 0 < m+1) hm
  obtain ⟨o,hoS,hoP,hout⟩ := binary_pair_outer hodd hperm hirr (by omega : m+1 = 4 ∨ m+1 = 5) hm
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


variable {G : Type*} [Group G] [Finite G]

/-- The literal core interval forces residual normalization in either
invariant binary linear quotient. Used also when retaining full detection data. -/
theorem normalizes_of_binary_quotient (T : Sylow 2 G)
    {X A H K U : Subgroup G} (hi : LocalInput 3 (T : Subgroup G) X A H)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hXK : X ≤ K)
    (hUT : U ≤ (T : Subgroup G)) (hcore : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ U)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (XiQuotient K) n 2) :
    H ⊓ normalizer (U : Set G) ≤ normalizer (X : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hi.overgroup
  have hHKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  have hTK := hTH.trans hHKn
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨S,hS⟩ := component_quotient_sylow hSyl hKH hKn
  have hAK : A ≤ K := (le_sup_right.trans hi.complement.le).trans hXK
  have hodd : XiOddQuotient 3 (quotientImage K A) :=
    hi.odd_complement.of_mulEquiv (complementEquiv hi hAK)
  have hperm : (quotientImage K A : Set (XiQuotient K)) * (S : Set (XiQuotient K)) =
      (S : Set (XiQuotient K)) * (quotientImage K A : Set (XiQuotient K)) := by
    simpa only [←hS,Sylow.coe_coe] using component_quotient_permute hi hAK
  have hirr : ¬ PairReducible (S : Subgroup (XiQuotient K)) (quotientImage K A) := by
    rw [hS]
    exact not_pairReducible hi hAK hTK
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h1 := pCoreIn_mono_of_normalizes (p := 2)
      (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left) (sup_le K.le_normalizer hTK)
    have h2 := pCoreIn_le_sylow (K ⊔ (T : Subgroup G))
      (T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using h1.trans h2
  let J := X ⊔ ((T : Subgroup G) ⊓ K)
  have hJN : X ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) := by
    apply sup_le ((show X ≤ J from le_sup_left).trans J.le_normalizer)
    exact (le_inf hi.invariant
      ((le_inf (T : Subgroup G).le_normalizer hTK).trans
        inf_normalizer_le_normalizer_inf)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJU : J.pCoreIn 2 ≤ U :=
    (pCoreIn_mono_of_normalizes (sup_le le_sup_left (inf_le_left.trans le_sup_right)) hJN).trans hcore
  have hquotcore : (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).pCoreIn 2 ≤
      quotientImage K U := by
    let F := X.subgroupOf K ⊔ (T : Subgroup G).subgroupOf K
    have hF : F.map K.subtype = J := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXK,subgroupOf_map_subtype]
    have hc : F.pCoreIn 2 ≤ U.subgroupOf K := by
      apply map_le_iff_le_comap.mp
      rw [map_pCoreIn_of_injective 2 F K.subtype K.subtype_injective,hF]
      exact hJU
    have hh := map_mono (f := QuotientGroup.mk' (pCore 2 K)) hc
    rw [map_pCoreIn_of_ker_isPGroup _ (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hh
    simpa only [F,quotientImage,Subgroup.map_sup] using hh
  have hres : (pResidual 2 (quotientImage K X ⊔ quotientImage K (T : Subgroup G) :
      Subgroup (XiQuotient K))).map
      (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).subtype = quotientImage K X := by
    have hp : IsPPerfect 2 (X.subgroupOf K) := hi.perfect.of_surjective
      (subgroupOfEquivOfLe hXK).symm.toMonoidHom (subgroupOfEquivOfLe hXK).symm.surjective
    have hnormal : (T : Subgroup G).subgroupOf K ≤ normalizer (X.subgroupOf K : Set K) := by
      rw [←subgroupOf_normalizer_eq hXK]
      exact comap_mono hi.invariant
    have he := embedded_pResidual_join_pGroup (X.subgroupOf K) ((T : Subgroup G).subgroupOf K)
      hp T.isPGroup'.comap_subtype hnormal
    have hh := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) he
    rw [map_embedded_pResidual,Subgroup.map_sup] at hh
    exact hh
  have hjoin : quotientImage K A ⊔ (S : Subgroup (XiQuotient K)) =
      quotientImage K X ⊔ quotientImage K (T : Subgroup G) := by
    have hcX : X.pCoreIn 2 ≤ (T : Subgroup G) := le_sup_left.trans hi.normalizer_factor.symm.le
    have he : A ⊔ ((T : Subgroup G) ⊓ K) = J := by
      apply le_antisymm (sup_le_sup_right (le_sup_right.trans hi.complement.le) _)
      apply sup_le _ le_sup_right
      rw [←hi.complement]
      exact sup_le ((le_inf hcX ((pCoreIn_le 2 X).trans hXK)).trans le_sup_right) le_sup_left
    have hs := congrArg (fun F : Subgroup G => F.subgroupOf K) he
    change _ = (X ⊔ ((T : Subgroup G) ⊓ K)).subgroupOf K at hs
    rw [subgroupOf_sup hAK inf_le_right,subgroupOf_sup hXK inf_le_right] at hs
    have hTi : ((T : Subgroup G) ⊓ K).subgroupOf K = (T : Subgroup G).subgroupOf K := by
      ext x
      exact and_iff_left x.property
    rw [hTi] at hs
    rw [hS]
    simpa only [quotientImage,Subgroup.map_sup] using
      congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) hs
  have hUS : quotientImage K U ≤ (S : Subgroup (XiQuotient K)) := by
    rw [hS]
    exact map_mono (comap_mono hUT)
  intro g hg
  let a := pCoreNormalizerAction 2 K ⟨g,hHKn hg.1⟩
  have ha : (quotientImage K U).map a.toMonoidHom = quotientImage K U :=
    pCoreNormalizerAction_preserves_image 2 K U ⟨g,hHKn hg.1⟩ hg.2
  have himage : (quotientImage K X).map a.toMonoidHom = quotientImage K X := by
    rcases hn with rfl | rfl
    · exact binary_preserves_residual hodd hperm hirr (m := 3) (by decide) (by decide) hm
        (hjoin.symm ▸ hres) (hjoin.symm ▸ hquotcore) hUS a ha
    · exact binary_preserves_residual hodd hperm hirr (m := 4) (by decide) (by decide) hm
        (hjoin.symm ▸ hres) (hjoin.symm ▸ hquotcore) hUS a ha
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hi.perfect
    (hcT.trans hi.invariant) ⟨g,hHKn hg.1⟩ himage


variable {G : Type*} [Group G] [Finite G]

/-- The Held interval-normalizer calculation preserves the original residual,
including its actual quotient marking and the index-two hypothesis. -/
theorem normalizes_of_held_quotient (T : Sylow 2 G)
    {X A H K U : Subgroup G} (hi : LocalInput 3 (T : Subgroup G) X A H)
    (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hXK : X ≤ K)
    (hUT : U ≤ (T : Subgroup G)) (hcore : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ U)
    (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hq : IsQuasisimple (XiQuotient K)) (hcomm : ⁅K,A⁆ = K)
    (hindex : U.relIndex (T : Subgroup G) ≤ 2)
    (hm : Nonempty (XiQuotient K ≃* Held.He)) :
    H ⊓ normalizer (U : Set G) ≤ normalizer (X : Set G) := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hi.overgroup
  have hHKn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  have hTK := hTH.trans hHKn
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨S,hS⟩ := component_quotient_sylow hSyl hKH hKn
  have hAK : A ≤ K := (le_sup_right.trans hi.complement.le).trans hXK
  have hodd : XiOddQuotient 3 (quotientImage K A) :=
    hi.odd_complement.of_mulEquiv (complementEquiv hi hAK)
  have hperm : (quotientImage K A : Set (XiQuotient K)) * (S : Set (XiQuotient K)) =
      (S : Set (XiQuotient K)) * (quotientImage K A : Set (XiQuotient K)) := by
    simpa only [←hS,Sylow.coe_coe] using component_quotient_permute hi hAK
  have hirr : ¬ PairReducible (S : Subgroup (XiQuotient K)) (quotientImage K A) := by
    rw [hS]
    exact not_pairReducible hi hAK hTK
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h1 := pCoreIn_mono_of_normalizes (p := 2)
      (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left) (sup_le K.le_normalizer hTK)
    have h2 := pCoreIn_le_sylow (K ⊔ (T : Subgroup G))
      (T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)] using h1.trans h2
  let J := X ⊔ ((T : Subgroup G) ⊓ K)
  have hJN : X ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) := by
    apply sup_le ((show X ≤ J from le_sup_left).trans J.le_normalizer)
    exact (le_inf hi.invariant
      ((le_inf (T : Subgroup G).le_normalizer hTK).trans
        inf_normalizer_le_normalizer_inf)).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJU : J.pCoreIn 2 ≤ U :=
    (pCoreIn_mono_of_normalizes (sup_le le_sup_left (inf_le_left.trans le_sup_right)) hJN).trans hcore
  have hquotcore : (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).pCoreIn 2 ≤
      quotientImage K U := by
    let F := X.subgroupOf K ⊔ (T : Subgroup G).subgroupOf K
    have hF : F.map K.subtype = J := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXK,subgroupOf_map_subtype]
    have hc : F.pCoreIn 2 ≤ U.subgroupOf K := by
      apply map_le_iff_le_comap.mp
      rw [map_pCoreIn_of_injective 2 F K.subtype K.subtype_injective,hF]
      exact hJU
    have hh := map_mono (f := QuotientGroup.mk' (pCore 2 K)) hc
    rw [map_pCoreIn_of_ker_isPGroup _ (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hh
    simpa only [F,quotientImage,Subgroup.map_sup] using hh
  have hres : (pResidual 2 (quotientImage K X ⊔ quotientImage K (T : Subgroup G) :
      Subgroup (XiQuotient K))).map
      (quotientImage K X ⊔ quotientImage K (T : Subgroup G)).subtype = quotientImage K X := by
    have hp : IsPPerfect 2 (X.subgroupOf K) := hi.perfect.of_surjective
      (subgroupOfEquivOfLe hXK).symm.toMonoidHom (subgroupOfEquivOfLe hXK).symm.surjective
    have hnormal : (T : Subgroup G).subgroupOf K ≤ normalizer (X.subgroupOf K : Set K) := by
      rw [←subgroupOf_normalizer_eq hXK]
      exact comap_mono hi.invariant
    have he := embedded_pResidual_join_pGroup (X.subgroupOf K) ((T : Subgroup G).subgroupOf K)
      hp T.isPGroup'.comap_subtype hnormal
    have hh := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) he
    rw [map_embedded_pResidual,Subgroup.map_sup] at hh
    exact hh
  have hjoin : quotientImage K A ⊔ (S : Subgroup (XiQuotient K)) =
      quotientImage K X ⊔ quotientImage K (T : Subgroup G) := by
    have hcX : X.pCoreIn 2 ≤ (T : Subgroup G) := le_sup_left.trans hi.normalizer_factor.symm.le
    have he : A ⊔ ((T : Subgroup G) ⊓ K) = J := by
      apply le_antisymm (sup_le_sup_right (le_sup_right.trans hi.complement.le) _)
      apply sup_le _ le_sup_right
      rw [←hi.complement]
      exact sup_le ((le_inf hcX ((pCoreIn_le 2 X).trans hXK)).trans le_sup_right) le_sup_left
    have hs := congrArg (fun F : Subgroup G => F.subgroupOf K) he
    change _ = (X ⊔ ((T : Subgroup G) ⊓ K)).subgroupOf K at hs
    rw [subgroupOf_sup hAK inf_le_right,subgroupOf_sup hXK inf_le_right] at hs
    have hTi : ((T : Subgroup G) ⊓ K).subgroupOf K = (T : Subgroup G).subgroupOf K := by
      ext x
      exact and_iff_left x.property
    rw [hTi] at hs
    rw [hS]
    simpa only [quotientImage,Subgroup.map_sup] using
      congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) hs
  have hUS : quotientImage K U ≤ (S : Subgroup (XiQuotient K)) := by
    rw [hS]
    exact map_mono (comap_mono hUT)
  have hKU : K.pCoreIn 2 ≤ U := by
    apply le_trans _ hcore
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) (hcT.trans le_sup_right)
      ((hi.overgroup.trans hHKn).trans
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hquotindex : (quotientImage K U).relIndex (S : Subgroup (XiQuotient K)) ≤ 2 := by
    have hQU : pCore 2 K ≤ U.subgroupOf K := fun x hx => hKU (mem_map_of_mem K.subtype hx)
    have hQT : pCore 2 K ≤ (T : Subgroup G).subgroupOf K := hQU.trans (comap_mono hUT)
    rw [hS]
    change ((U.subgroupOf K).map _).relIndex (((T : Subgroup G).subgroupOf K).map _) ≤ 2
    rw [relIndex_map_map,QuotientGroup.ker_mk',sup_of_le_left hQU,sup_of_le_left hQT]
    change (U.comap K.subtype).relIndex ((T : Subgroup G).subgroupOf K) ≤ 2
    rw [relIndex_comap,subgroupOf_map_subtype]
    exact (relIndex_le_of_le_right inf_le_left
      (U.subgroupOf (T : Subgroup G)).index_ne_zero_of_finite).trans hindex
  have hpair : PairInput S (quotientImage K A) :=
    ⟨hq,pCore_quotient_pCore_eq_bot 2,(component_quotient_sqtk hsq hKH).stronglyQuasithin,
      (component_quotient_rank hi hsq.stronglyQuasithin hKH hAK).2,hodd,
      component_quotient_commutator hAK hcomm,hperm⟩
  have hrescore : (quotientImage K X).pCoreIn 2 ≤ quotientImage K U := by
    apply le_trans _ hquotcore
    apply pCoreIn_mono_of_normalizes le_sup_left
    have hnX := le_normalizer_embedded_pResidual 2
      (quotientImage K X ⊔ quotientImage K (T : Subgroup G))
    rwa [hres] at hnX
  intro g hg
  let a := pCoreNormalizerAction 2 K ⟨g,hHKn hg.1⟩
  have ha : (quotientImage K U).map a.toMonoidHom = quotientImage K U :=
    pCoreNormalizerAction_preserves_image 2 K U ⟨g,hHKn hg.1⟩ hg.2
  have himage : (quotientImage K X).map a.toMonoidHom = quotientImage K X :=
    SporadicRemaining.HeldPairs.preserves_residual_of_equiv hpair hirr hm.some
      (hjoin.symm ▸ hres) hrescore hUS hquotindex a ha
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image K X hXK hi.perfect
    (hcT.trans hi.invariant) ⟨g,hHKn hg.1⟩ himage



end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private instance : IsElementaryAbelian 3 (Plane 3) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact (by decide +kernel : ∀ x : Plane 3, x^3 = 1)

/-- The original marked core interval excludes both invariant binary
linear quotients; no residual marking is supplied as an extra premise. -/
theorem doubleNatural_four_pure_component_nonbinary_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          K ∈ cComponentsIn H ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsQuasisimple (XiQuotient K) ∧
          ((componentOrbit K (T : Subgroup G)).subgroupOf H).Normal ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          componentOrbit V (T : Subgroup G) ⊓
            centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ ∧
          (Alternatives 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K ∨
            HeldAlternative 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K) ∧
          ¬ ((T : Subgroup G) ≤ normalizer (K : Set G) ∧
            (ClassicalGroup.IsPSL (XiQuotient K) 4 2 ∨
              ClassicalGroup.IsPSL (XiQuotient K) 5 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt⟩ :=
    D.doubleNatural_four_pure_component_embedding_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  refine ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,?_⟩
  rintro ⟨hTK,hmodel⟩
  have horbit : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hTK)
      (le_componentOrbit K T)
  rw [horbit] at hnK he hstrict
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨hXi,hXT,_,⟨e⟩⟩ :=
    D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf
  have hq : XiOddQuotient 3 (XiQuotient X) := by
    apply XiOddQuotient.of_mulEquiv (e := e.symm)
    exact Or.inl ⟨inferInstance,plane_card 3⟩
  have hi := localInput_of_mem_Xi hXi hSyl (show X ⊔ (T : Subgroup G) ≤ H from le_sup_right)
    (by decide : Odd 3) hq A
  have hc : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B.pointSylow w := by
    rw [hXT]
    exact D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf
  have hNH : H ⊓ normalizer (B.pointSylow w : Set G) ≤ normalizer (X : Set G) := by
    rcases hmodel with h4 | h5
    · exact PureFourXi.normalizes_of_binary_quotient T hi hK.1 hnK hstrict.le inf_le_left hc
        (Or.inl rfl) h4
    · exact PureFourXi.normalizes_of_binary_quotient T hi hK.1 hnK hstrict.le inf_le_left hc
        (Or.inr rfl) h5
  have hiT : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
    have hm := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
    change B.pointSylow w = _ at hm
    rw [hm]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  have hiP : (B.pointSylow w).relIndex (P : Subgroup G) = 2 := by
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (T : Subgroup G)
      bot_le inf_le_left
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (P : Subgroup G)
      bot_le hlt.le
    rw [relIndex_bot_left,relIndex_bot_left,hiT] at h1
    rw [relIndex_bot_left,relIndex_bot_left] at h2
    have hcard : Nat.card P = Nat.card T := by rw [P.card_eq_multiplicity,T.card_eq_multiplicity]
    rw [hcard,←h1] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B.pointSylow w)) h2
  have hpnormal : ((B.pointSylow w).subgroupOf (P : Subgroup G)).Normal :=
    normal_of_index_eq_two hiP
  have hPN : (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hlt.le).mp hpnormal
  have hHX : H ≤ normalizer (X : Set G) :=
    sup_le ((le_inf le_sup_left hPN).trans hNH) (sup_le X.le_normalizer hXi.invariant)
  exact hstrict.not_ge (he ▸ conjugateSpanBy_le le_rfl hHX)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All invariant component rows, including the corrected Held row, are
excluded in the actual escaping pure-point overgroup. -/
theorem doubleNatural_four_pure_component_swapped_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          K ∈ cComponentsIn H ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsQuasisimple (XiQuotient K) ∧
          ((componentOrbit K (T : Subgroup G)).subgroupOf H).Normal ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          componentOrbit V (T : Subgroup G) ⊓
            centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ ∧
          Nonempty (((A : Subgroup X).map X.subtype) ≃* Plane 3) ∧
          SwappedFactors (T : Subgroup G) ((A : Subgroup X).map X.subtype) K ∧
          SwappedModel 3 (XiQuotient K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,hnb⟩ :=
    D.doubleNatural_four_pure_component_nonbinary_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let A₀ := (A : Subgroup X).map X.subtype
  refine ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,?_⟩
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨hXi,hXT,⟨eN⟩,⟨eX⟩⟩ :=
    D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf
  have hq : XiOddQuotient 3 (XiQuotient X) := by
    apply XiOddQuotient.of_mulEquiv (e := eX.symm)
    exact Or.inl ⟨inferInstance,plane_card 3⟩
  have hi := localInput_of_mem_Xi hXi hSyl (show X ⊔ (T : Subgroup G) ≤ H from le_sup_right)
    (by decide : Odd 3) hq A
  rcases halt with ⟨hplane,hswap | ⟨hTK,hmodels⟩⟩ | hheld
  · exact ⟨hplane,hswap⟩
  · have horbit : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hTK)
        (le_componentOrbit K T)
    rw [horbit] at hnK hstrict
    obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    have hwreath : Nonempty (XiQuotient (X ⊔ (T : Subgroup G)) ≃*
        Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.ParabolicWreath) := by
      rw [hXT]
      exact ⟨eN.trans (RegularWreathProduct.congr eSL (MulEquiv.refl (Multiplicative (ZMod 2))))⟩
    have hD := Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.automizer_equiv_dihedral
      hi hplane hwreath
    obtain ⟨n,hn,hm,_⟩ :=
      Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.models_of_dihedral
        hi hK.1 hnK hTK hstrict.le hD ⟨hplane,Or.inr ⟨hTK,hmodels⟩⟩
    apply False.elim
    apply hnb
    refine ⟨hTK,?_⟩
    rcases hn with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm
  · have hTK := hheld.2.2.1
    have horbit : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hTK)
        (le_componentOrbit K T)
    rw [horbit] at hnK he hstrict
    have hsq : IsSQTK KnownSimple.IsKnownSimple H := by
      let N := normalizer (H.pCoreIn 2 : Set G)
      have hHN' : H ≤ N := H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
      have hN : IsTwoLocal N := ⟨H.pCoreIn 2,hH.1,isPGroup_pCoreIn 2 H,rfl⟩
      exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN')).mp
        ((h.simpleQTKE.twoLocal_sqtk hN).subgroup (H.subgroupOf N))
    have hcomm : ⁅K,A₀⁆ = K := by
      rcases Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.adequate_three_normalClosure
          hi hsq hSyl with hn | ⟨I,_,_,_,hcI,_,heI,_⟩
      · exact (hstrict.ne' (he.symm.trans hn)).elim
      · rw [←he,heI,hcI]
    have hc : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B.pointSylow w := by
      rw [hXT]
      exact D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf
    have hiT : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
      have hm := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
      change B.pointSylow w = _ at hm
      rw [hm]
      exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
    have hNH : H ⊓ normalizer (B.pointSylow w : Set G) ≤ normalizer (X : Set G) :=
      PureFourXi.normalizes_of_held_quotient T hi hK.1 hnK hstrict.le inf_le_left hc
        hsq hqK hcomm hiT.le hheld.2.2.2
    have hiP : (B.pointSylow w).relIndex (P : Subgroup G) = 2 := by
      have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (T : Subgroup G)
        bot_le inf_le_left
      have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (P : Subgroup G)
        bot_le hlt.le
      rw [relIndex_bot_left,relIndex_bot_left,hiT] at h1
      rw [relIndex_bot_left,relIndex_bot_left] at h2
      have hcard : Nat.card P = Nat.card T := by rw [P.card_eq_multiplicity,T.card_eq_multiplicity]
      rw [hcard,←h1] at h2
      exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B.pointSylow w)) h2
    have hpnormal : ((B.pointSylow w).subgroupOf (P : Subgroup G)).Normal :=
      normal_of_index_eq_two hiP
    have hPN : (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hlt.le).mp hpnormal
    have hHX : H ≤ normalizer (X : Set G) :=
      sup_le ((le_inf le_sup_left hPN).trans hNH) (sup_le X.le_normalizer hXi.invariant)
    exact (hstrict.not_ge (he ▸ conjugateSpanBy_le le_rfl hHX)).elim
end CFSG.Quasithin.Chapter12.Section02.ChosenModule


namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The remaining moved component is either of A5 type, or is genuinely
maximal and admits the Fundamental Setup from the source hypotheses. -/
theorem doubleNatural_four_pure_component_setup_or_a5_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          K ∈ cComponentsIn H ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsQuasisimple (XiQuotient K) ∧
          ((componentOrbit K (T : Subgroup G)).subgroupOf H).Normal ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          componentOrbit V (T : Subgroup G) ⊓
            centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ ∧
          Nonempty (((A : Subgroup X).map X.subtype) ≃* Plane 3) ∧
          SwappedFactors (T : Subgroup G) ((A : Subgroup X).map X.subtype) K ∧
          SwappedModel 3 (XiQuotient K) ∧
          (ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∨
            (K ∈ Chapter1.LStar G (T : Subgroup G) ∧
              Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K))) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,hplane,hswap,hmodel⟩ :=
    D.doubleNatural_four_pure_component_swapped_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  refine ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,hplane,hswap,hmodel,?_⟩
  by_cases ha5 : ClassicalGroup.IsPSL (XiQuotient K) 2 4
  · exact Or.inl ha5
  · have hmove : K < conjugateSpanBy K (T : Subgroup G) := by
      refine lt_of_le_of_ne (le_conjugateSpanBy K (T : Subgroup G)) ?_
      intro heq
      have hn := le_normalizer_conjugateSpanBy K (T : Subgroup G)
      rw [←heq] at hn
      exact hswap.1 hn
    have hmax := Chapter1.Section02.MovedMaximality.moved_local_mem_LStar
      h.simpleQTKE T hKL hmove ha5
    exact Or.inr ⟨hmax,Chapter3.Section02.source_exists_fundamentalSetup h.simpleQTKE T K
      hmax hfaith.2 hqK⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
