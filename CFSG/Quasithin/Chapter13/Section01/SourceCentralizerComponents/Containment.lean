module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents.Basic
public import Theory.GroupAction.IrreducibleInnerContainment
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Structure
public import Theory.GroupAction.IrreducibleCyclicNormal
public import Theory.GroupAction.IrreducibleElementaryContainment
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure

/-!
# Containment in an irreducibly normalized escaping component

In the normalizer of the escaping component K, the actual Sylow odd complement
of X embeds through the two-core quotient. Frattini factorization transfers
irreducibility from the full actor M ∩ N(K). The genuine A/C inputs and complete
outer-model catalogue make the complement action on the quasisimple image of K
inner. The odd-rank-two containment theorem applies to both source complement
types, including the extraspecial exponent-p group. Coprime absorption lifts the
complement into K; two-perfectness then puts the original X in K.

Only normality inside H ∩ N(K) is used. There is no assumption that K is normal
in H, and no use of the universal A.3.18 residual classification. The canonical
Ξ_p(L) application consumes the same escaping component and full action as the
checked source centralizer structure. Subnormal Sylow restriction also supplies
the component Sylow subgroup needed by the subsequent model marking.

Source: Aschbacher–Smith, proof of 13.1.12, the irreducible N_Mu(K) case on
printed p.874. The rank-two inner-action argument replaces the intervening
A.3.18 residual identification for this particular containment conclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1 Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem le_normal_of_complement {p : ℕ} [Fact p.Prime]
    (X : Subgroup G) (hX : IsPPerfect 2 X)
    (hq : IsPGroup p (XiQuotient X)) (P : Sylow p X)
    (N : Subgroup G) [N.Normal]
    (hPN : (P : Subgroup X).map X.subtype ≤ N) : X ≤ N := by
  let D := N.comap X.subtype
  have hPD : (P : Subgroup X) ≤ D := by
    intro x hx
    exact hPN (mem_map_of_mem X.subtype hx)
  have hgen : D ⊔ pCore 2 X = ⊤ := by
    have hs : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
      apply map_injective X.subtype_injective
      simpa only [Subgroup.map_sup,pCoreIn,← MonoidHom.range_eq_map,range_subtype] using
        RadicalActions.sylow_sup hq P
    exact top_unique (hs ▸ sup_le le_sup_right (hPD.trans le_sup_left))
  have hD : D = ⊤ := hX D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 X) pCore_isPGroup hgen)
  intro x hx
  exact (show (⟨x,hx⟩ : X) ∈ D from hD ▸ mem_top _)

/-- Containment under the full irreducible actor when the component is normal. -/
theorem normal_component_contains_of_irreducible
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (X M K : Subgroup G) (hXM : X ≤ M) (hn : M ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X) (hq : XiOddQuotient p (XiQuotient X))
    (hK : K.IsCComponent) (hQK : IsQuasisimple (XiQuotient K)) [K.Normal]
    (hmove : ⁅K,X⁆ = K)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A=⊥ ∨ A=⊤) :
    X ≤ K := by
  let P : Sylow p X := default
  let P₀ := (P : Subgroup X).map X.subtype
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let R := P₀.map q
  obtain ⟨hR,hi⟩ := quotient_complement_irreducible ho X M hXM hn hq hirr P
  let : IsQuasisimple B := hQK.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  let := pCore_isNilpotent (p := 2) (G := G)
  have hB : B.IsCComponent := hK.map_quotient (pCore 2 G)
  have hqG : IsStronglyQuasithin (G ⧸ pCore 2 G) := by
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans
      (hG.stronglyQuasithin r hr hor)
  have hsq : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) :=
    ⟨hqG, hG.isKGroup.quotient _⟩
  have hf : fittingSubgroup B ≤ center B :=
    (le_solvableRadical (fittingSubgroup B) inferInstance inferInstance).trans
      IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting hA hC hsq B hB hf).2
  have hiR : IsNormalizerFrattiniIrreducible R := hi
  have hinner : R ≤ B ⊔ centralizer (B : Set (G ⧸ pCore 2 G)) :=
    hiR.le_sup_centralizer_of_outer (Fact.out : p.Prime) ho hR.isPGroup hR.not_isCyclic B
      (OuterModels.quasisimple_outer_cyclicNormalOddQuotient hm)
  have hmoveR : ⁅B,R⁆ ≠ ⊥ := by
    intro he
    have hRC : R ≤ centralizer (B : Set (G ⧸ pCore 2 G)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hXC : X ≤ (centralizer (B : Set (G ⧸ pCore 2 G))).comap q :=
      le_normal_of_complement X hX hq.isPGroup P _ (map_le_iff_le_comap.mp hRC)
    have hz : ⁅B,X.map q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (map_le_iff_le_comap.mpr hXC))
    have heB : ⁅B,X.map q⁆ = B := by
      change ⁅K.map q,X.map q⁆ = K.map q
      rw [← map_commutator,hmove]
    exact hB.ne_bot (heB.symm.trans hz)
  have hRB : R ≤ B := hiR.le_normal_of_inner_of_exponent_p hR.isPGroup ho
    hR.not_isCyclic (by
      intro a
      rcases hR with ⟨he,_⟩ | ⟨_,_,hexp⟩
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p a
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (dvd_of_eq hexp) a)
    (hqG p (Fact.out : p.Prime) ho)
    B hinner hmoveR
  have hsup : P₀ ≤ K ⊔ pCore 2 G := by
    have hh := map_le_iff_le_comap.mp hRB
    change P₀ ≤ (K.map q).comap q at hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hPK : P₀ ≤ K := le_normal_of_le_sup_coprime_pGroup P₀ K (pCore 2 G)
    (P.isPGroup'.map X.subtype) pCore_isPGroup (Nat.coprime_two_right.mpr ho) hsup
  exact le_normal_of_complement X hX hq.isPGroup P K hPK

omit [Finite G] in
private theorem xi_irreducible_of_injective
    {D : Type*} [Group D] (f : G →* D) (hf : Function.Injective f)
    (X M : Subgroup G) (hn : M ≤ normalizer (X : Set G))
    (hm : M.map f ≤ normalizer (X.map f : Set D))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (X.map f)),
      (∀ s : M.map f, ∀ a ∈ A,
        xiFrattiniAction (M.map f) (X.map f) hm s a ∈ A) → A=⊥ ∨ A=⊤) :
    ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A=⊥ ∨ A=⊤ := by
  intro A hA
  let e := xiFrattiniMapEquiv f hf X
  have hi : ∀ s : M.map f, ∀ a ∈ A.map e.toMonoidHom,
      xiFrattiniAction (M.map f) (X.map f) hm s a ∈ A.map e.toMonoidHom := by
    intro s
    obtain ⟨t,rfl⟩ := (M.equivMapOfInjective f hf).surjective s
    rintro a ⟨b,hb,rfl⟩
    exact ⟨xiFrattiniAction M X hn t b,hA t b hb,
      xiFrattiniMapEquiv_equivariant f hf M X hn hm t b⟩
  rcases hirr (A.map e.toMonoidHom) hi with hb | ht
  · exact Or.inl ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (map_top_of_surjective e.toMonoidHom e.surjective).symm

/-- Restriction to the actual component normalizer removes ambient component
normality from the containment theorem. -/
theorem component_contains_of_normalizer_irreducible_in
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H X M K : Subgroup G) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hXM : X ≤ M) (hMH : M ≤ H) (hn : M ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X) (hq : XiOddQuotient p (XiQuotient X))
    (hK : K ∈ cComponentsIn H) (hQK : IsQuasisimple (XiQuotient K))
    (hXK : X ≤ normalizer (K : Set G)) (hmove : ⁅K,X⁆ = K)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : (M ⊓ normalizer (K : Set G) : Subgroup G), ∀ a ∈ A,
        xiFrattiniAction (M ⊓ normalizer (K : Set G)) X
          (inf_le_left.trans hn) s a ∈ A) → A=⊥ ∨ A=⊤) : X ≤ K := by
  let N := H ⊓ normalizer (K : Set G)
  let S := M ⊓ normalizer (K : Set G)
  have hSN : S ≤ N := inf_le_inf hMH le_rfl
  have hXN : X ≤ N := le_inf (hXM.trans hMH) hXK
  have hKN : K ≤ N := le_inf hK.1 K.le_normalizer
  have hXS : X ≤ S := le_inf hXM hXK
  have hnS : S ≤ normalizer (X : Set G) := inf_le_left.trans hn
  have hn' : S.subgroupOf N ≤ normalizer (X.subgroupOf N : Set N) :=
    (comap_mono hnS).trans (X.le_normalizer_comap N.subtype)
  have hnmap : (S.subgroupOf N).map N.subtype ≤
      normalizer ((X.subgroupOf N).map N.subtype : Set G) := by
    simpa only [map_subgroupOf_eq_of_le hSN,map_subgroupOf_eq_of_le hXN] using hnS
  have himap : ∀ A : Subgroup (XiFrattiniQuotient ((X.subgroupOf N).map N.subtype)),
      (∀ s : (S.subgroupOf N).map N.subtype, ∀ a ∈ A,
        xiFrattiniAction _ _ hnmap s a ∈ A) → A=⊥ ∨ A=⊤ := by
    revert hnmap
    rw [map_subgroupOf_eq_of_le hXN,map_subgroupOf_eq_of_le hSN]
    intro hnmap
    exact hirr
  have hi' := xi_irreducible_of_injective N.subtype N.subtype_injective
    (X.subgroupOf N) (S.subgroupOf N) hn' hnmap himap
  let eX : XiQuotient (X.subgroupOf N) ≃* XiQuotient X :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXN)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hXN))
  let eK : XiQuotient (K.subgroupOf N) ≃* XiQuotient K :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKN)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKN))
  have hsq : IsSQTK KnownSimple.IsKnownSimple N :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show N ≤ H from inf_le_left))).mp
      (hH.subgroup (N.subgroupOf H))
  have hK' : (K.subgroupOf N).IsCComponent :=
    hK.2.subgroupOf_of_le hKN inf_le_left
  have hQK' : IsQuasisimple (XiQuotient (K.subgroupOf N)) :=
    hQK.of_mulEquiv eK.symm
  let : (K.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKN).mpr inf_le_right
  have hm' : ⁅K.subgroupOf N,X.subgroupOf N⁆ = K.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKN,map_subgroupOf_eq_of_le hXN,hmove]
  have hx' : X.subgroupOf N ≤ K.subgroupOf N :=
    normal_component_contains_of_irreducible hA hC ho hsq
      (X.subgroupOf N) (S.subgroupOf N) (K.subgroupOf N)
      (subgroupOf_mono N hXS) hn'
      (hX.of_surjective (subgroupOfEquivOfLe hXN).symm.toMonoidHom
        (subgroupOfEquivOfLe hXN).symm.surjective)
      (hq.of_mulEquiv eX.symm) hK' hQK' hm' hi'
  have hm := map_mono (f := N.subtype) hx'
  simpa only [map_subgroupOf_eq_of_le hXN,map_subgroupOf_eq_of_le hKN] using hm

/-- In the actual involution centralizer, an irreducible component-normalizer
actor puts the original canonical radical in the escaping component. -/
theorem source_XiP_le_component_of_normalizer_irreducible
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G) (hu : orderOf u = 2)
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (K : Subgroup G) (hK : K ∈ cComponentsIn (centralizer ({u} : Set G)))
    (hQK : IsQuasisimple (XiQuotient K))
    (hXK : XiP p L ≤ normalizer (K : Set G)) (hmove : ⁅K,XiP p L⁆ = K)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓
          normalizer (K : Set G) : Subgroup G), ∀ a ∈ A,
        xiFrattiniAction
          ((normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) ⊓ normalizer (K : Set G))
          (XiP p L) (inf_le_left.trans (XiP_invariant p inf_le_left)) s a ∈ A) →
            A=⊥ ∨ A=⊤) : XiP p L ≤ K := by
  obtain ⟨hq,_,_⟩ := RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd
  exact component_contains_of_normalizer_irreducible_in hA hC ho
    (centralizer ({u} : Set G)) (XiP p L)
    (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) K
    (hG.involution_centralizer_sqtk hu) hXMu inf_le_right (XiP_invariant p inf_le_left)
    (XiP_isPPerfect p L) hq hK hQK hXK hmove hirr

/-- The Sylow two-subgroup needed for the source component marking is the
literal intersection with the ambient centralizer Sylow subgroup. -/
theorem component_sylow_normalizes_radical
    (H X K S : Subgroup G) (hK : K ∈ cComponentsIn H)
    (hS : IsSylowIn 2 S H) (hn : S ≤ normalizer (X : Set G)) :
    ∃ U : Sylow 2 K, (U : Subgroup K).map K.subtype = S ⊓ K ∧
      (U : Subgroup K) ≤ normalizer (X.subgroupOf K : Set K) := by
  obtain ⟨U,hU⟩ := Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hK.1 hK.2.subnormal
  refine ⟨U,hU,?_⟩
  intro x hx
  apply X.le_normalizer_comap K.subtype
  apply hn
  exact (hU ▸ mem_map_of_mem K.subtype hx).1

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
