module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.InvariantSieve
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedLayer
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.InvariantResidual

/-!
# The invariant closure and the full binary automorphism quotient

For an invariant PSL₄(2) or PSL₅(2) component, the existing local outer-action
calculation identifies the prime-to-three residual. Rank two forces its
centralizer to have order prime to three. The proved solvable-overgroup prime
bound and Suzuki exclusion then show that its image is the full generalized
Fitting subgroup of Mc/O₂(Mc).

Faithful conjugation on this centerless image embeds the full quotient in its
automorphism group. The actual component-Sylow join already fills that group,
so comparison of orders proves the full quotient isomorphism and Mc = L T.
InvariantSource supplies all these premises from the original rank-two setup.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding Chapter1.XiEmbedding.InvariantThree
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter15.Section04.LocalSetup.EmbeddingReduction
variable {G : Type*} [Group G] [Finite G]

private theorem centerless_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center A = ⊥) : center B = ⊥ := by
  rw [← Subgroup.center_map_equiv e,h,Subgroup.map_bot]

private theorem centralizer_three_coprime (L : Subgroup G)
    (hz : center L = ⊥) (hr : 2 ≤ primeRank 3 L) (hG : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer (L : Set G))) := by
  let P : Sylow 3 L := default
  have hn : ¬ IsCyclic P := by
    intro hc
    have hh := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨A,_,hA,he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let := he
  let E := (A.map (P : Subgroup L).subtype).map L.subtype
  let : IsElementaryAbelian 3 (A.map (P : Subgroup L).subtype) := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  apply prime_not_dvd_card_centralizer_of_full_rank L E (map_subtype_le _) _ hG hz
  simpa only [E,card_map_of_injective L.subtype_injective,
    card_map_of_injective (P : Subgroup L).subtype_injective] using hA

/-- The invariant binary closure is the literal prime-to-three residual and
its quotient image is the entire generalized Fitting subgroup. -/
theorem invariant_binary_closure_layer
    {T H P Mc L : Subgroup G} (h : LocalInput 3 T (residual H) P Mc)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Mc) (hHMc : H ≤ Mc)
    (hsol : Group.IsSolvable H) (hbound : SolvableOvergroupPrimeBound H Mc 3)
    (hno : NoSuzukiComponents Mc) (hL : L ∈ cComponentsIn Mc)
    (hn : (L.subgroupOf Mc).Normal) (hq : IsQuasisimple (XiQuotient L))
    (hcl : residualClosure H Mc = L)
    {n : ℕ} (hn' : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (XiQuotient L) n 2) :
    residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure H Mc) := by
  have hXL : residual H ≤ L := (le_conjugateSpanBy _ _).trans_eq hcl
  have hmodels : ClassicalGroup.IsPSL (XiQuotient L) 4 2 ∨
      ClassicalGroup.IsPSL (XiQuotient L) 5 2 := by
    rcases hn' with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm
  have hres : residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype :=
    le_antisymm (localInput_closure_le_primeToResidual h)
      ((binary_residual_le hsq h hL hn hXL hmodels).trans hcl.ge)
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let K := (L.subgroupOf Mc).map q
  let ec : XiQuotient L ≃* K :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL.1)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hL.1))).symm.trans
      (cComponentTwoCoreQuotientEquiv hL.2)
  let : IsQuasisimple (XiQuotient L) := hq
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv ec
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  have hK : IsComponent (Mc ⧸ pCore 2 Mc) K :=
    ⟨(hL.2.map_quotient (pCore 2 Mc)).subnormal,inferInstance⟩
  have hz : center K = ⊥ := centerless_of_equiv ec
    (Chapter15.Section04.LocalSetup.binary_linear_center_eq_bot (by omega : 0 < n) hm)
  have hr : 2 ≤ primeRank 3 K := by
    rw [←primeRank_equiv 3 ec]
    exact (component_quotient_rank h hsq.stronglyQuasithin hL.1
      ((le_sup_right.trans h.complement.le).trans hXL)).2.ge
  have hc := centralizer_three_coprime K hz hr
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 Mc) pCore_isPGroup).trans
      (hsq.stronglyQuasithin 3 (by decide) (by decide)))
  have hfit := fitting_quotient_eq_bot_of_closure_centralizers
    hHMc hsol hbound K (le_sSup hK) hc (by omega)
  let : K.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hlayer := closure_eq_generalizedFitting_of_centralizer Mc hsq hno K (le_sSup hK) hfit hc
  exact ⟨hres,hfit,by simpa only [hcl] using hlayer⟩

private theorem core_quotient_card_le_range
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hk : IsPGroup 2 f.ker) :
    Nat.card (A ⧸ pCore 2 A) ≤ Nat.card f.range := by
  rw [←index_eq_card]
  exact (index_antitone (le_sSup ⟨inferInstance,hk⟩ : f.ker ≤ pCore 2 A)).trans_eq (index_ker f)

private theorem quotient_card_le_of_subgroup (J Mc : Subgroup G) (hle : J ≤ Mc) :
    Nat.card (J ⧸ pCore 2 J) ≤ Nat.card (Mc ⧸ pCore 2 Mc) := by
  let A := J.subgroupOf Mc
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let f := q.comp A.subtype
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 Mc)).comp A.subtype).ker)
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hleker : f.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hk⟩
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hle)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hle))
  rw [←Nat.card_congr e.toEquiv,←index_eq_card]
  calc
    (pCore 2 A).index ≤ f.ker.index := index_antitone hleker
    _ = Nat.card f.range := index_ker f
    _ ≤ Nat.card (Mc ⧸ pCore 2 Mc) := Nat.card_le_card_of_injective _ f.range.subtype_injective

/-- Once the invariant binary image exhausts F*, the full Mc quotient is
the automorphism group already filled by the actual Sylow join. -/
theorem invariant_binary_full_quotient
    {T H P Mc L : Subgroup G} (h : LocalInput 3 T (residual H) P Mc)
    (hT : IsSylowIn 2 T Mc) (hL : L ∈ cComponentsIn Mc)
    (hn : (L.subgroupOf Mc).Normal) (hcl : residualClosure H Mc = L)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    {n : ℕ} (hn' : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (XiQuotient L) n 2) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let K := (L.subgroupOf Mc).map q
  let ec : XiQuotient L ≃* K :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL.1)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hL.1))).symm.trans
      (cComponentTwoCoreQuotientEquiv hL.2)
  have hz : center K = ⊥ := centerless_of_equiv ec
    (Chapter15.Section04.LocalSetup.binary_linear_center_eq_bot (by omega : 0 < n) hm)
  let : K.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hF : K = generalizedFitting (Mc ⧸ pCore 2 Mc) := by
    simpa only [hcl] using hlayer.image_eq_generalizedFitting
  have hcentral : centralizer (K : Set (Mc ⧸ pCore 2 Mc)) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxK : x ∈ K := by
      have hh := centralizer_generalizedFitting_le (Mc ⧸ pCore 2 Mc)
      rw [←hF] at hh
      exact hh hx
    have hxZ : (⟨x,hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hx y y.property)
    exact congrArg Subtype.val (show (⟨x,hxK⟩ : K) = 1 from by simpa only [hz,mem_bot] using hxZ)
  let f : (Mc ⧸ pCore 2 Mc) →* MulAut K := MulAut.conjNormal
  have hf : Function.Injective f := MulAut.conjNormal_injective_of_centralizer_eq_bot K hcentral
  have hXL : residual H ≤ L := (le_conjugateSpanBy _ _).trans_eq hcl
  obtain ⟨ej⟩ := BinaryAction.binary_quotient_aut_of_local h hT hL.1 hn hXL hn' hm
  have hcard : Nat.card (MulAut K) ≤ Nat.card (Mc ⧸ pCore 2 Mc) := by
    rw [←Nat.card_congr (MulAut.congr ec).toEquiv,←Nat.card_congr ej.toEquiv]
    exact quotient_card_le_of_subgroup (L ⊔ T) Mc
      (sup_le hL.1 (le_sup_right.trans h.overgroup))
  let eFull := MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hcard)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨eFull.trans (MulAut.congr (ec.symm.trans (e.trans (Atlas.fieldEquivPSL n ef))))⟩
/-- The same literal full automorphism quotient forces Mc to be generated
by the invariant component and the original Sylow subgroup. -/
theorem invariant_binary_join_eq
    {T H P Mc L : Subgroup G} (h : LocalInput 3 T (residual H) P Mc)
    (hT : IsSylowIn 2 T Mc) (hL : L ∈ cComponentsIn Mc)
    (hn : (L.subgroupOf Mc).Normal) (hXL : residual H ≤ L)
    {n : ℕ} (hn' : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (XiQuotient L) n 2)
    (hfull : Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) : Mc = L ⊔ T := by
  have hJMc : L ⊔ T ≤ Mc := sup_le hL.1 (le_sup_right.trans h.overgroup)
  let A := (L ⊔ T).subgroupOf Mc
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let f := q.comp A.subtype
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 Mc)).comp A.subtype).ker)
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  obtain ⟨ej⟩ := BinaryAction.binary_quotient_aut_of_local h hT hL.1 hn hXL hn' hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let em := e.trans (Atlas.fieldEquivPSL n ef)
  let eA := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hJMc)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hJMc))
  have hlo : Nat.card (Mc ⧸ pCore 2 Mc) ≤ Nat.card f.range := by
    rw [Nat.card_congr hfull.some.toEquiv,←Nat.card_congr (MulAut.congr em).toEquiv,
      ←Nat.card_congr ej.toEquiv,←Nat.card_congr eA.toEquiv]
    exact core_quotient_card_le_range f hk
  have hr : f.range = ⊤ := f.range.eq_top_of_card_eq
    (le_antisymm (Nat.card_le_card_of_injective _ f.range.subtype_injective) hlo)
  have hcore : pCore 2 Mc ≤ A := by
    obtain ⟨S,hS⟩ := hT
    intro x hx
    have ht : (x : G) ∈ T := hS ▸ mem_map_of_mem Mc.subtype
      ((pCore_isPGroup (p := 2) (G := Mc)).le_sylow_of_normal S hx)
    exact (show T ≤ L ⊔ T from le_sup_right) ht
  have hA : A = ⊤ := by
    have hm : A.map q = ⊤ := by
      simpa only [f,MonoidHom.range_comp,range_subtype] using hr
    have hker : q.ker ≤ A := by
      simpa only [q,QuotientGroup.ker_mk'] using hcore
    have hh := congrArg (comap q) hm
    simpa only [comap_map_eq_self hker,comap_top] using hh
  have hh := congrArg (map Mc.subtype) hA
  simpa only [A,map_subgroupOf_eq_of_le hJMc,←MonoidHom.range_eq_map,range_subtype] using hh.symm

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
