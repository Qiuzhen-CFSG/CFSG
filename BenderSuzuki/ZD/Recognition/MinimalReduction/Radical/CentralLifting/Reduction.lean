module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Cover
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralQuotient
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The covering component in the central-involution reduction

For a central subgroup `A` of order two, the odd core remains trivial in
`G/A`. The quotient's full ZD conclusion therefore identifies its actual
derived subgroup as a simple Bender group. The component constructed in
`CentralLifting.Cover` covers that factor and is not contained in `M`.
If it is nonsimple, the restricted projection has kernel of order two.

The last theorem makes the source's obstruction argument precise: a
Sylow-centralizing distinguished involution induces the identity on the
component, provided the double-cover Sylow-centralizer theorem is available.
This theorem is explicitly conditional. The genuine Bender-cover rigidity
and reconstruction of the full ZD conclusion in the simple-cover branch
remain separate mathematical obligations.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, printed pp. 34–35 (PDF pp. 51–52),
and Chapter 4, Lemma 2.8(b,c). The PDF corrects duplicated and omitted
passages in the Chapter 2 transcription.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- With full generation and trivial odd core, the ZD model is the actual derived subgroup. -/
public theorem StructureConclusion.derived_model_of_generated_of_oddCore_eq_bot
    (hs : StructureConclusion Z M) (hgen : Subgroup.closure Z = ⊤)
    (hodd : pPrimeCore 2 G = ⊥) : IsSimpleBenderGroup (commutator G) := by
  let L := Subgroup.closure Z
  let e : L ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have ho : pPrimeCore 2 L = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [pPrimeCore_map_iso, hodd, Subgroup.map_bot]
  let eq : (L ⧸ pPrimeCore 2 L) ≃* G :=
    ((QuotientGroup.quotientMulEquivOfEq ho).trans QuotientGroup.quotientBot).trans e
  have hd : (commutator (L ⧸ pPrimeCore 2 L)).map eq.toMonoidHom = commutator G := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eq.surjective]
    rfl
  obtain ⟨u, _, _, _, _, _, _, hmodel, _⟩ := hs
  exact hmodel.map_mulEquiv ((eq.subgroupMap _).trans (MulEquiv.subgroupCongr hd))

/-- The derived subgroup is not contained in the proper distinguished subgroup. -/
public theorem StructureConclusion.derived_not_le_of_generated
    (hs : StructureConclusion Z M) (hgen : Subgroup.closure Z = ⊤)
    (hM : M ≠ ⊤) : ¬ commutator G ≤ M := by
  intro hle
  let L := Subgroup.closure Z
  obtain ⟨u, huM, _, hgenL, _⟩ := hs
  have hder : commutator L ≤ M.comap L.subtype := by
    apply Subgroup.map_le_iff_le_comap.mp
    have hm : (commutator L).map L.subtype ≤ commutator G := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    exact hm.trans hle
  have htop : (⊤ : Subgroup L) ≤ M.comap L.subtype := by
    rw [← hgenL]
    exact sup_le hder (Subgroup.zpowers_le.mpr huM)
  apply hM
  apply top_unique
  intro g hg
  have hgL : g ∈ L := by change g ∈ Subgroup.closure Z; rwa [hgen]
  exact htop (Subgroup.mem_top (⟨g, hgL⟩ : L))

/-- The structural quotient branch supplies an actual Bender model for its derived subgroup. -/
public theorem central_quotient_derived_model
    (hgen : Subgroup.closure Z = ⊤) (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A))) :
    IsSimpleBenderGroup (commutator (G ⧸ A)) := by
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  apply hs.derived_model_of_generated_of_oddCore_eq_bot
  · rw [← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective A)]
  · exact Subgroup.pPrimeCore_quotient_eq_bot_of_central_two_subgroup A hAc hAp hodd

/-- The covering component cannot lie in the distinguished subgroup. -/
public theorem central_quotient_component_not_le
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A))) :
    ¬ centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A)) ≤ M := by
  have hmodel := central_quotient_derived_model hgen hodd A hAc hAcard hs
  have hgenq : Subgroup.closure ((QuotientGroup.mk' A) '' Z) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective A)]
  have hAM : A ≤ M := hAc.trans (center_le_of_productDisconnected h)
  have hM : M.map (QuotientGroup.mk' A) ≠ ⊤ := by
    intro he
    apply h.proper
    apply top_unique
    intro g _
    exact (quotient_mem_map_iff A hAM g).mp (he ▸ Subgroup.mem_top _)
  intro hle
  apply hs.derived_not_le_of_generated hgenq hM
  rw [← centralLiftComponent_map (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
    (commutator (G ⧸ A)) hmodel]
  exact Subgroup.map_mono hle

/-- The central quotient has a normal quasisimple covering component upstairs. -/
public theorem central_quotient_component
    (hgen : Subgroup.closure Z = ⊤) (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A))) :
    IsComponent G (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))) := by
  apply centralLiftComponent_isComponent _ (QuotientGroup.mk'_surjective A)
  · simpa only [QuotientGroup.ker_mk'] using hAc
  · exact central_quotient_derived_model hgen hodd A hAc hAcard hs

/-- A nonsimple covering component has a kernel of exactly order two. -/
public theorem central_quotient_cover_kernel_card_two_of_not_simple
    (A : Subgroup G) [A.Normal] (hAcard : Nat.card A = 2)
    (D : Subgroup (G ⧸ A)) (hD : IsSimpleBenderGroup D)
    (hnot : ¬ IsSimpleGroup (centralLiftComponent (QuotientGroup.mk' A) D)) :
    Nat.card (centralLiftProjection (QuotientGroup.mk' A) D).ker = 2 := by
  let f := centralLiftProjection (QuotientGroup.mk' A) D
  have hne : f.ker ≠ ⊥ := by
    intro he
    let e := MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp he,
      centralLiftProjection_surjective _ (QuotientGroup.mk'_surjective A) D hD⟩
    exact hnot (e.isSimpleGroup_congr.mpr hD.isSimple)
  have hlo : 1 < Nat.card f.ker := (Subgroup.one_lt_card_iff_ne_bot (H := f.ker)).mpr hne
  let i : f.ker → A := fun x => ⟨x.val.val, by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val x.property⟩
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) hxy
  have hhi := Nat.card_le_card_of_injective i hi
  rw [hAcard] at hhi
  change Nat.card f.ker = 2
  omega

/-- Conditional reduction to the genuine double-cover Sylow-centralizer
theorem. The rigidity premise must be discharged from the Bender models. -/
public theorem central_quotient_component_simple_of_rigidity
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A)))
    (hrigidity :
      Nat.card (centralLiftProjection (QuotientGroup.mk' A) (commutator (G ⧸ A))).ker = 2 →
      ∀ (P : Sylow 2 (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))))
        (α : MulAut (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A)))),
        (∀ x : P, α (x : centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))) = x) →
        α = 1) :
    IsSimpleGroup (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))) := by
  classical
  by_contra hnot
  let K := centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))
  have hmodel := central_quotient_derived_model hgen hodd A hAc hAcard hs
  have hcard := central_quotient_cover_kernel_card_two_of_not_simple A hAcard _ hmodel hnot
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  obtain ⟨S, _, hzS⟩ := hcentral z hz
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal K
  let α : MulAut K := MulAut.conjNormal z
  have hfix : ∀ x : P, α (x : K) = x := by
    intro x
    apply Subtype.ext
    have hxS : ((x : K) : G) ∈ S := by
      have hx : (x : K) ∈ (P : Subgroup K) := x.property
      rw [hP] at hx
      exact hx
    change z * ((x : K) : G) * z⁻¹ = ((x : K) : G)
    rw [(hzS ⟨_, hxS⟩).eq, mul_inv_cancel_right]
  have halpha := hrigidity hcard P α hfix
  apply central_quotient_component_not_le h hgen hodd A hAc hAcard hs
  intro k hk
  apply h.centralizer_le hz hzM
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have he := congrArg (fun a : MulAut K => (a ⟨k, hk⟩ : G)) halpha
  change z * k * z⁻¹ = k at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end BenderSuzuki.ZD
