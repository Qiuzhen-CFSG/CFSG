module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylowFour
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ModuleAbsorption
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.MarkedCentralizers
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.NativeSourceAssembly
public import Theory.Mathieu.M23.Properties.UniqueNormalFour
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad

/-!
# The simple Mathieu rows in the original paired-cubic component source

A Sylow subgroup of M22 or M23 has a unique normal four-group. The original
marked involution supplies an inner component action and hence absorbs the
first cubic module into the component. Its actual Sylow intersection normalizes
that module. Conjugation by the original x preserves the intersection, so
uniqueness contradicts the recorded noncommutation of the two modules.

The final wrappers construct the marked 1.1.5 hypotheses from the original
ambient Sylow and maximal two-local data; no model action is assumed.
Source: Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

private theorem unique_normal_four_source_false
    (g : SourceCentralizerGeometry c)
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hzK : center K = ⊥)
    (hU : c.U₁ ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hunique : ∀ (P : Sylow 2 K) (V W : Subgroup K),
      V ≤ (P : Subgroup K) → (P : Subgroup K) ≤ normalizer (V : Set K) →
      W ≤ (P : Subgroup K) → (P : Subgroup K) ≤ normalizer (W : Set K) →
      IsElementaryAbelian 2 V → IsElementaryAbelian 2 W →
      Nat.card V = 4 → Nat.card W = 4 → V = W) : False := by
  let H := involutionCentralizer g.z₂
  let U := (c.U₁.subgroupOf H).subgroupOf K
  obtain ⟨P,hP,hUE,hcard,hUP,hPN,_⟩ := g.component_sylow_normal_four K hzK hU
  let x : H := ⟨c.x,g.x_second⟩
  have hxP : x ∈ (g.P₂ : Subgroup H) := by
    have hh : c.x ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_right (mem_zpowers c.x)
    obtain ⟨v,hv,he⟩ := hh
    exact (show v = x from Subtype.ext he) ▸ hv
  let a : MulAut K := MulAut.conjNormal x⁻¹
  have haP : (P : Subgroup K).map a.toMonoidHom = (P : Subgroup K) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨p,hp,rfl⟩
      rw [hP] at hp ⊢
      change ((a p : K) : H) ∈ (g.P₂ : Subgroup H)
      rw [show ((a p : K) : H) = x⁻¹*(p:H)*x by simp only [a,MulAut.conjNormal_apply,inv_inv]]
      exact (g.P₂ : Subgroup H).mul_mem ((g.P₂ : Subgroup H).mul_mem
        ((g.P₂ : Subgroup H).inv_mem hxP) hp) hxP
    · exact le_of_eq (card_map_of_injective a.injective).symm
  have hUa : U = U.map a.toMonoidHom := by
    apply hunique P U (U.map a.toMonoidHom) hUP hPN
    · exact haP ▸ map_mono hUP
    · rw [←haP,←map_equiv_normalizer_eq]
      exact map_mono hPN
    · exact hUE
    · let := hUE
      exact IsElementaryAbelian.map a.toMonoidHom
    · exact hcard
    · exact (card_map_of_injective a.injective).trans hcard
  have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hUH : c.U₁ ≤ H := hUR.trans (fun r hr => mem_centralizer_singleton_iff.mpr (g.second_fixed r hr))
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  apply c.noncommuting
  rintro _ ⟨v,hv,rfl⟩ w hw
  let vH : H := ⟨v,hUH hv⟩
  have hvK : vH ∈ K := by
    obtain ⟨k,hk,he⟩ := hU hv
    exact (show k = vH from Subtype.ext he) ▸ hk
  let vK : K := ⟨vH,hvK⟩
  have hav : a vK ∈ U := hUa.symm ▸ mem_map_of_mem a.toMonoidHom (show vK ∈ U from hv)
  have he : c.x⁻¹*v*c.x ∈ c.U₁ := by
    change (((a vK : K) : H) : G) ∈ c.U₁ at hav
    simpa only [a,MulAut.conjNormal_apply,inv_inv,Subgroup.coe_mul,Subgroup.coe_inv] using hav
  have hcomm : c.U₁ ≤ centralizer (c.U₁ : Set G) := by
    let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
    exact le_centralizer c.U₁
  simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,inv_inv] using (hcomm he) w hw

private theorem normal_four_unique_transport
    {X : Type*} [Group X] [Finite X] {Y : Type*} [Group Y] [Finite Y]
    (e : X ≃* Y)
    (hu : ∀ (P : Sylow 2 Y) (V W : Subgroup Y),
      V ≤ (P : Subgroup Y) → (P : Subgroup Y) ≤ normalizer (V : Set Y) →
      W ≤ (P : Subgroup Y) → (P : Subgroup Y) ≤ normalizer (W : Set Y) →
      IsElementaryAbelian 2 V → IsElementaryAbelian 2 W →
      Nat.card V = 4 → Nat.card W = 4 → V = W)
    (P : Sylow 2 X) (V W : Subgroup X)
    (hVP : V ≤ (P : Subgroup X)) (hPV : (P : Subgroup X) ≤ normalizer (V : Set X))
    (hWP : W ≤ (P : Subgroup X)) (hPW : (P : Subgroup X) ≤ normalizer (W : Set X))
    (hV : IsElementaryAbelian 2 V) (hW : IsElementaryAbelian 2 W)
    (hcV : Nat.card V = 4) (hcW : Nat.card W = 4) : V = W := by
  apply map_injective (f := e.toMonoidHom) e.injective
  apply hu (P.mapSurjective (f:=e.toMonoidHom) e.surjective)
    (V.map e.toMonoidHom) (W.map e.toMonoidHom)
  · exact map_mono hVP
  · rw [←map_equiv_normalizer_eq]
    exact map_mono hPV
  · exact map_mono hWP
  · rw [←map_equiv_normalizer_eq]
    exact map_mono hPW
  · let := hV
    exact IsElementaryAbelian.map e.toMonoidHom
  · let := hW
    exact IsElementaryAbelian.map e.toMonoidHom
  · exact (card_map_of_injective e.injective).trans hcV
  · exact (card_map_of_injective e.injective).trans hcW

private theorem component_inner_of_large_centerless
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hzK : center K = ⊥) (hcard : 2520 < Nat.card K) :
    ∃ α : MulAut K,
      (∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
        (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹) ∧
      α ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨α,hα,hm⟩ := (Chapter1.lemma_1_1_5_three_knownSimple hG _ _ _ _ h K hK).2.2
  refine ⟨α,hα,?_⟩
  rcases ComponentRefinement.inner_or_alternating_quotient_of_modelAction hm with hi | h6 | h7
  · exact hi
  · obtain ⟨e⟩ := h6
    let eZ : K ≃* (K ⧸ center K) :=
      ((QuotientGroup.quotientMulEquivOfEq hzK).trans QuotientGroup.quotientBot).symm
    have hc := Nat.card_congr (eZ.trans e).toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc
    omega
  · obtain ⟨e⟩ := h7
    let eZ : K ≃* (K ⧸ center K) :=
      ((QuotientGroup.quotientMulEquivOfEq hzK).trans QuotientGroup.quotientBot).symm
    have hc := Nat.card_congr (eZ.trans e).toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc
    omega

 theorem SourceCentralizerGeometry.mathieu_twentyTwo_component_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (e : K ≃* Sporadic.Mathieu.M22) : False := by
  have hz : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have he : e k ∈ center _ := by
      exact (centerCongr e ⟨k,hk⟩).property
    have he1 : e k = 1 := by
      simpa only [Sporadic.Mathieu.m22_center_eq_bot,mem_bot] using he
    exact e.injective (he1.trans (map_one e).symm)
  have hc : 2520 < Nat.card K := by
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    decide
  obtain ⟨α,hα,hi⟩ := component_inner_of_large_centerless g hG h K hK hz hc
  have hU := g.first_module_le_component hG h K hK α hα hi hz
  let : K.Normal := g.component_normal_of_first_module h K hK hU
  exact unique_normal_four_source_false g K hz hU
    (normal_four_unique_transport e Sporadic.Mathieu.m22_sylow_normal_four_unique)

 theorem SourceCentralizerGeometry.mathieu_twentyThree_component_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (e : K ≃* Sporadic.Mathieu.M23) : False := by
  have hz : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have he : e k ∈ center _ := by
      exact (centerCongr e ⟨k,hk⟩).property
    have he1 : e k = 1 := by
      simpa only [Sporadic.Mathieu.M23Geometry.m23_center_eq_bot,mem_bot] using he
    exact e.injective (he1.trans (map_one e).symm)
  have hc : 2520 < Nat.card K := by
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    decide
  obtain ⟨α,hα,hi⟩ := component_inner_of_large_centerless g hG h K hK hz hc
  have hU := g.first_module_le_component hG h K hK α hα hi hz
  let : K.Normal := g.component_normal_of_first_module h K hK hU
  exact unique_normal_four_source_false g K hz hU
    (normal_four_unique_transport e Sporadic.Mathieu.m23_sylow_normal_four_unique)

theorem SourceCentralizerGeometry.mathieu_twentyTwo_component_false_from_source
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (e : K ≃* Sporadic.Mathieu.M22) : False :=
  g.mathieu_twentyTwo_component_false hG (g.lemma115 hG hM hTM hu).2 K hK e

theorem SourceCentralizerGeometry.mathieu_twentyThree_component_false_from_source
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (e : K ≃* Sporadic.Mathieu.M23) : False :=
  g.mathieu_twentyThree_component_false hG (g.lemma115 hG hM hTM hu).2 K hK e

end CFSG.Quasithin.Chapter2.DoubleA3
