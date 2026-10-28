module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.QuasisimpleCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.OddExtensions
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction

/-!
# The complete source relative-component embedding catalogue

A.3.6 supplies the two remaining nonquasisimple carriers. In its natural
kernel case, project the original smaller component to the prime-field
PSL₂ quotient. Its binary simple two-core quotient survives the solvable
kernel. If the image fills PSL₂(p), the field comparison gives p = 5;
otherwise the full Sylow intersection gives both exceptional congruences.
The p = 5 case belongs to the odd nilpotent extension row. Neither step
assumes a splitting or triviality of the smaller intrinsic two-core.

Transport through the literal ambient two-core quotient combines these
branches with the complete quasisimple catalogue. The source applications
prove containment, relative normality and every 11.1.1 alternative at both
flag normalizers and every eligible nontrivial U ≤ V₁. They retain full V₂,
including its fixed layer, and the actual N_T(U) Sylow hypothesis.

Only the preceding flag quotient markings and pointwise line action remain
explicit; qt-d-1222-natural-flag-cartan supplies them, with final discharge
owned by qt-d-1222-natural-local-geometry. Refinement.SourceCatalogue uses
this complete classification in the first-normalizer sieve. The remaining
second-normalizer cases and both field-four triangle orientations stay
with qt-d-1222-natural-relative-components.

Source: Aschbacher--Smith A.3.6, A.3.12--14 and 11.1.1,
printed pp.43--50,761, combined manuscript of 1 March 2004.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding

private theorem extension_prime_parameters
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hp3 : 3 < p)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hext : HasExtension K (fun N _ => Group.IsSolvable N) (fun Q _ => Source.IsSL Q 2 p)) :
    p = 5 ∨ Source.ExceptionalPrime p := by
  obtain ⟨N,hN,hsol,F,_,_,hF,⟨e⟩⟩ := hext
  let := hN
  let := hsol
  let := hK.perfect
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let q := QuotientGroup.mk' N
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let k := e.toMonoidHom.comp q
  let : Group.IsSolvable k.ker := by
    change Group.IsSolvable (e.toMonoidHom.comp q).ker
    rw [MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective]
    infer_instance
  let π : K →* PSL(2,F) := (QuotientGroup.mk' (center SL(2,F))).comp k
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp (QuotientGroup.mk'_surjective N))
  let : Group.IsSolvable π.ker := by
    change Group.IsSolvable ((QuotientGroup.mk' (center SL(2,F))).comp k).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact isSolvable_comap_of_solvable_ker k (center SL(2,F))
  obtain ⟨S,_,hlocal⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK hK.subnormal
  let C := B.subgroupOf K
  let E := C.map π
  have hE : E ∈ localCComponents (S.mapSurjective hπ) :=
    localCComponents_map_of_solvable_ker hlocal π
  let b := subgroupOfEquivOfLe hBK
  let : Group.IsPerfect B := by
    let := hB.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (f := π.subgroupMap C) (π.subgroupMap_surjective C)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := by
    obtain ⟨F',_,_,hF',⟨e'⟩⟩ := hm
    let : IsSimpleGroup PSL(2,F') := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hF']
      exact (show (4 : ℕ) = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn))
    exact e'.isSimpleGroup
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := bq.isSimpleGroup
  let : Group.IsSolvable (π.subgroupMap C).ker := by
    rw [ker_subgroupMap]
    let j : (π.ker.subgroupOf C) →* π.ker :=
      (C.subtype.comp (π.ker.subgroupOf C).subtype).codRestrict π.ker (fun x => x.property)
    apply Group.isSolvable_of_isSolvable_injective (f := j)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => (z : K)) hab))
  let a := PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (π.subgroupMap C) (π.subgroupMap_surjective C)
  let z : (E ⧸ pCore 2 E) ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq
      (Theory.PSL2.odd_perfect_subgroup_twoCore_eq_bot (hF ▸ ho) E)).trans
        QuotientGroup.quotientBot
  have hEm : ClassicalGroup.IsPSL E 2 (2^n) :=
    hm.of_mulEquiv ((a.trans z).symm.trans bq)
  by_cases ht : E = ⊤
  · have he : ClassicalGroup.IsPSL E 2 p :=
      ⟨F,inferInstance,inferInstance,hF,⟨(MulEquiv.subgroupCongr ht).trans topEquiv⟩⟩
    exact .inl (binary_odd_prime_parameters hn hEm hp ho hp3 he).2
  · have htopK : (⊤ : Subgroup K).IsCComponent := by
      simpa only [subgroupOf_self] using hK.subgroupOf le_rfl
    have htop : (⊤ : Subgroup PSL(2,F)).IsCComponent := by
      have h := cComponent_map_of_solvable_ker htopK π hπ
      rwa [map_top_of_surjective π hπ] at h
    obtain ⟨⟨_,_,hsq,h8⟩,_⟩ := SourceEmbeddings.proper_primePSL2_models
      (S.mapSurjective hπ) hE htop le_top ht hp ho
      ⟨F,inferInstance,inferInstance,hF,⟨topEquiv⟩⟩
    refine .inr ⟨hp,?_,h8⟩
    have hbound := Nat.mod_lt p (by decide : 0 < 5)
    interval_cases h : p % 5 <;> simp_all [Nat.pow_mod]

private theorem odd_extension_transport {A C : Type*} [Group A] [Group C]
    (e : A ≃* C) (h : OddExtensionCarrier C) : OddExtensionCarrier A := by
  have step (N : Subgroup C) [N.Normal] :
      ∃ (M : Subgroup A) (_ : M.Normal) (a : M ≃* N),
        Nonempty ((A ⧸ M) ≃* (C ⧸ N)) := by
    let M := N.comap e.toMonoidHom
    have hmap : M.map e.toMonoidHom = N := by
      exact map_comap_eq_self_of_surjective e.surjective N
    exact ⟨M,inferInstance,
      (M.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap),
      ⟨QuotientGroup.congr M N e hmap⟩⟩
  rcases h with ⟨N,hN,⟨hNil,hodd⟩,F,_,_,hF,⟨q⟩⟩ | ⟨p,hp,N,hN,⟨v⟩,F,_,_,hF,⟨q⟩⟩
  · let := hN
    let := hNil
    obtain ⟨M,hM,a,⟨b⟩⟩ := step N
    let := hM
    exact .inl ⟨M,hM,⟨Group.nilpotent_of_mulEquiv a.symm,
      (Nat.card_congr a.toEquiv).symm ▸ hodd⟩,
      F,inferInstance,inferInstance,hF,⟨b.trans q⟩⟩
  · let := hN
    obtain ⟨M,hM,a,⟨b⟩⟩ := step N
    let := hM
    exact .inr ⟨p,hp,M,hM,⟨a.trans v⟩,F,inferInstance,inferInstance,hF,⟨b.trans q⟩⟩

/-- A.3.6 produces the actual odd-extension carrier, and the original
local Sylow forces the exceptional congruences in the elementary row. -/
theorem odd_extension_of_nonquasisimple
    {G : Type*} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B ≤ K)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hnot : ¬ IsQuasisimple K) : OddExtensionCarrier K := by
  have hsource := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    G hG hO K hK
  cases hsource.1 with
  | simple hc _ _ => exact (hnot hc.2).elim
  | cover hc _ _ => exact (hnot hc.2).elim
  | natural h =>
    obtain ⟨p,hp,hp3,F,_,_,hF,v,ρ,_⟩ := h.2
    let : Fact p.Prime := ⟨hp⟩
    let N := generalizedFitting K
    let : Group.IsNilpotent N := by
      change Group.IsNilpotent (generalizedFitting K)
      rw [h.1]
      infer_instance
    have ho : Odd (Nat.card N) := by
      rw [show N = fittingSubgroup K from h.1]
      exact NoncentralFitting.fitting_odd_card hK hO
    have hmodel : Source.IsSL (K ⧸ N) 2 p :=
      ⟨F,inferInstance,inferInstance,hF,⟨ρ⟩⟩
    rcases extension_prime_parameters P hB hK hBK hn hp hp3 hm
      ⟨N,inferInstance,inferInstance,hmodel⟩ with he | he
    · exact .inl ⟨N,inferInstance,⟨inferInstance,ho⟩,he ▸ hmodel⟩
    · let : Fintype F := Fintype.ofFinite F
      let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
      exact .inr ⟨p,he,N,inferInstance,
        ⟨v.trans (AddEquiv.piCongrRight (fun _ : Fin 2 => a.toAddEquiv)).toMultiplicative⟩,
        hmodel⟩
  | nilpotent h =>
    have ho : Odd (Nat.card (generalizedFitting K)) := by
      rw [h.1]
      exact NoncentralFitting.fitting_odd_card hK hO
    exact .inl ⟨generalizedFitting K,inferInstance,⟨h.2.1,ho⟩,h.2.2.1⟩

/-- The full 11.1.1 embedding list, derived from the SQTK source hypotheses
and the smaller binary rank-one quotient, with no assumed carrier list. -/
theorem relative_component_alternative
    {G : Type*} [Group G] [Finite G]
    {H B K P : Subgroup G} (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) :
    ComponentAlternative B K n := by
  by_cases hquasi : IsQuasisimple (K ⧸ pCore 2 K)
  · let := hquasi
    exact relative_quasisimple_component_alternative hH hP hB hK hBK hPB hn hm
  obtain ⟨P₀,hP₀⟩ := hP
  have hPH : P ≤ H := hP₀ ▸ map_subtype_le (P₀ : Subgroup H)
  have hBH : B ≤ H := hBK.trans hK.1
  have hlocal : B.subgroupOf H ∈ localCComponents P₀ := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hPH hBH).mp ⟨hBH,hB⟩
    have he : P.subgroupOf H = (P₀ : Subgroup H) := by
      rw [← hP₀]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he] at hh
    exact hh.1
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := K.subgroupOf H
  let C := J.map q
  let k := subgroupOfEquivOfLe hK.1
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let e : (K ⧸ pCore 2 K) ≃* C := kq.symm.trans (cComponentTwoCoreQuotientEquiv hK.2)
  have hc : ¬ IsQuasisimple C := by
    intro hh
    let := hh
    exact hquasi (IsQuasisimple.of_mulEquiv e.symm)
  let A := B.subgroupOf H
  let b := subgroupOfEquivOfLe hBH
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := (q.subgroupMap A).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective A) hk
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 H)).ker
    rw [QuotientGroup.ker_mk']
    exact _root_.IsNilpotent.to_isSolvable
  let Q : Sylow 2 (H ⧸ pCore 2 H) :=
    P₀.mapSurjective (f := q) (QuotientGroup.mk'_surjective (pCore 2 H))
  have hb : A.map q ∈ localCComponents Q := by
    exact localCComponents_map_of_solvable_ker
      (B := A) (S := (P₀ : Subgroup H)) hlocal q
  have hext := odd_extension_of_nonquasisimple
    (ChapterE.Structure.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup)
    (pCore_quotient_pCore_eq_bot 2) Q
    hb (hK.2.map_quotient (pCore 2 H)) (map_mono (comap_mono hBK)) hn
    (hm.of_mulEquiv (a.symm.trans bq)) hc
  let : Group.IsPerfect B := by
    let := hB.1.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  exact component_alternative_of_odd_extension hBK hn hm (odd_extension_transport e hext)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Source 11.1.1 at both flag normalizers, preserving the full plane. -/
theorem flag_component_alternative (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) : ComponentAlternative (f.Li i) K S.field.degree := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_component_alternative
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal i.castSucc)) hs
    (flag_mem_local_of_model D S f i hm) hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm

/-- Source 11.1.1 for every eligible nontrivial subspace of the first line,
retaining N_T(U) as the actual Sylow subgroup of N_G(U). -/
theorem subspace_component_alternative
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) : ComponentAlternative (f.Li 0) K S.field.degree := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_component_alternative (S.source.simpleQTKE.twoLocal_sqtk ⟨U,hU,htwo,rfl⟩)
    hSyl hlocalP hK hLK (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm

/-- Complete containment, relative normality, model list and uniqueness at
both flag normalizers, with only the preceding rank-one marking explicit. -/
theorem flag_exists_unique_normal_component_alternative (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) K ∧
      f.Li i ≤ K ∧ K ∈ Chapter1.He G ∧ ComponentAlternative (f.Li i) K S.field.degree ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) J →
        f.Li i ≤ J → J = K := by
  obtain ⟨K,hK,hLK,hHe,hu⟩ := flag_exists_unique_normal_component_of_model D S f i hm
  exact ⟨K,hK,hLK,hHe,flag_component_alternative D S f i hm hK.1 hLK,hu⟩

/-- Complete source 11.1.1(i), including arbitrary U, literal Sylow,
relative normality, every quotient alternative and uniqueness. -/
theorem subspace_exists_unique_normal_component_alternative
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K : Subgroup G, Source.NormalComponentIn (normalizer (U : Set G)) K ∧
      f.Li 0 ≤ K ∧ ComponentAlternative (f.Li 0) K S.field.degree ∧
      ∀ J : Subgroup G, Source.ComponentIn (normalizer (U : Set G)) J → f.Li 0 ≤ J → J = K := by
  obtain ⟨K,hK,hLK,hu⟩ :=
    subspace_exists_unique_normal_component_of_model D S f U hU hUV hSyl hm hfix
  exact ⟨K,hK,hLK,subspace_component_alternative D S f U hU hUV hSyl hm hfix hK.1 hLK,hu⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
