module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition

/-!
# Excluding nonquasisimple proper maximal point overcomponents

A nontrivial perfect subgroup of prime-field SL₂ is the full group or
SL₂(5). Thus the seed--point chain has equal images in the containing
two-Fitting quotient, or its point image fills that quotient. A.4.11 and
the completed maximal-local radical theorem make the literal two-Fitting
preimage centralize the original line. Equal images make the point
component fix the line; a full point image makes the containing component
fix the original point. Each contradicts strict comparison.

A.3.6 bounds the two-rank of a nonquasisimple containing quotient. The
complete 11.1.1 field-four catalogue then leaves its nilpotent and
elementary-plane extension rows, both excluded by this argument. Hence
the actual proper maximal container has quasisimple two-core quotient.
SourceModules consumes this result in the negative module comparison.
Earlier geometry, seed marking and R₁ centralization retain final discharge
by qt-d-1222-shadow-components; comparison assembly remains with
qt-d-1222-shadow-component-comparison.
Source: Aschbacher--Smith A.3.6, A.3.12, A.4.11, and 11.4.2, pp.43--48,61,776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem perfect_prime_image_chain {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : A →* SL(2,ZMod p)) [Group.IsSolvable f.ker]
    (U B : Subgroup A) [Group.IsPerfect U] [Nontrivial U] [Group.IsPerfect B]
    (hUB : U ≤ B) : B.map f = U.map f ∨ B.map f = ⊤ := by
  let : Group.IsPerfect (U.map f) := Group.IsPerfect.map f
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
  have hu : U.map f ≠ ⊥ := by
    intro he
    have hk : U ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    exact Group.IsPerfect.not_isSolvable U
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hk) (inclusion_injective hk))
  have hb : B.map f ≠ ⊥ := fun he => hu (bot_unique (he ▸ map_mono hUB))
  let : Nontrivial (U.map f) := (nontrivial_iff_ne_bot _).mpr hu
  let : Nontrivial (B.map f) := (nontrivial_iff_ne_bot _).mpr hb
  by_cases ht : B.map f = ⊤
  · exact Or.inr ht
  have hut : U.map f ≠ ⊤ := fun he => ht (top_unique (he ▸ map_mono hUB))
  obtain ⟨_,⟨eb⟩⟩ := (ChapterA.RankActions.primePerfectSL2Recognition p hp (B.map f)
    inferInstance inferInstance).resolve_left (fun ⟨e⟩ => ht ((B.map f).eq_top_of_card_eq
      (Nat.card_congr e.toEquiv)))
  obtain ⟨_,⟨eu⟩⟩ := (ChapterA.RankActions.primePerfectSL2Recognition p hp (U.map f)
    inferInstance inferInstance).resolve_left (fun ⟨e⟩ => hut ((U.map f).eq_top_of_card_eq
      (Nat.card_congr e.toEquiv)))
  exact Or.inl (eq_of_le_of_card_ge (map_mono hUB)
    ((Nat.card_congr eb.toEquiv).trans (Nat.card_congr eu.toEquiv).symm).le).symm

/-- Perfect chains above a prime SL₂ Fitting quotient either have the
same quotient image or fill that quotient; all kernels remain literal. -/
theorem prime_fitting_chain {U B J : Subgroup G}
    (hUB : U ≤ B) (hBJ : B ≤ J)
    [Group.IsPerfect U] [Nontrivial U] [Group.IsPerfect B]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : Source.IsSL (J ⧸ twoFittingCore J) 2 p) :
    B ≤ U ⊔ (twoFittingCore J).map J.subtype ∨
      J = B ⊔ (twoFittingCore J).map J.subtype := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let r : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := e.trans (Atlas.fieldEquivSL 2 r)
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (twoFittingCore J))
  have hq : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = twoFittingCore J := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  let : Group.IsSolvable q.ker := hk.symm ▸ twoFittingCore_solvable
  have hUJ := hUB.trans hBJ
  let u := subgroupOfEquivOfLe hUJ
  let b := subgroupOfEquivOfLe hBJ
  let : Group.IsPerfect (U.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := u.symm.toMonoidHom) u.symm.surjective
  let : Nontrivial (U.subgroupOf J) := u.surjective.nontrivial
  let : Group.IsPerfect (B.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := b.symm.toMonoidHom) b.symm.surjective
  rcases perfect_prime_image_chain hp q (U.subgroupOf J) (B.subgroupOf J)
      (comap_mono hUB) with he | he
  · have hb : B.subgroupOf J ≤ U.subgroupOf J ⊔ twoFittingCore J := by
      have hh := le_comap_map q (B.subgroupOf J)
      rwa [he,comap_map_eq,hk] at hh
    have hh := map_mono (f := J.subtype) hb
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hUJ] at hh
    exact Or.inl hh
  · have hh := congrArg (comap q) he
    rw [comap_map_eq,hk,comap_top] at hh
    have he := congrArg (map J.subtype) hh
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBJ,
      ←MonoidHom.range_eq_map,range_subtype] at he
    exact Or.inr he.symm

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- The same original line lies in the omega-center of every containing
local Sylow join, by characteristic two and the actual R₁ centralization. -/
theorem line_le_overcomponent_omega
    (_h : EarlierGeometry E) (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hle : E.Kz ≤ J) :
    E.V₁ ≤ omegaOneCenterAmbient ((J ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have hcore : (J ⊔ (T : Subgroup G)).pCoreIn 2 ≤ E.R₁ :=
    pCoreIn_le_of_sylow_le T le_sup_right
      (sup_le_sup_right ((le_conjugateSpanBy _ _).trans hle) _)
  have he : J ⊔ (T : Subgroup G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (E.input.source.simpleQTKE.evenCharacteristic T)
      ⟨hJ.2.2,show (T : Subgroup G) ≤ J ⊔ (T : Subgroup G) from le_sup_right⟩
  let := D.elementary
  intro v hv
  have hc := (hcent.trans (centralizer_le hcore)) hv
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨he ⟨mem_sup_right (D.le_sylow (E.V₁_le hv)),hc⟩,
      elemPow_eq_one_of_isElementaryAbelian v (E.V₁_le hv),hc⟩

/-- The actual two-Fitting preimage of a nonquasisimple maximal container
centralizes the source line. This applies A.4.11 to that container's JT. -/
theorem overcomponent_fitting_centralizes_line
    (h : EarlierGeometry E) (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hrad : MaximalRadicalCentralization T)
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hle : E.Kz ≤ J) (hn : ¬ IsQuasisimple (J ⧸ pCore 2 J)) :
    (twoFittingCore J).map J.subtype ≤ centralizer (E.V₁ : Set G) := by
  exact (ChapterA.Section04.embedded_twoFittingCore_centralizes_omegaCenter_of_radical_reduced
    J (J ⊔ (T : Subgroup G)) le_sup_left hJ.1.1.subnormal (hrad J hJ hn)).trans
      (centralizer_le (line_le_overcomponent_omega h hcent hJ.1 hle))

/-- A prime SL₂ quotient cannot occur above the two-Fitting core of a
proper nonquasisimple maximal point overcomponent. Its perfect image chain
would either make the point component fix the line or make J fix the point. -/
theorem not_prime_fitting_overcomponent
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hU : E.L₁ ∈ Chapter1.L G (T : Subgroup G))
    (hrad : MaximalRadicalCentralization T)
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : E.Kz < J) (hn : ¬ IsQuasisimple (J ⧸ pCore 2 J))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    ¬ Source.IsSL (J ⧸ twoFittingCore J) 2 p := by
  intro hm
  let := Chapter1.mem_L_isPerfect hU
  let := Chapter1.mem_L_isPerfect h.point_mem_local_family
  let u := subgroupOfEquivOfLe (show E.L₁ ≤ E.L₁ ⊔ (T : Subgroup G) from le_sup_left)
  let : Nontrivial (E.L₁.subgroupOf (E.L₁ ⊔ (T : Subgroup G))) :=
    (nontrivial_iff_ne_bot _).mpr hU.1.ne_bot
  let : Nontrivial E.L₁ := u.injective.nontrivial
  have hF := overcomponent_fitting_centralizes_line h hcent hrad hJ hlt.le hn
  rcases prime_fitting_chain (U := E.L₁) (B := E.Kz) (J := J) (le_conjugateSpanBy _ _) hlt.le hp hm with hb | hj
  · exact hne ((h.eq_iff_point_centralizes_line hf).mpr
      (hb.trans (sup_le h.seed_centralizes hF)))
  · apply h.proper_overcomponent_moves_point hJ.1 hlt
    rw [hj]
    exact sup_le h.point_component.1
      (hF.trans (centralizer_le (Set.singleton_subset_iff.mpr h.point_mem)))

/-- The two-rank bound from A.3.6 applies on the actual local container,
independently of whether the point component is already maximal. -/
theorem overcomponent_quotient_two_rank_le_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (J ⧸ pCore 2 J)) :
    primeRank 2 (J ⧸ pCore 2 J) ≤ 1 := by
  let Q := J ⧸ pCore 2 J
  have hl := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup hG T hl
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hsq.subgroup (J.subgroupOf (J ⊔ (T : Subgroup G))))
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q :=
    ChapterE.Structure.sqtk_two_quotient hs (pCore 2 J) pCore_isPGroup
  have htop : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 J)
  by_contra! hr
  change 1 < primeRank 2 Q at hr
  have hr' : 2 ≤ primeRank 2 (⊤ : Subgroup Q) := by
    rw [primeRank_equiv 2 (topEquiv (G := Q))]
    omega
  let := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
    hQ (pCore_quotient_pCore_eq_bot 2) hbar hr'
  exact hn (IsQuasisimple.of_mulEquiv topEquiv)

/-- The original maximal overcomponent has quasisimple two-core quotient.
The complete catalogue and its two odd-extension exclusions are discharged;
only earlier source geometry, the seed marking and R₁ centralization remain. -/
theorem ofFlag_proper_overcomponent_quasisimple
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  by_contra hn
  have hm := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ.1 hlt).2
  have hr := overcomponent_quotient_two_rank_le_one S.source.simpleQTKE hJ.1 hn
  let := Chapter1.mem_L_isPerfect hJ.1
  have hs : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have hu := LocalGeometry.Components.flag_mem_local_of_model D S f 0 hs
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hrad : MaximalRadicalCentralization T := by
    intro I hI hnI
    exact ofFlag_maximal_radical_centralizes S hI hnI
  rcases Frattini.Catalogue.fieldFour_extensions hr hn hm with hnil | ⟨p,hp,he⟩
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact not_prime_fitting_overcomponent h hf hne hcent hu hrad hJ hlt hn
      (by decide : 3 < 5)
      (Frattini.twoFitting_sl2_of_nilpotent_extension (by decide : 3 < 5) (by decide) hnil)
  · let : Fact p.Prime := ⟨hp.1⟩
    have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
    exact not_prime_fitting_overcomponent h hf hne hcent hu hrad hJ hlt hn hp3
      (Frattini.twoFitting_sl2_of_elementary_extension hp3 he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
