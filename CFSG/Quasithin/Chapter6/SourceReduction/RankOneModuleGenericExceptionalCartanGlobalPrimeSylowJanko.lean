module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.JankoLocal
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.CubicCoreQuotientNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeComponentSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeHallRank

/-!
# J₁ exclusions at the smaller changed Sylow

The literal quotient X/O₂(X), for X = G₀T₀, carries a faithful prime
actor on its normal containing component. If that component is J₁, the
actor is cubic: a solvable Sylow join in J₁ normalizes the elementary
Sylow group of order eight. A quintic actor would centralize that Sylow,
contradicting the certified order-five normalizer bound.

When the selected right factor has A₅ quotient, its actual Hall
intersection B∩R has order three. It centralizes D, so their join is a
three-group. Since Out(J₁) is trivial and nine does not divide |J₁|,
B∩R fills the induced action image. The perfect-subgroup core-kernel
argument forces D to normalize R, contradicting its source movement.
This works for A₅ parabolic factors as well as actual H-components.
Combining with the non-A₅ component theorem removes J₁ for every
actual H-component, without imposing a non-A₅ hypothesis.

Source: Aschbacher–Smith 5.1.13 and 5.2.2, printed pp.636–638,648–649;
GLS3 Table 5.3f for the certified J₁ model calculations. The smaller-Sylow
hypothesis remains explicit; this module does not claim the full 5.2.2
normalization theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoActors

private theorem no_five_solvable (S : Sylow 2 Janko1.Model) (E : Subgroup Janko1.Model)
    (hE : Nat.card E = 5)
    (hs : Group.IsSolvable (E ⊔ (S : Subgroup Janko1.Model) : Subgroup _)) : False := by
  let := hs
  have hn : E ≤ normalizer (S : Set Janko1.Model) := le_sup_left.trans
    (CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow.janko_one_model_solvable_overgroup_le_normalizer
      (MulEquiv.refl _) S (E ⊔ (S : Subgroup Janko1.Model)) le_sup_right)
  let f : E →* MulAut S := (S : Subgroup Janko1.Model).normalizerMonoidHom.comp (inclusion hn)
  let := Janko1.SylowTwo.elementary S
  have hAut : Nat.card (MulAut S) = 168 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow S 3
      (by simpa using Janko1.SylowTwo.card S)]
    norm_num [Fin.prod_univ_succ]
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (MulAut S)) := by
    rw [hE,hAut]
    decide
  have hr : f.range = ⊥ := f.range.eq_bot_of_card_eq
    (Nat.eq_one_of_dvd_coprimes hcop (card_range_dvd f) f.range.card_subgroup_dvd_card)
  have hc : (S : Subgroup Janko1.Model) ≤ centralizer (E : Set Janko1.Model) := by
    intro s hs e he
    have hh : f ⟨e,he⟩ = 1 := mem_bot.mp (hr ▸ (show f ⟨e,he⟩ ∈ f.range from ⟨⟨e,he⟩,rfl⟩))
    have hx := congrArg (fun a : MulAut S => (a ⟨s,hs⟩ : Janko1.Model)) hh
    change e * s * e⁻¹ = s at hx
    exact mul_inv_eq_iff_eq_mul.mp hx
  have hd := card_dvd_of_le (hc.trans (centralizer_le_normalizer (E : Set Janko1.Model)))
  rw [Janko1.SylowTwo.card S] at hd
  exact Janko1.LocalStructure.primeNormalizerBound_five E hE hd

private noncomputable def innerEquiv : Janko1.Model ≃* MulAut Janko1.Model := by
  have hc : center Janko1.Model = ⊥ :=
    (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp he))
  exact MulEquiv.ofBijective _ ⟨conj_injective_of_center_eq_bot hc,Janko1.OuterCertificate.aut_inner⟩

variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem exists_action (K : Subgroup G) [K.Normal] (e : K ≃* Janko1.Model) :
    ∃ f : G →* Janko1.Model, f.ker = centralizer (K : Set G) ∧ Function.Surjective f := by
  let f : G →* Janko1.Model := innerEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : G →* MulAut K))
  have hf (k : K) : f k = e k := by
    apply innerEquiv.injective
    change innerEquiv (innerEquiv.symm (MulAut.congr e (MulAut.conjNormal (k : G)))) = _
    rw [innerEquiv.apply_symm_apply]
    have hk : (MulAut.conjNormal (k : G) : MulAut K) = MulAut.conj k := by
      ext x
      rfl
    rw [hk]
    exact MulAut.congr_conj e k
  refine ⟨f,?_,?_⟩
  · ext g
    change innerEquiv.symm (MulAut.congr e (MulAut.conjNormal g)) = 1 ↔ _
    rw [←map_one innerEquiv.symm,innerEquiv.symm.injective.eq_iff,
      ←map_one (MulAut.congr e),(MulAut.congr e).injective.eq_iff]
    change g ∈ (MulAut.conjNormal : G →* MulAut K).ker ↔ _
    rw [MulAut.conjNormal_ker_eq_centralizer]
  · intro x
    obtain ⟨k,rfl⟩ := e.surjective x
    exact ⟨k,hf k⟩

private theorem no_five_actor (K E : Subgroup G) [K.Normal]
    (e : K ≃* Janko1.Model) (S : Sylow 2 G)
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hs : Group.IsSolvable (E ⊔ (S : Subgroup G) : Subgroup G)) : False := by
  obtain ⟨f,hker,hf⟩ := exists_action K e
  have hi : Function.Injective (f.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxk : (x : G) ∈ centralizer (K : Set G) := hker ▸ hx
    exact Subtype.ext (mem_bot.mp ((disjoint_iff.mp hd) ▸ ⟨x.property,hxk⟩))
  have hc : Nat.card (E.map f) = 5 := by
    have hr : (f.comp E.subtype).range = E.map f := by rw [MonoidHom.range_comp,range_subtype]
    rw [←hr,←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,hE]
  let := hs
  have hsol := Group.isSolvable_of_surjective (f.subgroupMap_surjective (E ⊔ (S : Subgroup G)))
  rw [Subgroup.map_sup] at hsol
  exact no_five_solvable (S.mapSurjective hf) (E.map f) hc hsol

private theorem cubic_normalizes (R K D C : Subgroup G) [Group.IsPerfect R]
    (e : (K ⧸ pCore 2 K) ≃* Janko1.Model) (hRK : R ≤ K)
    (hDK : D ≤ normalizer (K : Set G)) (hCR : C ≤ R)
    (hCD : C ≤ centralizer (D : Set G))
    (hQ : K.pCoreIn 2 ≤ normalizer (R : Set G))
    (hD : Nat.card D = 3) (hC : Nat.card C = 3) :
    D ≤ normalizer (R : Set G) := by
  have hA : D ⊔ C ≤ normalizer (K : Set G) :=
    sup_le hDK ((hCR.trans hRK).trans K.le_normalizer)
  have hp : IsPGroup 3 (D ⊔ C : Subgroup G) :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hD)).to_sup_of_normal_left'
      (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hC))
      (hCD.trans (centralizer_le_normalizer (D : Set G)))
  have hzJ : center Janko1.Model = ⊥ :=
    (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp he))
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have hj := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center Janko1.Model at hj
    rw [hzJ,mem_bot] at hj
    exact e.injective (hj.trans e.map_one.symm)
  let : Subsingleton (MulAut.Outer (K ⧸ pCore 2 K)) := by
    let := Janko1.OuterCertificate.outer_subsingleton
    exact (MulAut.outerCongr e).injective.subsingleton
  have hout : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) := IsPGroup.of_subsingleton _ _
  have hcard : ¬ 9 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr e.toEquiv,Janko1.card_model]
    norm_num
  exact le_sup_left.trans (CubicCoreQuotientNormalizer.normalizes_of_small_image
    R K (D ⊔ C) C hRK hA le_sup_right hCR hQ hC hz
    (CubicCoreQuotientNormalizer.cubic_action_image_card_le_three _ hp hz hout hcard))
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoActors

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
/-- A J₁ containing quotient forces the original escaping actor to be cubic. -/
theorem LocalData.source_overcomponent_janko_prime
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal)
    (e : (K ⧸ pCore 2 K) ≃* Janko1.Model) :
    p = 3 := by
  rcases hd.prime with hp | hp
  · exact hp
  subst p
  exfalso
  let X := generated L H D R ⊔ normalizingSylow T R
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let Dbar := (D.subgroupOf X).map q
  have hRX : R ≤ X := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have hDX : D ≤ X := le_sup_left.trans le_sup_left
  have hTX : normalizingSylow T R ≤ X := le_sup_right
  obtain ⟨hc,hdis,_⟩ := d.right_quotient_prime_orbit h hH c hd hz hRX hDX hSyl
  obtain ⟨S,hS⟩ := hSyl
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let : (K.subgroupOf X).Normal := hKn
  let : Kbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let : Group.IsPerfect Kbar := (hK.map_quotient (pCore 2 X)).perfect
  have hdC : Disjoint Dbar (centralizer (Kbar : Set (X ⧸ pCore 2 X))) :=
    hdis.mono_right ((centralizer_le (map_mono (comap_mono hRK))).trans
      (centralizer_le_normalizer (Rbar : Set (X ⧸ pCore 2 X))))
  have hsol : Group.IsSolvable (Dbar ⊔ (P : Subgroup (X ⧸ pCore 2 X)) : Subgroup _) := by
    let := d.actor_join_solvable h hH c hd
    let : Group.IsSolvable ((D ⊔ normalizingSylow T R).subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (sup_le hDX hTX)).toMonoidHom)
        (subgroupOfEquivOfLe (sup_le hDX hTX)).injective
    have hs : Group.IsSolvable (((D ⊔ normalizingSylow T R).subgroupOf X).map q) :=
      Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
    change Group.IsSolvable (Dbar ⊔ (S : Subgroup X).map q : Subgroup _)
    rw [heS]
    rw [subgroupOf_sup hDX hTX,Subgroup.map_sup] at hs
    exact hs
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  exact JankoActors.no_five_actor Kbar Dbar (eK.trans e) P hc hdC hsol


/-- The original cubic Hall intersection excludes J₁ for every A₅ right factor,
including a factor in a rank-one parabolic. -/
theorem LocalData.A5_right_not_janko_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  have hp := d.source_overcomponent_janko_prime h hH c hd hz hSyl hRK hKX hK hKn e
  subst p
  let X := generated L H D R ⊔ normalizingSylow T R
  let := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  have hXK : X ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKX).mp hKn
  have hDK : D ≤ normalizer (K : Set G) :=
    (le_sup_left.trans le_sup_left).trans hXK
  obtain ⟨S,hS⟩ := hSyl
  have hQ : K.pCoreIn 2 ≤ normalizer (R : Set G) :=
    (pCoreIn_mono_of_normalizes hKX hXK).trans
      ((hS ▸ pCoreIn_le_sylow X S).trans inf_le_right)
  have hC : Nat.card (B ⊓ R : Subgroup G) = 3 := by
    simpa using d.right_cartan_card c (m := 2) hA5
  have hn := JankoActors.cubic_normalizes R K D (B ⊓ R) e hRK hDK inf_le_right
    (inf_le_left.trans (c.centralizes_prime_actor h hd)) hQ hd.card hC
  exact d.prime_actor_not_normalizes_right h hH c hd hz hn

/-- Both A₅ and non-A₅ actual components exclude the J₁ containing quotient. -/
theorem LocalData.component_source_not_janko_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent)
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R < K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  by_cases hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4
  · exact d.A5_right_not_janko_container h hH c hd hz hA5 hSyl hRK.le hKX hK hKn
  · exact d.component_source_overcomponent_not_janko h hH c hd hz hC hA5 hSyl
      (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
