module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourNormal
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.SevenOrder
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.SpecificGroups.SL2.BinaryThreeSection
/-!
# Finite point models in degree four

The seven-section of the original point residual survives the literal
intersection of L₁T with its containing component, including every further
quotient with kernel prime to seven. In M₂₂ the intersection has nontrivial
two-core, since it contains a full Sylow but its core-free quotient has
order dividing 168. Its core normalizer contradicts the native seven-free
two-local theorem. The same argument excludes the central triple cover.

The native J₂ Sylow-overgroup bound and elementary J₁ Sylows exclude those
rows; orders exclude M₁₁, M₁₂ and the central A₆ cover. FourCatalogue uses
these results in the original 12.9.3 point-component construction.
Source: Aschbacher--Smith 12.9.3, p.858, and A.3.12, pp.47--48.
Adapted from the checked Section05 PointCovers and PointSporadicComplete
proofs, with the original natural degree-four quotients and Sylow marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
  (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) (F : InvariantFlag T V 4)
include h in
private theorem seven_dvd_point_residual : 7 ∣ Nat.card (F.Li L 1) := by
  apply dvd_trans (b := Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)))
  · rw [Nat.card_congr ((Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some).toEquiv]
    change 7 ∣ Nat.card SL(3,ZMod 2)
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  · exact (pCore 2 (F.Li L 1)).card_quotient_dvd_card

private theorem seven_dvd_map_of_coprime_kernel {A X : Type*}
    [Group A] [Finite A] [Group X] (f : A →* X) (B : Subgroup A)
    (hc : Nat.Coprime 7 (Nat.card f.ker)) (h7 : 7 ∣ Nat.card B) :
    7 ∣ Nat.card (B.map f) := by
  let g := f.comp B.subtype
  have hg : Nat.card g.ker ∣ Nat.card f.ker := by
    let j : g.ker →* f.ker := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact card_dvd_of_injective j
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : f.ker => (t : A)) h)))
  have he := g.ker.card_mul_index
  rw [index_ker] at he
  have hrg : g.range = B.map f := by simp [g, MonoidHom.range_comp]
  rw [hrg] at he
  exact (hc.coprime_dvd_right hg).dvd_of_dvd_mul_left (he.symm ▸ h7)

include h earlier

omit earlier in
/-- The seven-section survives both the two-core projection and the coprime quotient. -/
theorem four_point_intersection_seven_dvd {K : Subgroup G}
    (hLK : F.Li L 1 ≤ K)
    {X : Type*} [Group X] (f : (K ⧸ pCore 2 K) →* X)
    (hc : Nat.Coprime 7 (Nat.card f.ker)) :
    7 ∣ Nat.card (fourPointIntersectionImage F L K
      (f.comp (QuotientGroup.mk' (pCore 2 K)))) := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := (F.Li L 1).subgroupOf K
  have h7 : 7 ∣ Nat.card B := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLK).toEquiv]
    exact seven_dvd_point_residual h F
  have hcop : Nat.Coprime 7 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 7 2).pow_right n).coprime_dvd_right hn
  have h7q := seven_dvd_map_of_coprime_kernel q B hcop h7
  have h7f := seven_dvd_map_of_coprime_kernel f (B.map q) hc h7q
  apply h7f.trans (card_dvd_of_le ?_)
  rintro _ ⟨x,⟨b,hb,rfl⟩,rfl⟩
  exact ⟨⟨b,⟨(show F.Li L 1 ≤ F.Li L 1 ⊔ (T : Subgroup G) from le_sup_left) hb,
    b.property⟩⟩,rfl⟩

/-- No coprime-to-seven quotient of the actual component quotient is M₂₂. -/
theorem four_point_component_not_mathieu_central_quotient {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H)) (hLK : F.Li L 1 ≤ K)
    (f : (K ⧸ pCore 2 K) →* Sporadic.Mathieu.M22)
    (hf : Function.Surjective f) (hc : Nat.Coprime 7 (Nat.card f.ker)) : False := by
  let ψ := f.comp (QuotientGroup.mk' (pCore 2 K))
  let J := fourPointIntersectionImage F L K ψ
  obtain ⟨S,hSJ⟩ := four_point_intersection_sylow F hK ψ
    (hf.comp (QuotientGroup.mk'_surjective _))
  have hcore : pCore 2 J ≠ ⊥ := by
    intro hz
    have hcJ := four_point_intersection_corefree_card h earlier F ψ hz
    have h16 : 16 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 4)
      (by rw [Sporadic.Mathieu.m22_order]; decide)
    have hd := (h16.trans (card_dvd_of_le hSJ)).trans hcJ
    norm_num at hd
  have hloc : IsTwoLocal (normalizer (J.pCoreIn 2 : Set Sporadic.Mathieu.M22)) := by
    refine ⟨J.pCoreIn 2,?_,pCore_isPGroup.map J.subtype,rfl⟩
    intro he
    exact hcore ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set Sporadic.Mathieu.M22) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  exact Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal S _ hloc
    (hSJ.trans hJN) ((four_point_intersection_seven_dvd h F hLK f hc).trans
      (card_dvd_of_le hJN))

/-- The central Mathieu22-cover row is impossible for the original point component. -/
theorem four_point_component_not_mathieu_cover {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H)) (hLK : F.Li L 1 ≤ K) :
    ¬ IsM22Cover (K ⧸ pCore 2 K) := by
  intro hm
  let Q := K ⧸ pCore 2 K
  obtain ⟨z⟩ := hm.2.1
  obtain ⟨e⟩ := hm.2.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  apply four_point_component_not_mathieu_central_quotient h earlier F hK hLK f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk : f.ker = center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc : Nat.card f.ker = 3 := by rw [hk]; simpa using Nat.card_congr z.toEquiv
  rw [hc]
  decide

omit earlier in
/-- The point residual's seven-section survives in every containing component quotient. -/
theorem four_point_component_quotient_seven_dvd {K : Subgroup G}
    (hLK : F.Li L 1 ≤ K) : 7 ∣ Nat.card (K ⧸ pCore 2 K) := by
  let f := MonoidHom.id (K ⧸ pCore 2 K)
  have hc : Nat.Coprime 7 (Nat.card f.ker) := by
    simp only [f, MonoidHom.ker_id, card_bot]
    decide
  exact (four_point_intersection_seven_dvd h F hLK f hc).trans
    (fourPointIntersectionImage F L K (f.comp (QuotientGroup.mk' (pCore 2 K)))).card_subgroup_dvd_card

omit earlier in
/-- The actual central three-cover of A₆ has no surviving seven-section. -/
theorem four_point_component_not_alternating_six_cover {K : Subgroup G}
    (hLK : F.Li L 1 ≤ K) : ¬ IsAlternatingCover (K ⧸ pCore 2 K) 6 := by
  intro hm
  let Q := K ⧸ pCore 2 K
  obtain ⟨z⟩ := hm.2.1
  obtain ⟨e⟩ := hm.2.2
  have hc : Nat.card (center Q) = 3 := by simpa using Nat.card_congr z.toEquiv
  have h7 := four_point_component_quotient_seven_dvd h F hLK
  rw [card_eq_card_quotient_mul_card_subgroup (center Q),
    Nat.card_congr e.toEquiv, hc, nat_card_alternatingGroup] at h7
  norm_num [Nat.factorial] at h7

/-- The simple M₂₂ row is excluded using the literal intersection map. -/
theorem four_point_component_not_mathieuTwentyTwo {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn F.H) (hLK : F.Li L 1 ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) : False := by
  apply four_point_component_not_mathieu_central_quotient h earlier F hK hLK
    e.toMonoidHom e.surjective
  rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective,card_bot]
  decide

omit earlier in
/-- Both small Mathieu rows lack the original seven-section. -/
theorem four_point_component_not_small_mathieu {K : Subgroup G}
    (hLK : F.Li L 1 ≤ K)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M11) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M12)) : False := by
  have hd := four_point_component_quotient_seven_dvd h F hLK
  rcases hm with hm | hm
  all_goals obtain ⟨e⟩ := hm
  · rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order] at hd
    norm_num at hd
  · rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order] at hd
    norm_num at hd

/-- The actual Hall–Janko model has no point intersection of the required order. -/
theorem four_point_component_not_jankoTwo {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn F.H) (hLK : F.Li L 1 ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let X := Sporadic.LeechRelated.J2.Carrier
  let ψ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let J := fourPointIntersectionImage F L K ψ
  obtain ⟨S,hSJ⟩ := four_point_intersection_sylow F hK ψ
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have h7 : 7 ∣ Nat.card J := four_point_intersection_seven_dvd h F hLK
    e.toMonoidHom (by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective,card_bot]; decide)
  have hproper : J ≠ ⊤ := by
    intro ht
    let a : J ≃* X := (MulEquiv.subgroupCongr ht).trans topEquiv
    have hcoreX : pCore 2 X = ⊥ := by
      rw [←pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
    have hc := four_point_intersection_core_quotient_card h earlier F ψ
    rw [Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv,
      hcoreX,Nat.card_congr (QuotientGroup.quotientBot).toEquiv] at hc
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hc
    norm_num at hc
  exact Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_not_seven_dvd S J hSJ hproper h7
omit earlier in
/-- The actual J1 quotient cannot support the original binary-three section. -/
theorem four_point_component_not_jankoOne {K : Subgroup G}
    (hLK : F.Li L 1 ≤ K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  let B := F.Li L 1
  let π := ((Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 B))
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hLK))
  have hf : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 K).comap (inclusion hLK) := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 K) (inclusion hLK x)) = 1 ↔ _
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLK)
  apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_subgroup_exponent
    (X := Janko1.Model) _ π
    (((Li_three_core_equiv h F 1 (Or.inr ⟨rfl,Or.inl rfl⟩) rfl).some).surjective.comp (QuotientGroup.mk'_surjective _)) f hf
  intro P hP x
  obtain ⟨S,hS⟩ := hP.exists_le_sylow
  let := Janko1.SylowTwo.elementary S
  exact (inclusion_injective hS) (by
    rw [map_pow,map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S) _)


end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
