module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointRankOne
public import Theory.Mathieu.M22.Properties.TwoLocalSeven

/-!
# Central-cover exclusions for the original point component

The literal image of L₁T ∩ K₁ contains a full Sylow subgroup of every
surjective quotient of K₁. If its two-core vanishes, its order divides
168, the order of the unchanged (L₁T)/O₂(L₁T). The seven-section of L₁
also survives a further quotient with kernel of order prime to seven.

For the central M₂₂ cover, the resulting image in M₂₂ has nontrivial
two-core, since a full Sylow has order divisible by sixteen. Its two-core
normalizer is then a two-local Sylow overgroup divisible by seven,
contrary to the native M₂₂ bound. This excludes the entire cover without
assuming Y ≤ K₁. The seven-section also excludes the central A₆ cover.

PointCatalogue uses both exclusions in the original normal-component
construction. Odd ternary models, the central A₇ cover, general normalizers
and quasisimple strict enlargement remain with qt-d-1251-local; final
exterior assembly belongs to qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3, pp.817--818, using A.3.6 and A.3.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The image of the original Sylow join intersected with the containing component. -/
@[expose] def pointResidualIntersectionImage (K : Subgroup G)
    {X : Type*} [Group X] (f : K →* X) : Subgroup X :=
  (f.comp (inclusion (show (s.marking.Li 1 ⊔ (T : Subgroup G)) ⊓ K ≤ K from inf_le_right))).range

/-- A two-core-free image of the original intersection has order dividing 168. -/
theorem pointResidualIntersectionImage_corefree_card {K : Subgroup G}
    {X : Type*} [Group X] [Finite X] (ψ : K →* X)
    (hcore : pCore 2 (s.pointResidualIntersectionImage K ψ) = ⊥) :
    Nat.card (s.pointResidualIntersectionImage K ψ) ∣ 168 := by
  let J := s.marking.Li 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  let f := ψ.comp (inclusion (show A ≤ K from inf_le_right))
  change pCore 2 f.range = ⊥ at hcore
  have hcoref : pCore 2 A ≤ f.ker := by
    have hh : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    rw [hcore] at hh
    have hh' := (Subgroup.map_eq_bot_iff _).mp (bot_unique hh)
    intro x hx
    exact congrArg Subtype.val (hh' hx)
  let g := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (show A ≤ J from inf_le_left))
  have hkg : IsPGroup 2 g.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hgcore : g.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hkg⟩
  have hgf : g.ker ≤ f.ker := hgcore.trans hcoref
  let r : (A ⧸ g.ker) →* f.range := QuotientGroup.lift g.ker f.rangeRestrict
    (fun x hx => Subtype.ext (hgf hx))
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' g.ker x,hx⟩
  have hcard : Nat.card f.range ∣ 168 := by
    have hd := card_dvd_of_surjective r hr
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
    exact (hd.trans g.range.card_subgroup_dvd_card).trans
      (dvd_of_eq s.point_residual_join_core_card)
  exact hcard

/-- Relative subnormality preserves the full original Sylow in the literal image. -/
theorem pointResidualIntersectionImage_sylow {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    {X : Type*} [Group X] [Finite X] (ψ : K →* X) (hψ : Function.Surjective ψ) :
    ∃ S : Sylow 2 X, (S : Subgroup X) ≤ s.pointResidualIntersectionImage K ψ := by
  let J := s.marking.Li 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  obtain ⟨S,hS⟩ := (T.subtype s.sylow_le_G₁).exists_subgroupOf_eq_of_subnormal C hK.2.subnormal
  let c : C ≃* K := subgroupOfEquivOfLe hK.1
  let P := (S.mapSurjective (f := c.toMonoidHom) c.surjective).mapSurjective hψ
  refine ⟨P,?_⟩
  rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
  have hyT : (y : G) ∈ (T : Subgroup G) := by
    rw [hS] at hy
    exact hy
  have hyA : (y : G) ∈ A := ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hyT,y.property⟩
  exact ⟨⟨y,hyA⟩,rfl⟩

private theorem seven_dvd_point_residual : 7 ∣ Nat.card (s.marking.Li 1) := by
  apply dvd_trans (b := Nat.card (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1)))
  · rw [Nat.card_congr (s.marking.LiCoreEquiv 1 (.inl rfl)).toEquiv]
    change 7 ∣ Nat.card SL(3,ZMod 2)
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  · exact (pCore 2 (s.marking.Li 1)).card_quotient_dvd_card

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

/-- The seven-section survives both the two-core projection and the coprime quotient. -/
theorem pointResidualIntersectionImage_seven_dvd {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K)
    {X : Type*} [Group X] (f : (K ⧸ pCore 2 K) →* X)
    (hc : Nat.Coprime 7 (Nat.card f.ker)) :
    7 ∣ Nat.card (s.pointResidualIntersectionImage K
      (f.comp (QuotientGroup.mk' (pCore 2 K)))) := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := (s.marking.Li 1).subgroupOf K
  have h7 : 7 ∣ Nat.card B := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLK).toEquiv]
    exact s.seven_dvd_point_residual
  have hcop : Nat.Coprime 7 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 7 2).pow_right n).coprime_dvd_right hn
  have h7q := seven_dvd_map_of_coprime_kernel q B hcop h7
  have h7f := seven_dvd_map_of_coprime_kernel f (B.map q) hc h7q
  apply h7f.trans (card_dvd_of_le ?_)
  rintro _ ⟨x,⟨b,hb,rfl⟩,rfl⟩
  exact ⟨⟨b,⟨(show s.marking.Li 1 ≤ s.marking.Li 1 ⊔ (T : Subgroup G) from le_sup_left) hb,
    b.property⟩⟩,rfl⟩

/-- No coprime-to-seven quotient of the actual component quotient is M₂₂. -/
theorem point_component_not_mathieu_central_quotient {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (f : (K ⧸ pCore 2 K) →* Sporadic.Mathieu.M22)
    (hf : Function.Surjective f) (hc : Nat.Coprime 7 (Nat.card f.ker)) : False := by
  let ψ := f.comp (QuotientGroup.mk' (pCore 2 K))
  let J := s.pointResidualIntersectionImage K ψ
  obtain ⟨S,hSJ⟩ := s.pointResidualIntersectionImage_sylow hK ψ
    (hf.comp (QuotientGroup.mk'_surjective _))
  have hcore : pCore 2 J ≠ ⊥ := by
    intro hz
    have hcJ := s.pointResidualIntersectionImage_corefree_card ψ hz
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
    (hSJ.trans hJN) ((s.pointResidualIntersectionImage_seven_dvd hLK f hc).trans
      (card_dvd_of_le hJN))

/-- The central Mathieu22-cover row is impossible for the original point component. -/
theorem point_component_not_mathieu_cover {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K) :
    ¬ IsM22Cover (K ⧸ pCore 2 K) := by
  intro hm
  let Q := K ⧸ pCore 2 K
  obtain ⟨z⟩ := hm.2.1
  obtain ⟨e⟩ := hm.2.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  apply s.point_component_not_mathieu_central_quotient hK hLK f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk : f.ker = center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc : Nat.card f.ker = 3 := by rw [hk]; simpa using Nat.card_congr z.toEquiv
  rw [hc]
  decide

/-- The point residual's seven-section survives in every containing component quotient. -/
theorem point_component_quotient_seven_dvd {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) : 7 ∣ Nat.card (K ⧸ pCore 2 K) := by
  let f := MonoidHom.id (K ⧸ pCore 2 K)
  have hc : Nat.Coprime 7 (Nat.card f.ker) := by
    simp only [f, MonoidHom.ker_id, card_bot]
    decide
  exact (s.pointResidualIntersectionImage_seven_dvd hLK f hc).trans
    (s.pointResidualIntersectionImage K (f.comp (QuotientGroup.mk' (pCore 2 K)))).card_subgroup_dvd_card

/-- The actual central three-cover of A₆ has no surviving seven-section. -/
theorem point_component_not_alternating_six_cover {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) : ¬ IsAlternatingCover (K ⧸ pCore 2 K) 6 := by
  intro hm
  let Q := K ⧸ pCore 2 K
  obtain ⟨z⟩ := hm.2.1
  obtain ⟨e⟩ := hm.2.2
  have hc : Nat.card (center Q) = 3 := by simpa using Nat.card_congr z.toEquiv
  have h7 := s.point_component_quotient_seven_dvd hLK
  rw [card_eq_card_quotient_mul_card_subgroup (center Q),
    Nat.card_congr e.toEquiv, hc, nat_card_alternatingGroup] at h7
  norm_num [Nat.factorial] at h7
end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
