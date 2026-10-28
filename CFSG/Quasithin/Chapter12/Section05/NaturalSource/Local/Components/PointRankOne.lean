module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.ParabolicImage
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.SpecificGroups.PSL2.NormalPerfectOvergroupCore
public import Theory.GroupTheory.CComponent.LocalImageEquality

/-!
# Non-enlargement of the rank-one point-component models

The proper full-Sylow overgroups of the Bender models, binary L₃(2),
and even SU₃ covers are solvable, so their actual containing component
coincides with L₁. In odd-prime PSL₂, a proper enlargement would make
the point-residual image A₅, contrary to its surviving seven-section.

For a quadratic prime field a proper enlargement identifies that image
with PSL₂(p). Its original quotient has order 168, forcing p = 7. To
exclude L₂(49), intersect K₁ with the original L₁T. The image of L₁
is a nontrivial normal perfect subgroup, so the image of the intersection
has trivial two-core. Its order therefore divides the order 168 of the
original (L₁T)/O₂(L₁T), retaining the literal actor and Sylow. But it
contains a full Sylow subgroup of L₂(49), of order 16, a contradiction.

PointCore.PointNonenlargement supplies the original component, normalizer,
point-core, point-control and generation-one applications. The other point
models and remaining source branches belong to qt-d-1251-local; final
exterior assembly belongs to qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3, printed pp.817--818, using the proved
full-Sylow branches of A.3.12. All models retain actual isomorphisms.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem point_local_in_normalizer :
    (s.marking.Li 1).subgroupOf (s.marking.Gi 1) ∈
      Chapter1.L (s.marking.Gi 1) (T.subtype s.sylow_le_G₁) := by
  simpa only [Sylow.coe_subtype] using
    (Chapter1.mem_LIn_iff_subgroupOf s.sylow_le_G₁ (s.marking.Li_le_Gi 1)).mp
      ⟨s.marking.Li_le_Gi 1,s.Li_mem_local 1 (.inl rfl)⟩

/-- Solvability of all proper full-Sylow overgroups of the actual quotient forces equality. -/
theorem point_component_eq_of_solvable_sylow_overgroups {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hp : SolvableSylowOvergroups (K ⧸ pCore 2 K)) : s.marking.Li 1 = K := by
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  let a := subgroupOfEquivOfLe hK.1
  let e := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
    (T.subtype s.sylow_le_G₁) (s.point_local_in_normalizer).1 hK.2 (comap_mono hLK)
    (isSolvable_proper_sylow_overgroup_of_twoCore_quotient
      (isSolvable_proper_sylow_overgroup_of_equiv e hp))
  exact (map_subgroupOf_eq_of_le (s.marking.Li_le_Gi 1)).symm.trans
    ((congrArg (map H.subtype) he).trans (map_subgroupOf_eq_of_le hK.1))

/-- The Bender quotient families admit no strict point-component enlargement. -/
theorem point_component_eq_of_bender {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K)) : s.marking.Li 1 = K :=
  s.point_component_eq_of_solvable_sylow_overgroups hK hLK
    (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hm)

/-- The binary L₃(2) quotient forces equality of the original embedded subgroups. -/
theorem point_component_eq_of_binary_three {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) : s.marking.Li 1 = K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact s.point_component_eq_of_solvable_sylow_overgroups hK hLK
    (isSolvable_proper_sylow_overgroup_of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF))

/-- The original point-residual image retains its order-168 two-core quotient. -/
theorem point_residual_image_core_card :
    Nat.card (s.pointCoreImage (s.marking.Li 1) ⧸
      pCore 2 (s.pointCoreImage (s.marking.Li 1))) = 168 := by
  let H := s.marking.Gi 1
  let B := (s.marking.Li 1).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let a := subgroupOfEquivOfLe (s.marking.Li_le_Gi 1)
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (s.marking.LiCoreEquiv 1 (.inl rfl))
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  have hc : Nat.card (B.map q ⧸ pCore 2 (B.map q)) = 168 :=
    (Nat.card_congr (e.symm.trans b).toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  exact hc

/-- The actual point residual with the original Sylow still has its order-168 quotient. -/
theorem point_residual_join_core_card :
    Nat.card ((s.marking.Li 1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (s.marking.Li 1 ⊔ (T : Subgroup G) : Subgroup G)) = 168 := by
  let J := s.marking.Li 1 ⊔ (T : Subgroup G)
  have hJ : J ≤ L ⊔ (T : Subgroup G) := sup_le_sup (s.marking.Li_le_L 1) le_rfl
  let A := J.subgroupOf (L ⊔ (T : Subgroup G))
  let a : A ≃* J := subgroupOfEquivOfLe hJ
  have hk : IsPGroup 2 (s.actor.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact s.actor_ker_isPGroup.comap_subtype
  let b := (s.actor.subgroupMap A).pCoreQuotientEquiv (s.actor.subgroupMap_surjective A) hk
  let c : A.map s.actor ≃* Representation.SL5ExteriorSquare.parabolicResidualFlag 2 :=
    MulEquiv.subgroupCongr (s.actor_image_local_join 1 (.inl rfl))
  let e := ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans b).trans
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
      Representation.SL5ExteriorSquare.parabolicTwoResidualFlagQuotientEquiv)
  exact (Nat.card_congr e.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card

private theorem point_residual_image_seven_dvd :
    7 ∣ Nat.card (s.pointCoreImage (s.marking.Li 1)) := by
  exact (show 7 ∣ Nat.card (s.pointCoreImage (s.marking.Li 1) ⧸
      pCore 2 (s.pointCoreImage (s.marking.Li 1))) by
        rw [s.point_residual_image_core_card]; decide).trans
    (pCore 2 (s.pointCoreImage (s.marking.Li 1))).card_quotient_dvd_card

private theorem point_component_eq_of_image_eq {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (he : s.pointCoreImage (s.marking.Li 1) = s.pointCoreImage K) : s.marking.Li 1 = K := by
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : q.ker ≤ (T.subtype s.sylow_le_G₁ : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal _
  have hh := local_cComponent_eq_of_map_eq (s.point_local_in_normalizer).1 hK.2
    (comap_mono hLK) q hk he
  exact (map_subgroupOf_eq_of_le (s.marking.Li_le_Gi 1)).symm.trans
    ((congrArg (map H.subtype) hh).trans (map_subgroupOf_eq_of_le hK.1))

/-- A proper odd-prime PSL₂ enlargement would make the original seven-section an A₅. -/
theorem point_component_eq_of_prime_linear {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) : s.marking.Li 1 = K := by
  let H := s.marking.Gi 1
  let B := (s.marking.Li 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let a := subgroupOfEquivOfLe hK.1
  let e : (K ⧸ pCore 2 K) ≃* C.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.2)
  have hB : B.map q ∈ ChapterA.Section03.localCComponents
      ((T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents (s.point_local_in_normalizer)
  by_cases he : B.map q = C.map q
  · exact s.point_component_eq_of_image_eq hK hLK he
  obtain ⟨_,⟨b⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
    _ hB (hK.2.map_quotient _) (map_mono (comap_mono hLK)) he hp ho (hm.of_mulEquiv e.symm)
  have h7 := s.point_residual_image_seven_dvd
  change 7 ∣ Nat.card (B.map q) at h7
  rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup] at h7
  norm_num [Nat.factorial] at h7

/-- The even SU₃ covering models also force equality through their actual quotient images. -/
theorem point_component_eq_of_binary_unitary_three {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) {n : ℕ} (hn : 0 < n)
    (hm : Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    s.marking.Li 1 = K := by
  let H := s.marking.Gi 1
  let B := (s.marking.Li 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let a := subgroupOfEquivOfLe hK.1
  let e : C.map q ≃* (K ⧸ pCore 2 K) :=
    (cComponentTwoCoreQuotientEquiv hK.2).symm.trans
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  have hB : B.map q ∈ ChapterA.Section03.localCComponents
      ((T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents (s.point_local_in_normalizer)
  obtain ⟨F,_,_,J,hF,hc,⟨b⟩⟩ := hm
  apply s.point_component_eq_of_image_eq hK hLK
  exact ChapterA.Section03.SourceEmbeddings.eq_of_binary_su3_containing_component
    _ hB (hK.2.map_quotient _) (map_mono (comap_mono hLK)) hn
    ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.trans b⟩⟩

/-- A strict quadratic-field point component is necessarily the source L₂(49) row. -/
theorem point_component_eq_or_quadratic_seven {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2)) :
    s.marking.Li 1 = K ∨ p = 7 := by
  let H := s.marking.Gi 1
  let B := (s.marking.Li 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let a := subgroupOfEquivOfLe hK.1
  let e : (K ⧸ pCore 2 K) ≃* C.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.2)
  have hB : B.map q ∈ ChapterA.Section03.localCComponents
      ((T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents (s.point_local_in_normalizer)
  by_cases he : B.map q = C.map q
  · exact .inl (s.point_component_eq_of_image_eq hK hLK he)
  obtain ⟨hgt,F,_,_,hF,⟨b⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_models
    _ hB (hK.2.map_quotient _) (map_mono (comap_mono hLK)) he hp ho (hm.of_mulEquiv e.symm)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (B.map q) := b.isSimpleGroup
  have hc : Nat.card (B.map q ⧸ pCore 2 (B.map q)) = 168 :=
    s.point_residual_image_core_card
  have hcore : pCore 2 (B.map q) = ⊥ := by
    rcases (inferInstance : (pCore 2 (B.map q)).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · rw [he] at hc
      simp at hc
  have hcard : Nat.card (B.map q) = 168 := by
    rwa [hcore,Nat.card_congr (QuotientGroup.quotientBot (G := B.map q)).toEquiv] at hc
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF ▸ ho)
  rw [←Nat.card_congr b.toEquiv,hcard,hF] at horder
  have hd : p ∣ 2 ^ 4 * 3 * 7 := by
    change p ∣ 336
    exact ⟨p ^ 2 - 1,horder⟩
  right
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · have hd' := hp.dvd_of_dvd_pow hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd' with he | he <;> omega
    · rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he <;> omega
  · rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with he | he <;> omega

/-- The quadratic exceptional point quotient is excluded by the original Sylow action. -/
theorem point_component_not_linear_fortyNine {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) : ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 49 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let J := s.marking.Li 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  have hBA : s.marking.Li 1 ≤ A := le_inf le_sup_left hLK
  let B := (s.marking.Li 1).subgroupOf A
  let ψ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkψ : IsPGroup 2 ψ.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let f := ψ.comp (inclusion (show A ≤ K from inf_le_right))
  have hkf : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker]
    exact hkψ.comap_of_injective _ (inclusion_injective _)
  have hnB : B.Normal := (normal_subgroupOf_iff_le_normalizer hBA).mpr
    (inf_le_left.trans ((sup_le (s.Li_le_Mi 1)
      (le_inf le_sup_right s.sylow_le_G₁)).trans (s.Mi_normalizes_Li 1)))
  let := hnB
  let a : B ≃* s.marking.Li 1 := subgroupOfEquivOfLe hBA
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
  have hne : B.map f ≠ ⊥ := by
    intro he
    have hBk : B ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    let : Group.IsNilpotent B := (hkf.to_le hBk).isNilpotent
    have hbns := Chapter1.mem_L_not_isSolvable (s.Li_mem_local 1 (.inl rfl))
    exact hbns (Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective)
  have hBD : B.map f ≤ f.range := map_le_range f B
  have heBD : (B.map f).subgroupOf f.range = B.map f.rangeRestrict := by
    have he : (B.map f.rangeRestrict).map f.range.subtype = B.map f := by
      rw [map_map]
      rfl
    rw [←he]
    exact comap_map_eq_self_of_injective f.range.subtype_injective _
  have hnD : ((B.map f).subgroupOf f.range).Normal :=
    heBD.symm ▸ (Normal.map hnB f.rangeRestrict f.rangeRestrict_surjective)
  have hcoreD : pCore 2 f.range = ⊥ :=
    Theory.PSL2.twoCore_eq_bot_of_normal_perfect (hF ▸ (by decide : Odd 49)) hne hBD hnD
  have hcoref : pCore 2 A ≤ f.ker := by
    have hh : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    rw [hcoreD] at hh
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
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  obtain ⟨S,hS⟩ := (T.subtype s.sylow_le_G₁).exists_subgroupOf_eq_of_subnormal C hK.2.subnormal
  let c : C ≃* K := subgroupOfEquivOfLe hK.1
  let P := (S.mapSurjective (f := c.toMonoidHom) c.surjective).mapSurjective hψ
  have hPD : (P : Subgroup PSL(2,F)) ≤ f.range := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    have hyT : (y : G) ∈ (T : Subgroup G) := by
      rw [hS] at hy
      exact hy
    have hyA : (y : G) ∈ A := ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hyT,y.property⟩
    exact ⟨⟨y,hyA⟩,rfl⟩
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF ▸ (by decide : Odd 49))
  rw [hF] at horder
  have hsize : Nat.card PSL(2,F) = 58800 := by omega
  have h16 : 16 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 4) (by rw [hsize]; decide)
  have hbad := (h16.trans (card_dvd_of_le hPD)).trans hcard
  norm_num at hbad

/-- Every odd-field degree-one or degree-two linear point model forces equality. -/
theorem point_component_eq_of_odd_linear {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ e)) : s.marking.Li 1 = K := by
  rcases he with rfl | rfl
  · exact s.point_component_eq_of_prime_linear hK hLK hp ho (by simpa using hm)
  · rcases s.point_component_eq_or_quadratic_seven hK hLK hp ho hm with he | he
    · exact he
    · subst p
      exact (s.point_component_not_linear_fortyNine hK hLK hm).elim

/-- All full-Sylow non-enlargement model rows retain the actual point residual. -/
theorem point_component_eq_of_non_enlarging_model {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∨
      (∃ p e : ℕ, p.Prime ∧ Odd p ∧ (e = 1 ∨ e = 2) ∧
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ e)) ∨
      (∃ n : ℕ, 0 < n ∧ Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ n))) :
    s.marking.Li 1 = K := by
  rcases hm with hm | hm | ⟨p,e,hp,ho,he,hm⟩ | ⟨n,hn,hm⟩
  · exact s.point_component_eq_of_bender hK hLK hm
  · exact s.point_component_eq_of_binary_three hK hLK hm
  · exact s.point_component_eq_of_odd_linear hK hLK hp ho he hm
  · exact s.point_component_eq_of_binary_unitary_three hK hLK hn hm

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
