module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.FourQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Theory.SpecificGroups.PSL2.NormalPerfectOvergroupCore
public import Theory.GroupTheory.CComponent.LocalImageEquality
/-!
# Rank-one point-component comparisons in degree four

The original L₁ remains a local C-component under the literal projection
G₁ → G₁/O₂(G₁). The Bender and binary unitary rows have solvable proper
Sylow overgroups and hence cannot enlarge it. For odd prime and quadratic
PSL₂ quotients, the actual restricted Sylow and order-168 smaller quotient
leave only the quadratic-seven possibility. The image of (L₁T) ∩ K₁ then
has trivial two-core and order dividing 168 but contains a Sylow subgroup
of L₂(49) whose order is divisible by sixteen, a contradiction.

FourNormal applies these equalities to construct the original degree-four
ComponentGeometry and abelian point span. Other component models and the
remaining source assembly stay with qt-d-1291-natural-source.
Source: Aschbacher--Smith 12.9.3, printed p.858. The quotient comparison
adapts the checked Section05 PointRankOne argument for 12.5.3, pp.817--818.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
  (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple) (F : InvariantFlag T V 4)
include h earlier
/-- Solvability of all proper full-Sylow overgroups of the actual quotient forces equality. -/
theorem four_point_component_eq_of_solvable_sylow_overgroups {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K)
    (hp : SolvableSylowOvergroups (K ⧸ pCore 2 K)) : F.Li L 1 = K := by
  let H := F.H
  let C := K.subgroupOf H
  let a := subgroupOfEquivOfLe hK.1
  let e := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
    (T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)) (four_point_local_in_normalizer h earlier F).1 hK.2 (comap_mono hLK)
    (isSolvable_proper_sylow_overgroup_of_twoCore_quotient (G := C)
      (isSolvable_proper_sylow_overgroup_of_equiv e hp))
  exact (map_subgroupOf_eq_of_le (((F.Li_le L 1).trans inf_le_right))).symm.trans
    ((congrArg (map H.subtype) he).trans (map_subgroupOf_eq_of_le hK.1))

/-- The Bender quotient families admit no strict point-component enlargement. -/
theorem four_point_component_eq_of_bender {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K)) : F.Li L 1 = K :=
  four_point_component_eq_of_solvable_sylow_overgroups h earlier F hK hLK
    (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hm)

/-- The binary L₃(2) quotient forces equality of the original embedded subgroups. -/
theorem four_point_component_eq_of_binary_three {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2) : F.Li L 1 = K := by
  obtain ⟨k,_,_,hF,⟨e⟩⟩ := hm
  exact four_point_component_eq_of_solvable_sylow_overgroups h earlier F hK hLK
    (isSolvable_proper_sylow_overgroup_of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF))

omit earlier in
private theorem four_point_residual_image_seven_dvd :
    7 ∣ Nat.card (((F.Li L 1).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))) := by
  exact (show 7 ∣ Nat.card (((F.Li L 1).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)) ⧸
      pCore 2 (((F.Li L 1).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)))) by
        rw [four_point_image_core_card h F]; decide).trans
    (pCore 2 (((F.Li L 1).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)))).card_quotient_dvd_card

private theorem four_point_component_eq_of_image_eq {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K)
    (he : ((F.Li L 1).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)) = (K.subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))) : F.Li L 1 = K := by
  let H := F.H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : q.ker ≤ ((T : Subgroup G).subgroupOf H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype (show (T : Subgroup G) ≤ H from F.invariant 1))
  have hh := local_cComponent_eq_of_map_eq (four_point_local_in_normalizer h earlier F).1 hK.2
    (comap_mono hLK) q hk he
  exact (map_subgroupOf_eq_of_le (((F.Li_le L 1).trans inf_le_right))).symm.trans
    ((congrArg (map H.subtype) hh).trans (map_subgroupOf_eq_of_le hK.1))

/-- A proper odd-prime PSL₂ enlargement would make the original seven-section an A₅. -/
theorem four_point_component_eq_of_prime_linear {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) : F.Li L 1 = K := by
  let H := F.H
  let B := (F.Li L 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let a := subgroupOfEquivOfLe hK.1
  let e : (K ⧸ pCore 2 K) ≃* C.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.2)
  have hB : B.map q ∈ ChapterA.Section03.localCComponents
      ((T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective, Sylow.coe_subtype] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents (four_point_local_in_normalizer h earlier F)
  by_cases he : B.map q = C.map q
  · exact four_point_component_eq_of_image_eq h earlier F hK hLK he
  obtain ⟨_,⟨b⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
    _ hB (hK.2.map_quotient _) (map_mono (comap_mono hLK)) he hp ho (hm.of_mulEquiv e.symm)
  have h7 := four_point_residual_image_seven_dvd h F
  change 7 ∣ Nat.card (B.map q) at h7
  rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup] at h7
  norm_num [Nat.factorial] at h7

/-- The even SU₃ covering models also force equality through their actual quotient images. -/
theorem four_point_component_eq_of_binary_unitary_three {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K) {n : ℕ} (hn : 0 < n)
    (hm : Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    F.Li L 1 = K := by
  let H := F.H
  let B := (F.Li L 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let a := subgroupOfEquivOfLe hK.1
  let e : C.map q ≃* (K ⧸ pCore 2 K) :=
    (cComponentTwoCoreQuotientEquiv hK.2).symm.trans
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  have hB : B.map q ∈ ChapterA.Section03.localCComponents
      ((T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective, Sylow.coe_subtype] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents (four_point_local_in_normalizer h earlier F)
  obtain ⟨k,_,_,J,hF,hc,⟨b⟩⟩ := hm
  apply four_point_component_eq_of_image_eq h earlier F hK hLK
  exact ChapterA.Section03.SourceEmbeddings.eq_of_binary_su3_containing_component
    _ hB (hK.2.map_quotient _) (map_mono (comap_mono hLK)) hn
    ⟨k,inferInstance,inferInstance,J,hF,hc,⟨e.trans b⟩⟩

/-- A strict quadratic-field point component is necessarily the source L₂(49) row. -/
theorem four_point_component_eq_or_quadratic_seven {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ 2)) :
    F.Li L 1 = K ∨ p = 7 := by
  let H := F.H
  let B := (F.Li L 1).subgroupOf H
  let C := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let a := subgroupOfEquivOfLe hK.1
  let e : (K ⧸ pCore 2 K) ≃* C.map q :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.2)
  have hB : B.map q ∈ ChapterA.Section03.localCComponents
      ((T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))) := by
    simpa only [Sylow.coe_mapSurjective, Sylow.coe_subtype] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents (four_point_local_in_normalizer h earlier F)
  by_cases he : B.map q = C.map q
  · exact .inl (four_point_component_eq_of_image_eq h earlier F hK hLK he)
  obtain ⟨hgt,k,_,_,hF,⟨b⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_models
    _ hB (hK.2.map_quotient _) (map_mono (comap_mono hLK)) he hp ho (hm.of_mulEquiv e.symm)
  let : IsSimpleGroup PSL(2,k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (B.map q) := b.isSimpleGroup
  have hc : Nat.card (B.map q ⧸ pCore 2 (B.map q)) = 168 :=
    four_point_image_core_card h F
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
theorem four_point_component_not_linear_fortyNine {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K) : ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 49 := by
  rintro ⟨k,_,_,hF,⟨e⟩⟩
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let A := J ⊓ K
  have hBA : F.Li L 1 ≤ A := le_inf le_sup_left hLK
  let B := (F.Li L 1).subgroupOf A
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
    (inf_le_left.trans (four_point_join_normalizes h earlier F))
  let := hnB
  let a : B ≃* F.Li L 1 := subgroupOfEquivOfLe hBA
  let : Group.IsPerfect (F.Li L 1) := four_point_residual_perfect h F
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
  have hne : B.map f ≠ ⊥ := by
    intro he
    have hBk : B ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    let : Group.IsNilpotent B := (hkf.to_le hBk).isNilpotent
    have hbns := Chapter1.mem_L_not_isSolvable (Li_mem_local h earlier F 1 (Or.inr ⟨rfl,Or.inl rfl⟩))
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
      (dvd_of_eq (four_point_residual_join_core_card h earlier F))
  let H := F.H
  let C := K.subgroupOf H
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)).exists_subgroupOf_eq_of_subnormal C hK.2.subnormal
  let c : C ≃* K := subgroupOfEquivOfLe hK.1
  let P := (S.mapSurjective (f := c.toMonoidHom) c.surjective).mapSurjective hψ
  have hPD : (P : Subgroup PSL(2,k)) ≤ f.range := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    have hyT : (y : G) ∈ (T : Subgroup G) := by
      rw [hS] at hy
      exact hy
    have hyA : (y : G) ∈ A := ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hyT,y.property⟩
    exact ⟨⟨y,hyA⟩,rfl⟩
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF ▸ (by decide : Odd 49))
  rw [hF] at horder
  have hsize : Nat.card PSL(2,k) = 58800 := by omega
  have h16 : 16 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 4) (by rw [hsize]; decide)
  have hbad := (h16.trans (card_dvd_of_le hPD)).trans hcard
  norm_num at hbad

/-- Every odd-field degree-one or degree-two linear point model forces equality. -/
theorem four_point_component_eq_of_odd_linear {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K) {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ e)) : F.Li L 1 = K := by
  rcases he with rfl | rfl
  · exact four_point_component_eq_of_prime_linear h earlier F hK hLK hp ho (by simpa using hm)
  · rcases four_point_component_eq_or_quadratic_seven h earlier F hK hLK hp ho hm with he | he
    · exact he
    · subst p
      exact (four_point_component_not_linear_fortyNine h earlier F hK hLK hm).elim

/-- All full-Sylow non-enlargement model rows retain the actual point residual. -/
theorem four_point_component_eq_of_non_enlarging_model {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (F.H))
    (hLK : F.Li L 1 ≤ K)
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∨
      (∃ p e : ℕ, p.Prime ∧ Odd p ∧ (e = 1 ∨ e = 2) ∧
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (p ^ e)) ∨
      (∃ n : ℕ, 0 < n ∧ Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 (2 ^ n))) :
    F.Li L 1 = K := by
  rcases hm with hm | hm | ⟨p,e,hp,ho,he,hm⟩ | ⟨n,hn,hm⟩
  · exact four_point_component_eq_of_bender h earlier F hK hLK hm
  · exact four_point_component_eq_of_binary_three h earlier F hK hLK hm
  · exact four_point_component_eq_of_odd_linear h earlier F hK hLK hp ho he hm
  · exact four_point_component_eq_of_binary_unitary_three h earlier F hK hLK hn hm


end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
