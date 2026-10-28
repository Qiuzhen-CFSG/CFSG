module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstTwentyFiveExclusion
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Signed ternary field-five exclusions at the first normalizer

The actual local A₅ section in PSL₃(5) or PSU₃(5) is the binary cover
SL₂(5). Its full Sylow normalizer fixes the central involution. The actual
involution centralizer lifts through a cubic central kernel to GL₂ or GU₂,
retaining the smaller subgroup and the full Sylow. Projectivizing this
rank-one group gives PGL₂(5). Its Sylow subgroup has order eight, while
A₅ has two-part four and trivial centralizer, forcing an outer actor.
Perfectness lifts innerness through the smaller central two-core quotient,
so the outer actor is detected on the original A₅ section. Solvable-kernel
transport also treats the special linear and special unitary coverings.

The ambient two-core map and restriction to N_G(V₁) lift this actor to
T intersect K. The containing component centralizes the entire V₁,
including C_V(L). The proved natural point-fixer theorem makes that
actor inner on the literal L₁/O₂(L₁), giving the contradiction. The actual
Cartan consumer retains just SL₃(4), PSL₃(4), and J₁ as exceptional models.

The rank-one marking, pointwise action, and Cartan facts are preceding
inputs from qt-d-1222-natural-flag-cartan, with ultimate discharge in
qt-d-1222-natural-local-geometry. The exhaustive embedding list, remaining
sieve, field-four triangle, second-component equality, and source-family
assembly remain owned by qt-d-1222-natural-relative-components.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
proof of 11.1.2, printed pp.761--762, using A.3.12(9), A.3.14 and A.3.21(a).
The imported concrete model calculations retain their source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Ternary
open ChapterA.Section03.SourceEmbeddings

private theorem inner_transport {A B : Type*} [Group A] [Group B]
    (q : A →* B) (hq : Function.Surjective q)
    (a : MulAut A) (b : MulAut B) (he : ∀ x, q (a x) = b (q x))
    (hi : (quotientAut (pCore 2 A)) a ∈ MulAut.innerSubgroup (A ⧸ pCore 2 A)) :
    (quotientAut (pCore 2 B)) b ∈ MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  have hc : pCore 2 A ≤ (pCore 2 B).comap q := by
    rw [← map_le_iff_le_comap]
    exact le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map q hq,pCore_isPGroup.map q⟩
  let d := QuotientGroup.map (pCore 2 A) (pCore 2 B) q hc
  obtain ⟨z,hz⟩ := hi
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) z
  refine ⟨QuotientGroup.mk' (pCore 2 B) (q z),?_⟩
  ext y
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) y
  obtain ⟨x,rfl⟩ := hq y
  have hh := congrArg d (DFunLike.congr_fun hz (QuotientGroup.mk' (pCore 2 A) x))
  simp only [quotientAut_apply_mk,MulAut.conj_apply,map_mul,map_inv,
    d,QuotientGroup.map_mk',he] at hh
  rw [quotientAut_apply_mk,MulAut.conj_apply]
  simpa only [QuotientGroup.mk'_apply] using hh

private theorem inner_of_core_inner {A : Type*} [Group A] [Finite A]
    [IsQuasisimple A] (a : MulAut A)
    (hi : quotientAut (pCore 2 A) a ∈ MulAut.innerSubgroup (A ⧸ pCore 2 A)) :
    a ∈ MulAut.innerSubgroup A := by
  obtain ⟨z,hz⟩ := hi
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) z
  refine ⟨z,?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq (QuotientGroup.mk' (pCore 2 A))
    (by rw [QuotientGroup.ker_mk']; exact IsQuasisimple.pCore_le_center 2)
  ext x
  change QuotientGroup.mk' (pCore 2 A) (z*x*z⁻¹) = QuotientGroup.mk' (pCore 2 A) (a x)
  simpa only [MulAut.conj_apply,quotientAut_apply_mk,map_mul,map_inv] using
    DFunLike.congr_fun hz (QuotientGroup.mk' (pCore 2 A) x)

private def InnerAction {G : Type*} [Group G] (P B : Subgroup G) : Prop :=
  ∀ t : P, ∃ b : B, ∀ x : B,
    (t:G) * x * (t:G)⁻¹ = (b:G) * x * (b:G)⁻¹

private theorem inner_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) {P B : Subgroup G} (hi : InnerAction P B) :
    InnerAction (P.map f) (B.map f) := by
  rintro ⟨t,s,hs,rfl⟩
  obtain ⟨b,hb⟩ := hi ⟨s,hs⟩
  refine ⟨⟨f b,mem_map_of_mem f b.property⟩,?_⟩
  rintro ⟨x,y,hy,rfl⟩
  simpa only [map_mul,map_inv] using congrArg f (hb ⟨y,hy⟩)

private theorem inner_lift {G H : Type*} [Group G] [Group H]
    (f : G →* H) {P B : Subgroup G} {Q C : Subgroup H}
    (hP : P.map f ≤ Q) (hn : P ≤ normalizer (B : Set G))
    (e : B ≃* C) (he : ∀ b : B, f b = e b)
    (hi : InnerAction Q C) : InnerAction P B := by
  intro t
  obtain ⟨c,hc⟩ := hi ⟨f t,hP (mem_map_of_mem f t.property)⟩
  refine ⟨e.symm c,?_⟩
  intro x
  have ht := hn t.property
  have hh := hc (e x)
  have heq : e (B.normalizerMonoidHom ⟨t,ht⟩ x) = c * e x * c⁻¹ := by
    apply Subtype.ext
    rw [←he]
    change f ((t:G)*x*(t:G)⁻¹) = (c:H) * e x * (c:H)⁻¹
    simpa only [map_mul,map_inv,he] using hh
  have hx : B.normalizerMonoidHom ⟨t,ht⟩ x = e.symm c*x*(e.symm c)⁻¹ := by
    apply e.injective
    rw [map_mul,map_mul,map_inv,e.apply_symm_apply]
    exact heq
  exact congrArg Subtype.val hx

private def center_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

private theorem five_cover_center {A : Type*} [Group A]
    (hm : Chapter1.Section02.LocalModels.IsSL A 2 5) :
    Nonempty (A ⧸ center A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  obtain ⟨e5⟩ := ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨(center_equiv (e.trans (GorensteinWalter.sl2RingEquiv a))).trans e5⟩

private theorem sl2_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hm : Chapter1.Section02.LocalModels.IsSL B 2 5) :
    Chapter1.Section02.LocalModels.IsSL A 2 5 := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩

private theorem sylow_not_inner_pgl_five {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) (P : Sylow 2 (ProjGenLinGroup (Fin 2) F))
    (A : Subgroup (ProjGenLinGroup (Fin 2) F))
    (e : A ≃* alternatingGroup (Fin 5))
    (hi : InnerAction P A) : False := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hAc : Nat.card A = 60 := by rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num
  have hA : A ≠ ⊥ := by intro h; simp [h] at hAc
  have hc := Theory.PGL2.centralizer_eq_bot_of_perfect A hA
  have hPA : (P : Subgroup _) ≤ A := by
    intro t ht
    obtain ⟨b,hb⟩ := hi ⟨t,ht⟩
    have hz : b.val⁻¹*t ∈ centralizer (A : Set _) := by
      intro x hx
      have he := (hb ⟨x,hx⟩).symm
      have hh : (b.val⁻¹*t)*x*(b.val⁻¹*t)⁻¹=x := by
        calc
          _ = b.val⁻¹*(t*x*t⁻¹)*b.val := by group
          _ = x := by rw [←he]; group
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have he : b.val=t := inv_mul_eq_one.mp (hc.le hz)
    exact he ▸ b.property
  have hcard : Nat.card (ProjGenLinGroup (Fin 2) F) = 120 := by
    rw [GorensteinWalter.pgl2_card_formula,hF]
    norm_num
  have hd := (P.pow_dvd_card_of_pow_dvd_card (n:=3) (by rw [hcard]; decide)).trans
    (card_dvd_of_le hPA)
  norm_num [hAc] at hd

private theorem gl2_not_inner {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) (P : Sylow 2 (GL (Fin 2) F))
    (A : Subgroup (GL (Fin 2) F)) [Group.IsPerfect A]
    (hm : Chapter1.Section02.LocalModels.IsSL A 2 5)
    (hi : InnerAction P A) : False := by
  obtain ⟨a⟩ := five_cover_center hm
  let : Nontrivial (A ⧸ center A) := a.nontrivial
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  obtain ⟨d⟩ := GeneralLinearGroup.projective_image_equiv_quotient_center A
    (Group.IsPerfect.not_isMulCommutative A)
  exact sylow_not_inner_pgl_five hF
    (P.mapSurjective ProjGenLinGroup.mk_surjective) (A.map ProjGenLinGroup.mk)
    (d.trans a) (inner_map ProjGenLinGroup.mk hi)

private theorem gu2_not_inner (P : Sylow 2 (ABG.GU2 5 1 one_ne_zero))
    (A : Subgroup (ABG.GU2 5 1 one_ne_zero)) [Group.IsPerfect A]
    (hm : Chapter1.Section02.LocalModels.IsSL A 2 5)
    (hi : InnerAction P A) : False := by
  obtain ⟨a⟩ := five_cover_center hm
  let : Nontrivial (A ⧸ center A) := a.nontrivial
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  have hA := Group.IsPerfect.not_isMulCommutative A
  obtain ⟨f,hf,hk⟩ := ABG.GU2_prime_projective_quotient 5 (by decide) (by decide)
  let b := f.comp A.subtype
  have hbker : b.ker = center A := by
    ext x
    change f x.val=1 ↔ _
    rw [← MonoidHom.mem_ker,hk,← ABG.GU2_centralizer_eq_scalar 5 1 one_ne_zero A hA]
    rw [mem_centralizer_iff,mem_center_iff]
    constructor
    · intro h y
      exact Subtype.ext (h y y.property)
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y,hy⟩)
  have hbrange : b.range=A.map f := by rw [MonoidHom.range_comp,A.range_subtype]
  let d : A.map f ≃* A ⧸ center A :=
    ((MulEquiv.subgroupCongr hbrange.symm).trans
      (QuotientGroup.quotientKerEquivRange b).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hbker)
  exact sylow_not_inner_pgl_five (by simpa using GaloisField.card 5 1 one_ne_zero)
    (P.mapSurjective hf) (A.map f) (d.trans a) (inner_map f hi)

private theorem noncommutative_cover {A H : Type*} [Group A] [Group H]
    (f : A →* H) (hf : Function.Surjective f) (B : Subgroup H)
    [IsQuasisimple B] : ¬ IsMulCommutative A := by
  intro ha
  have hh : IsMulCommutative H := IsMulCommutative.of_comm (fun x y => by
    obtain ⟨x,rfl⟩ := hf x
    obtain ⟨y,rfl⟩ := hf y
    rw [←map_mul,←map_mul,ha.is_comm.comm x y])
  have hb : IsMulCommutative B := IsMulCommutative.of_comm (fun x y =>
    Subtype.ext (hh.is_comm.comm x y))
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  exact Group.IsPerfect.not_isMulCommutative B hb

private theorem inner_restrict {G : Type*} [Group G] {P B C : Subgroup G}
    (hBC : B ≤ C) (hi : InnerAction P B) :
    InnerAction (P.subgroupOf C) (B.subgroupOf C) := by
  intro t
  obtain ⟨b,hb⟩ := hi ⟨t.val,t.property⟩
  refine ⟨⟨⟨b,hBC b.property⟩,b.property⟩,?_⟩
  intro x
  exact Subtype.ext (hb ⟨x.val,x.property⟩)

open ChapterC.Section05.NormalizerControl.EmbeddingSelection
private theorem linear_not_inner {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) (P : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    [IsQuasisimple B] (hm : Chapter1.Section02.LocalModels.IsSL B 2 5)
    (hn : (P : Subgroup PSL(3,F)) ≤ normalizer (B : Set PSL(3,F)))
    (hi : InnerAction P B) : False := by
  obtain ⟨z,_,hz,hC⟩ := sl2_five_full_sylow_in_centralizer P B hm hn
  let C := centralizer ({z} : Set PSL(3,F))
  have hPC : (P : Subgroup _) ≤ C := le_sup_right.trans hC
  have hBC : B ≤ C := le_sup_left.trans hC
  let Q := P.subtype hPC
  let D := B.subgroupOf C
  let d : D ≃* B := subgroupOfEquivOfLe hBC
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv d.symm
  have hQD : (Q : Subgroup C) ≤ normalizer (D : Set C) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hBC]
    exact subgroupOf_mono C hn
  have h2 : (2:F)≠0 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
    (by decide : Odd 5) (k:=1) (by simpa using hF)
  obtain ⟨f,hf,hk,h3⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection z hz h2
  obtain ⟨R,A,e,hR,_,hRA,he⟩ :=
    Theory.SpecificGroups.OddThreeLevi.exists_perfect_sylow_normalized_lift
      (MonoidHom.id _) Function.injective_id (noncommutative_cover f hf D)
      f hf hk h3 Q D hQD
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  apply gl2_not_inner hF R A (sl2_transport (e.trans d) hm)
  apply inner_lift f (P:=R) (B:=A) (Q:=Q) (C:=D) ?_ hRA e he
    (inner_restrict hBC hi)
  change (R.mapSurjective hf : Subgroup C) ≤ (Q : Subgroup C)
  rw [hR]

private theorem unitary_not_inner {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (hF : Nat.card F = 5^2) (hc : ∀ x, J.conj x=x^5)
    (P : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (B : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    [IsQuasisimple B] (hm : Chapter1.Section02.LocalModels.IsSL B 2 5)
    (hn : (P : Subgroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      normalizer (B : Set (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)))
    (hi : InnerAction P B) : False := by
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨z,_,hz,hC⟩ := sl2_five_full_sylow_in_centralizer P B hm hn
  let C := centralizer ({z} : Set _)
  have hPC : (P : Subgroup _) ≤ C := le_sup_right.trans hC
  have hBC : B ≤ C := le_sup_left.trans hC
  let Q := P.subtype hPC
  let D := B.subgroupOf C
  let d : D ≃* B := subgroupOfEquivOfLe hBC
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv d.symm
  have hQD : (Q : Subgroup C) ≤ normalizer (D : Set C) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hBC]
    exact subgroupOf_mono C hn
  obtain ⟨f,hf,hk,h3⟩ := SU3.OddCubicCentralizer.surjection 5 (by decide) F J hF hc z hz
  let ρ := (ABG.unitaryForm 2 5 1 one_ne_zero).unitarySubgroup.subtype
  obtain ⟨R,A,e,hR,_,hRA,he⟩ :=
    Theory.SpecificGroups.OddThreeLevi.exists_perfect_sylow_normalized_lift
      ρ Subtype.val_injective (noncommutative_cover f hf D)
      f hf hk h3 Q D hQD
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  apply gu2_not_inner R A (sl2_transport (e.trans d) hm)
  apply inner_lift f (P:=R) (B:=A) (Q:=Q) (C:=D) ?_ hRA e he
    (inner_restrict hBC hi)
  change (R.mapSurjective hf : Subgroup C) ≤ (Q : Subgroup C)
  rw [hR]

/-- Both projective ternary field-five rows force an outer action on the
literal local A₅ quotient. -/
theorem projective_has_outer {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ ChapterA.Section03.localCComponents P)
    (hn : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSL G 3 5 ∨ ClassicalGroup.IsPSU G 3 5) :
    ∃ t : G, ∃ ht : t ∈ (P : Subgroup G),
      quotientAut (pCore 2 B) (B.normalizerMonoidHom ⟨t,hn ht⟩) ∉
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  obtain ⟨hB,hfive⟩ := odd_three_five_section_models P B hl hn eB (by decide) (by decide) hm
  let : IsQuasisimple B := hB
  by_contra h
  push Not at h
  have hi : InnerAction P B := by
    intro t
    obtain ⟨b,hb⟩ := inner_of_core_inner (B.normalizerMonoidHom ⟨t,hn t.property⟩)
      (h t t.property)
    refine ⟨b,fun x => ?_⟩
    exact (congrArg Subtype.val (DFunLike.congr_fun hb x)).symm
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
    let A := B.map e.toMonoidHom
    let a : A ≃* B := (B.equivMapOfInjective e.toMonoidHom e.injective).symm
    let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a.symm
    exact linear_not_inner hF Q A (sl2_transport a hfive)
      ((map_mono hn).trans (B.le_normalizer_map e.toMonoidHom)) (inner_map e.toMonoidHom hi)
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
    let A := B.map e.toMonoidHom
    let a : A ≃* B := (B.equivMapOfInjective e.toMonoidHom e.injective).symm
    let : IsQuasisimple A := IsQuasisimple.of_mulEquiv a.symm
    exact unitary_not_inner J hF hc Q A (sl2_transport a hfive)
      ((map_mono hn).trans (B.le_normalizer_map e.toMonoidHom)) (inner_map e.toMonoidHom hi)

private theorem surjective_has_outer {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (q : G →* H) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (P : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ ChapterA.Section03.localCComponents P)
    (hn : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSL H 3 5 ∨ ClassicalGroup.IsPSU H 3 5) :
    ∃ t : G, ∃ ht : t ∈ (P : Subgroup G),
      quotientAut (pCore 2 B) (B.normalizerMonoidHom ⟨t,hn ht⟩) ∉
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  let A := B.map q
  let R := P.mapSurjective hq
  have hRA : (R : Subgroup H) ≤ normalizer (A : Set H) :=
    (map_mono hn).trans (B.le_normalizer_map q)
  obtain ⟨eA⟩ := FiveLocalFF.SolvableQuotients.section_map q B hl eB
  obtain ⟨t,ht,ho⟩ := projective_has_outer R A
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q) hRA eA hm
  obtain ⟨s,hs,rfl⟩ := ht
  refine ⟨s,hs,?_⟩
  intro hi
  apply ho
  apply inner_transport (q.subgroupMap B) (q.subgroupMap_surjective B) _ _ _ hi
  intro x
  apply Subtype.ext
  change q (s*x*s⁻¹)=q s*q x*(q s)⁻¹
  simp only [map_mul,map_inv]

private theorem kernel_central_comp {G A H : Type*} [Group G] [Group A] [Group H]
    (e : G ≃* A) (q : A →* H) (hk : q.ker ≤ center A) :
    (q.comp e.toMonoidHom).ker ≤ center G := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul,MulEquiv.coe_toMonoidHom] using mem_center_iff.mp (hk hx) (e y)

/-- Both signs and both special/projective coverings of the field-five
ternary row have a noninner Sylow actor on the original A₅ section. -/
theorem signed_has_outer {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ ChapterA.Section03.localCComponents P)
    (hn : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (u : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign G u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign G u 3 5) :
    ∃ t : G, ∃ ht : t ∈ (P : Subgroup G),
      quotientAut (pCore 2 B) (B.normalizerMonoidHom ⟨t,hn ht⟩) ∉
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  rcases hm with hm | hm
  · apply projective_has_outer P B hl hn eB
    cases u with
    | false => exact .inl hm
    | true => exact .inr hm
  · cases u with
    | false =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let q := (PSL3.projection F).comp e.toMonoidHom
      have hq := (PSL3.projection_surjective F).comp e.surjective
      have hk : q.ker ≤ center G := kernel_central_comp e (PSL3.projection F)
        (by rw [PSL3.projection_ker])
      let : Group.IsSolvable q.ker := Group.isSolvable_of_comm (fun x y =>
        Subtype.ext ((mem_center_iff.mp (hk x.property) y).symm))
      exact surjective_has_outer q hq P B hl hn eB
        (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
    | true =>
      obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
      let q := J.specialToProjective.comp e.toMonoidHom
      have hq := J.specialToProjective_surjective.comp e.surjective
      have hk : q.ker ≤ center G := kernel_central_comp e J.specialToProjective
        J.specialToProjective_ker_le_center
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective q hq
      let : Group.IsSolvable q.ker := Group.isSolvable_of_comm (fun x y =>
        Subtype.ext ((mem_center_iff.mp (hk x.property) y).symm))
      exact surjective_has_outer q hq P B hl hn eB
        (.inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)

variable {G : Type*} [Group G] [Finite G]
private theorem signed_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (u : Bool)
    (h : Chapter1.Section02.LocalModels.IsPSLSign B u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign B u 3 5) :
    Chapter1.Section02.LocalModels.IsPSLSign A u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign A u 3 5 := by
  cases u with
  | false =>
    rcases h with h | h
    · exact .inl (h.of_mulEquiv e)
    · obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
      exact .inr ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩
  | true =>
    rcases h with h | h
    · obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := h
      exact .inl ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.trans a⟩⟩
    · obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := h
      exact .inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.trans a⟩⟩

/-- The signed ternary model supplies a noninner actor in the original
Sylow intersection with the containing C-component. -/
theorem containing_has_outer_sylow
    (P : Sylow 2 G) (B K : Subgroup G) (hK : K.IsCComponent)
    (hB : B ∈ ChapterA.Section03.localCComponents P)
    (hBK : B < K) (hPB : (P : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (u : Bool)
    (hm : Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) :
    ∃ t : G, ∃ ht : t ∈ (P : Subgroup G), t ∈ K ∧
      (quotientAut (pCore 2 B)) (B.normalizerMonoidHom ⟨t,hPB ht⟩) ∉
        MulAut.innerSubgroup (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let C := K.map q
  let A := B.map q
  have hAC : A ≤ C := map_mono hBK.le
  let E := A.subgroupOf C
  let eC : C ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm
  have hmC := signed_transport eC u hm
  obtain ⟨S,hS,hl,hn,_,⟨eE⟩⟩ :=
    proper_five_section_in_containing_image P B K hK hB hBK hPB eB
  obtain ⟨s,hs,hout⟩ := signed_has_outer S E hl hn eE u hmC
  obtain ⟨t,htK,hts⟩ := s.property
  change q t = s.val at hts
  have htP : t ∈ (P : Subgroup G) := by
    have hh : q t ∈ (P : Subgroup G).map q := by
      rw [hts]
      change s ∈ ((P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) :
        Subgroup (G ⧸ pCore 2 G)).subgroupOf C
      rwa [← hS]
    change t ∈ ((P : Subgroup G).map q).comap q at hh
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
      (pCore_isPGroup.le_sylow_of_normal P)] at hh
    exact hh
  refine ⟨t,htP,htK,?_⟩
  intro hi
  apply hout
  let d : E ≃* A := subgroupOfEquivOfLe hAC
  let r : B →* E := d.symm.toMonoidHom.comp (q.subgroupMap B)
  have hr : Function.Surjective r := d.symm.surjective.comp (q.subgroupMap_surjective B)
  apply inner_transport r hr _ _ _ hi
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change q (t * x.val * t⁻¹) = s.val * q x.val * s.val⁻¹
  simp only [map_mul,map_inv,hts]


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Ternary

open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Restriction to the actual first normalizer retains the original
rank-one quotient action and lifts the model actor to T intersect K. -/
theorem first_ternary_outer_on_rankOne
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (u : Bool)
    (hk : Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) :
    ∃ t : G, ∃ ht : t ∈ (T : Subgroup G), t ∈ K ∧
      Closure.coreQuotientAction (f.Li 0) ⟨t,f.sylow_normalizes_Li 0 ht⟩ ∉
        MulAut.innerSubgroup (f.Li 0 ⧸ pCore 2 (f.Li 0)) := by
  have heB : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card F = 4 by simpa [hfour] using hF)
    exact ⟨e.trans a⟩
  obtain ⟨eB⟩ := heB
  let H := normalizer (f.Vi 0 : Set G)
  have hTH : (T : Subgroup G) ≤ H := f.invariant 0
  have hCH : K ≤ H := hK.1
  have hBH : f.Li 0 ≤ H := hLK.le.trans hCH
  let P := T.subtype hTH
  let B := (f.Li 0).subgroupOf H
  let C := K.subgroupOf H
  let b : B ≃* f.Li 0 := subgroupOfEquivOfLe hBH
  let k : C ≃* K := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  have hlocal : B ∈ ChapterA.Section03.localCComponents P := by
    have hh := (Chapter1.mem_LIn_iff_subgroupOf hTH hBH).mp
      ⟨hBH,flag_mem_local_of_model D S f 0 hm⟩
    exact hh.1
  have hBC : B < C := by
    refine lt_of_le_of_ne (comap_mono hLK.le) ?_
    intro he
    apply hLK.ne
    simpa only [B,C,map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hCH] using
      congrArg (map H.subtype) he
  have hPB : (P : Subgroup H) ≤ normalizer (B : Set H) := by
    intro t ht x
    exact f.sylow_normalizes_Li 0 ht x
  obtain ⟨t,ht,htC,hout⟩ := Ternary.containing_has_outer_sylow P B C hK.2
    hlocal hBC hPB (bq.trans eB) u (Ternary.signed_transport kq u hk)
  refine ⟨t.val,ht,htC,?_⟩
  intro hi
  apply hout
  apply Ternary.inner_transport b.symm.toMonoidHom b.symm.surjective _ _ _ hi
  intro x
  rfl

/-- The signed ternary field-five rows are impossible at the first normalizer. -/
theorem first_component_not_ternary
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G)) {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (u : Bool) :
    ¬ (Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
      Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) := by
  intro hk
  obtain ⟨t,ht,htK,hout⟩ := first_ternary_outer_on_rankOne D S f hm hfour hK hLK u hk
  have htc := subspace_containing_component_centralizes D S f (f.Vi 0) le_rfl
    hm hfix hK hLK.le htK
  exact hout (point_centralizing_sylow_inner_on_first D S f ⟨t,ht⟩ htc)

/-- In the literal Cartan consumer, the remaining exceptional rows are
SL₃(4), PSL₃(4), and J₁. The exhaustive embedding list remains explicit. -/
theorem first_refinement_or_linearFour_or_janko_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (S.field.degree = 2 ∧ (Source.IsSL (K ⧸ pCore 2 K) 3 4 ∨
        ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model))) := by
  by_cases he : f.Li 0 = K
  · exact .inl (.equal (by simpa using he))
  have hlt := lt_of_le_of_ne hLK he
  rcases first_refinement_or_ternary_or_janko_of_cartan D S f hu hm hfix hX hK hLK
    hXcard hfaith hk with h | ⟨hn,h⟩
  · exact .inl h
  · refine .inr ⟨hn,?_⟩
    rcases h with h | h | ⟨u,h⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact (first_component_not_ternary D S f hm hn hfix hK.1 hlt u h).elim
    · exact .inr (.inr h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
