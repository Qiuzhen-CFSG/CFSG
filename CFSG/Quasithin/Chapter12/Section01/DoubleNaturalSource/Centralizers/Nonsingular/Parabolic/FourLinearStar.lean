module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.AlternatingStarSource
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.SpecificGroups.SymmetricEight.ThreeSectionSylow

/-!
# Excluding the degree-four binary-four star component

The marked central cover K/O2(K) maps onto K* = A8. The actual local
point centralizer acts on that cover and hence on the eight-letter model.
Its kernel acts trivially on the point residual modulo its two-core,
so the full H.9 point action factors through the permutation image.

The source degree-four Sylow theorem supplies a full even Sylow in this
image. The perfect residual retains a factor seven and has no factor five,
forcing the image to be even. Every radical-free quotient of this Sylow
overgroup is perfect, contradicting its quotient Aut(L3(2)). The possible
central star kernel is retained throughout, and relative normality is
only required inside C_G(w).

`FourLinearStarSource` applies the exclusion to the actual centralizer and
closure assembly. Source: Aschbacher--Smith 12.1.1 and H.9.1(4), printed
pp.788--789 and390. The remaining parabolic and J4 obligations stay with
qt-d-double-natural-centralizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open PerfectCentralCovering BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Trivial action on the containing component modulo its two-core already
kills the full nonsingular point action. -/
theorem doubleNatural_adapted_coreAction_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
      ∀ hn : B.localPointCentralizer w ≤ normalizer (K : Set G),
      (((quotientAut (pCore 2 K)).comp K.normalizerMonoidHom).comp (inclusion hn)).ker ≤
        (S.localPointAction w).ker := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hRK hn m hm
  let R := B.pointResidual w
  let M := B.localPointCentralizer w
  let f := S.localPointAction w
  let a := K.normalizerMonoidHom.comp (inclusion hn)
  let π := QuotientGroup.mk' (pCore 2 K)
  let i := inclusion hRK
  have hcore : (pCore 2 K).comap i ≤ pCore 2 R :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective i (inclusion_injective hRK)⟩
  have hfc : f m ∈ centralizer (pResidual 2 (S.setup.stabilizer (Additive.ofMul w)) : Set _) := by
    intro j hj
    rw [←S.residual_localPointAction w hw.nonsingular] at hj
    obtain ⟨r,hr,rfl⟩ := hj
    let rR : R := ⟨r,hr⟩
    let r' : R := ⟨(m : G) * r * (m : G)⁻¹ / r, R.div_mem
      ((mem_normalizer_iff.mp (B.localPointCentralizer_normalizes_residual w m.property) r).mp hr) hr⟩
    have hc : i r' ∈ pCore 2 K := by
      change a m (i rR) / i rR ∈ pCore 2 K
      apply (QuotientGroup.eq_iff_div_mem).mp
      have hh := congrArg (fun u : MulAut (K ⧸ pCore 2 K) => u (π (i rR))) hm
      change quotientAut (pCore 2 K) (a m) (π (i rR)) = π (i rR) at hh
      rw [quotientAut_apply_mk] at hh
      exact hh
    have hr' : r' ∈ (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))).ker := by
      rw [(S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).1]
      exact hcore hc
    have he : f (m*r*m⁻¹/r) = 1 := by
      apply Subtype.ext
      exact hr'
    rw [map_div,map_mul,map_mul,map_inv,div_eq_one,mul_inv_eq_iff_eq_mul] at he
    exact he.symm
  rw [S.nonsingular_stabilizer_residual_centralizer_eq_bot w hw.nonsingular] at hfc
  exact hfc



/-- The original full point action excludes the degree-four L4(2) star row. -/
theorem doubleNatural_four_adapted_C27_not_linearFour
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ¬ Nonempty (starImage K Q K ≃* SL(4,ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi ⟨e₀⟩
  let M := B.localPointCentralizer w
  let R := B.pointResidual w
  let J := S.setup.stabilizer (Additive.ofMul w)
  let E := alternatingGroup (Fin 8)
  let e := e₀.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  have hMN : M ≤ normalizer (K : Set G) := inf_le_right.trans
    ((normal_subgroupOf_iff_le_normalizer hi.component.1).mp hKn)
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  let : IsQuasisimple (K ⧸ pCore 2 K) := hi.quasisimple
  let c : Cover (K ⧸ pCore 2 K) E := {
    toMonoidHom := e.toMonoidHom.comp (coreToStar hi.normalizes)
    surjective := e.surjective.comp (coreToStar_surjective hi.normalizes)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact coreToStar_ker_central_from_source hi }
  have hc : c.toMonoidHom.ker = center (K ⧸ pCore 2 K) := by
    have hh := c.comap_center
    rw [alternatingGroup.center_eq_bot (by simp),MonoidHom.comap_bot] at hh
    exact hh
  let a := (quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hMN))
  let t := (c.autMap hc).comp a
  let s : Equiv.Perm (Fin 8) ≃* MulAut E := MulEquiv.ofBijective _
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  let r := s.symm.toMonoidHom.comp t
  let q := e.toMonoidHom.comp (toStarImage K Q)
  have hr (k : K) (hk : (k : G) ∈ M) : r ⟨k,hk⟩ = (q k : Equiv.Perm (Fin 8)) := by
    apply s.injective
    change s (s.symm (c.autMap hc (a ⟨k,hk⟩))) = MulAut.conjNormal (q k : Equiv.Perm (Fin 8))
    rw [s.apply_symm_apply,MulAut.conjNormal_val]
    apply MulEquiv.ext
    intro y
    obtain ⟨z,rfl⟩ := c.surjective y
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    rw [c.autMap_apply]
    change c.toMonoidHom (quotientAut (pCore 2 K)
      (K.normalizerMonoidHom (inclusion hMN ⟨k,hk⟩))
      (QuotientGroup.mk' (pCore 2 K) j)) = _
    rw [quotientAut_apply_mk,MulAut.conj_apply]
    have he : K.normalizerMonoidHom (inclusion hMN ⟨k,hk⟩) j = k*j*k⁻¹ := by
      apply Subtype.ext
      exact normalizerMonoidHom_apply_apply_coe K _ j
    rw [he]
    simp only [map_mul,map_inv]
    rfl
  let f := S.localPointAction w
  have hker : r.ker ≤ f.ker := by
    apply le_trans _ (D.doubleNatural_adapted_coreAction_kernel h B S w hw K hRK hMN)
    intro m hm
    apply (c.autMap_injective hc)
    apply s.symm.injective
    change r m = s.symm (c.autMap hc 1)
    simpa only [map_one] using (show r m = 1 from hm)
  let f' : r.range →* J := r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective
    ⟨f,by simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have hf' : Function.Surjective f' := by
    intro j
    obtain ⟨m,rfl⟩ := S.localPointAction_surjective w j
    exact ⟨r.rangeRestrict m,r.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ m⟩
  obtain ⟨P,hP⟩ := D.doubleNatural_four_adapted_C27_star_sylow h B S w hw K hKn hi
  have hPN : ((P.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 E) : Subgroup E).map E.subtype ≤ r.range := by
    rintro _ ⟨_,⟨k,hk,rfl⟩,rfl⟩
    obtain ⟨x,hx,he⟩ := hP hk
    let k' : K := ⟨x,hx.2⟩
    have hkk : toStarImage K Q k' = k := Subtype.ext he
    refine ⟨⟨x,hx.1⟩,?_⟩
    rw [hr k' hx.1]
    change (e (toStarImage K Q k') : Equiv.Perm (Fin 8)) = _
    rw [hkk]
    rfl
  let g := r.comp (inclusion hRM)
  let A := g.range
  let := (S.nonsingular_residual_local_cComponent w hw.nonsingular).perfect
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRM).toMonoidHom) (subgroupOfEquivOfLe hRM).surjective
  let : Group.IsPerfect A := Group.IsPerfect.range g
  have hNA : r.range ≤ normalizer (A : Set _) := by
    have hA : A = (R.subgroupOf M).map r := by
      ext x
      constructor
      · rintro ⟨z,rfl⟩
        exact ⟨inclusion hRM z,z.property,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨z,hz⟩,rfl⟩
    rw [hA]
    rintro _ ⟨m,rfl⟩
    apply (R.subgroupOf M).le_normalizer_map r
    exact mem_map_of_mem r (show m ∈ normalizer (R.subgroupOf M : Set M) from
      fun z => B.localPointCentralizer_normalizes_residual w m.property z)
  let j := (toStarImage K Q).comp (inclusion hRK)
  let : Group.IsSolvable j.ker := six_star_map_ker_solvable hi hRK
  have hgk : g.ker = j.ker := by
    ext x
    change r (inclusion hRM x) = 1 ↔ j x = 1
    have hx := hr ⟨x,hRK x.property⟩ (hRM x.property)
    change r (inclusion hRM x) = (e (j x) : Equiv.Perm (Fin 8)) at hx
    rw [hx]
    constructor
    · intro hh
      exact e.injective ((Subtype.ext hh).trans (e.map_one).symm)
    · intro hh
      rw [hh,map_one]
      rfl
  let : Group.IsSolvable g.ker := hgk ▸ inferInstanceAs (Group.IsSolvable j.ker)
  obtain ⟨eR⟩ := (S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).2
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := eR.isSimpleGroup
  have hRc : Nat.card (R ⧸ pCore 2 R) = 168 := by
    rw [Nat.card_congr eR.toEquiv,Matrix.PSL3Two.card_PSL]
  have h5R : ¬ 5 ∣ Nat.card R := by
    obtain ⟨d,hd⟩ := (pCore_isPGroup (p := 2) (G := R)).exists_card_eq
    rw [←(pCore 2 R).card_mul_index,index_eq_card,hRc,hd]
    intro hh
    have hh := ((by decide : Nat.Coprime 5 2).pow_right d).dvd_of_dvd_mul_left hh
    norm_num at hh
  have h5 : ¬ 5 ∣ Nat.card A := fun hh => h5R (hh.trans (card_dvd_of_surjective g.rangeRestrict g.rangeRestrict_surjective))
  have h7 : 7 ∣ Nat.card A := by
    have hd : 7 ∣ Nat.card R := (by decide : 7 ∣ 168).trans
      (hRc ▸ card_quotient_dvd_card (pCore 2 R))
    obtain ⟨d,hdg⟩ := (pCore_isPGroup.to_le (PerfectCoreTwoExtension.solvable_ker_le_core g)).exists_card_eq
    rw [←g.ker.card_mul_index,index_ker,hdg] at hd
    exact ((by decide : Nat.Coprime 7 2).pow_right d).dvd_of_dvd_mul_left hd
  obtain ⟨eJ⟩ := (S.setup.nonsingular_structure
    (show S.setup.quadratic (Additive.ofMul w) = 1 by rw [S.quadratic_eq]; exact hw.nonsingular)).2.2.1
  change J ≃* MulAut Matrix.PSL3Two.PSL at eJ
  have hrad : solvableRadical J = ⊥ := by
    let eA := eJ.trans (MulAut.congr (projectiveEquivLinear (by decide : 0 < 3)))
    let := BinaryNaturalDual.ModelOrbits.AutomorphismModel.linear_simple (by decide : 3 ≤ 3)
    let : IsQuasisimple (LinearGroup 3) := IsQuasisimple.of_mulEquiv
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.innerEquiv (by decide : 0 < 3)).symm
      (hG := (BinaryNaturalDual.ModelOrbits.AutomorphismModel.inner_isComponent (by decide : 3 ≤ 3)).2)
    have hh := MulAut.radical_free_of_inner_le (linear_center_eq_bot (by decide : 0 < 3))
      (⊤ : Subgroup (MulAut (LinearGroup 3))) le_top
    have hAut : solvableRadical (MulAut (LinearGroup 3)) = ⊥ := by
      rw [←map_solvableRadical_equiv (topEquiv : (⊤ : Subgroup (MulAut (LinearGroup 3))) ≃* _),hh,Subgroup.map_bot]
    apply map_injective (f := eA.toMonoidHom) eA.injective
    rw [map_solvableRadical_equiv,hAut,Subgroup.map_bot]
  let : Group.IsPerfect J := Theory.SpecificGroups.SymmetricEight.ThreeSectionSylow.eight_sylow_three_section_image_perfect
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) r.range A hPN hNA h7 h5 f' hf' hrad
  let : Group.IsPerfect (MulAut Matrix.PSL3Two.PSL) :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  let I := MulAut.innerSubgroup Matrix.PSL3Two.PSL
  have hIc : Nat.card I = 168 := by
    let eI := MonoidHom.ofInjective (f := (MulAut.conj : Matrix.PSL3Two.PSL →* _))
      (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.Automorphisms.center_psl_eq_bot)
    rw [←Nat.card_congr eI.toEquiv,Matrix.PSL3Two.card_PSL]
  have hIi : I.index = 2 := by
    have hh := I.index_mul_card
    rw [hIc,Matrix.PSL3Two.Automorphisms.card_aut] at hh
    omega
  let : Group.IsPerfect (⊤ : Subgroup (MulAut Matrix.PSL3Two.PSL)) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv : (⊤ : Subgroup (MulAut Matrix.PSL3Two.PSL)) ≃* _).symm.toMonoidHom)
      topEquiv.symm.surjective
  have htop := top_unique (le_of_isPerfect_of_index_eq_two ⊤ I hIi)
  rw [htop,card_top,Matrix.PSL3Two.Automorphisms.card_aut] at hIc
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
