module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveEndpointStar
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ParabolicAutomorphisms
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourLinearStar

/-!
# Excluding the degree-five nonsingular star branch

The proved endpoint geometry makes the actual star intersection a line or
hyperplane parabolic in SL5(2). Every automorphism preserving it is inner.
The local point centralizer acts on the perfect central cover K/O2(K), so
its induced inner action preserves the literal intersection image. Rigidity
of the central cover and the original residual action show that this action's
kernel is contained in the kernel of the full H.9 nonsingular point action.

The geometric Sylow placement now makes Aut(L4(2)) a radical-free image of
a full-Sylow overgroup in SL5(2). Such an image is perfect, contradicting
its genuine inner subgroup of index two. The central star kernel is retained;
normality is only relative to the original C_G(w).

`FiveStarExclusionSource` applies this exclusion to the actual nonsingular
centralizers and degree-five zeroth closure. The degree-four fixed-space
argument and ordinary J4 exclusion retain their existing owner.
Source: Aschbacher--Smith 12.1.1, printed pp.788--789; H.9.1(4), p.390.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open PerfectCentralCovering BinaryLinear BinaryLinear.OuterCyclic
open BinaryLinear.FiveFlagGeometry BinaryNaturalDual.ModelOrbits.AutomorphismModel
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full original point action excludes every degree-five nonnormal star branch. -/
theorem doubleNatural_five_adapted_C27_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        False := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi
  let M := B.localPointCentralizer w
  let J := S.setup.stabilizer (Additive.ofMul w)
  obtain ⟨e₀⟩ := D.doubleNatural_five_adapted_C27_star_linearFive h B S w hw K hRK hi
  let e := e₀.trans (slEquivLinear 5)
  have hMN : M ≤ normalizer (K : Set G) := inf_le_right.trans
    ((normal_subgroupOf_iff_le_normalizer hi.component.1).mp hKn)
  let : IsQuasisimple (K ⧸ pCore 2 K) := hi.quasisimple
  let c : Cover (K ⧸ pCore 2 K) (LinearGroup 5) := {
    toMonoidHom := e.toMonoidHom.comp (coreToStar hi.normalizes)
    surjective := e.surjective.comp (coreToStar_surjective hi.normalizes)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact coreToStar_ker_central_from_source hi }
  have hc : c.toMonoidHom.ker = center (K ⧸ pCore 2 K) := by
    have hh := c.comap_center
    rw [linear_center_eq_bot (by decide : 0 < 5),MonoidHom.comap_bot] at hh
    exact hh
  let a := (quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hMN))
  let t := (c.autMap hc).comp a
  let q := e.toMonoidHom.comp (toStarImage K Q)
  have htq (m : M) (k : K) :
      t m (q k) = q (K.normalizerMonoidHom (inclusion hMN m) k) := by
    change c.autMap hc (a m) (c.toMonoidHom (QuotientGroup.mk' (pCore 2 K) k)) = _
    rw [c.autMap_apply]
    change c.toMonoidHom (quotientAut (pCore 2 K)
      (K.normalizerMonoidHom (inclusion hMN m)) (QuotientGroup.mk' (pCore 2 K) k)) = _
    rw [quotientAut_apply_mk]
    rfl
  let P := ((starM K Q M).subgroupOf (starImage K Q K)).map e.toMonoidHom
  have hP : P = (M.subgroupOf K).map q := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨z,hz,he⟩ := hy
      let k : K := ⟨z,hz.2⟩
      refine ⟨k,hz.1,?_⟩
      apply congrArg e
      exact Subtype.ext he
    · rintro ⟨k,hk,rfl⟩
      refine ⟨toStarImage K Q k,?_,rfl⟩
      exact ⟨⟨k,mem_sup_left k.property⟩,⟨hk,k.property⟩,rfl⟩
  have htP (m : M) : P.map (t m).toMonoidHom = P := by
    apply eq_of_le_of_card_ge ?_ (card_map_of_injective (t m).injective).symm.le
    rw [hP]
    rintro _ ⟨_,⟨k,hk,rfl⟩,rfl⟩
    refine ⟨K.normalizerMonoidHom (inclusion hMN m) k,?_,(htq m k).symm⟩
    change (m : G) * k * (m : G)⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem m.property hk) (M.inv_mem m.property)
  obtain ⟨b,i,_,hendpoint⟩ := D.doubleNatural_five_adapted_C27_endpoint h B S w hw K hRK hi e
  have hti (m : M) : t m ∈ MulAut.innerSubgroup (LinearGroup 5) := by
    apply singleton_flag_preserving_is_inner b i
    change P = flagStabilizer b {i} at hendpoint
    rw [←hendpoint]
    exact htP m
  let d : LinearGroup 5 ≃* MulAut.innerSubgroup (LinearGroup 5) :=
    MonoidHom.ofInjective (f := MulAut.conj)
      (MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot (by decide : 0 < 5)))
  let r : M →* LinearGroup 5 := d.symm.toMonoidHom.comp (t.codRestrict _ hti)
  have hr (k : K) (hk : (k : G) ∈ M) : r ⟨k,hk⟩ = q k := by
    apply MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot (by decide : 0 < 5))
    have hd (m : M) : MulAut.conj (r m) = t m := by
      change (d (d.symm ⟨t m,hti m⟩) : MulAut (LinearGroup 5)) = t m
      rw [d.apply_symm_apply]
    rw [hd]
    apply MulEquiv.ext
    intro x
    obtain ⟨j,rfl⟩ := (e.surjective.comp (toStarImage_surjective K Q)) x
    change t ⟨k,hk⟩ (q j) = MulAut.conj (q k) (q j)
    rw [htq,MulAut.conj_apply]
    change q (k*j*k⁻¹) = q k*q j*(q k)⁻¹
    simp only [map_mul,map_inv]
  let f := S.localPointAction w
  have hker : r.ker ≤ f.ker := by
    apply le_trans _ (D.doubleNatural_adapted_coreAction_kernel h B S w hw K hRK hMN)
    intro m hm
    have hb : c.autMap hc (a m) = 1 := by
      have hh := congrArg (fun x : LinearGroup 5 => (d x : MulAut (LinearGroup 5))) hm
      simpa only [r,t,MonoidHom.comp_apply,MonoidHom.codRestrict_apply,OneMemClass.coe_one,
        MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply,map_one] using hh
    exact c.autMap_injective hc (hb.trans (c.autMap hc).map_one.symm)
  let f' : r.range →* J := r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective
    ⟨f,by simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have hf' : Function.Surjective f' := by
    intro j
    obtain ⟨m,rfl⟩ := S.localPointAction_surjective w j
    exact ⟨r.rangeRestrict m,r.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ m⟩
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_five_adapted_C27_star_sylow h B S w hw K hRK hi
  have hPr : ((P₀.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 (LinearGroup 5)) :
      Subgroup (LinearGroup 5)) ≤ r.range := by
    rintro _ ⟨k,hk,rfl⟩
    obtain ⟨x,hx,he⟩ := hP₀ hk
    let k' : K := ⟨x,hx.2⟩
    have hkk : toStarImage K Q k' = k := Subtype.ext he
    refine ⟨⟨x,hx.1⟩,?_⟩
    rw [hr k' hx.1]
    change e (toStarImage K Q k') = _
    rw [hkk]
    rfl
  obtain ⟨eJ⟩ := (S.setup.nonsingular_structure
    (show S.setup.quadratic (Additive.ofMul w) = 1 by rw [S.quadratic_eq]; exact hw.nonsingular)).2.2.1
  change J ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) at eJ
  let eA := eJ.trans (MulAut.congr (projectiveEquivLinear (by decide : 0 < 4)))
  have hrad : solvableRadical J = ⊥ := by
    let := linear_simple (by decide : 3 ≤ 4)
    let : IsQuasisimple (LinearGroup 4) :=
      IsQuasisimple.of_mulEquiv (innerEquiv (by decide : 0 < 4)).symm
        (hG := (inner_isComponent (by decide : 3 ≤ 4)).2)
    have hh := MulAut.radical_free_of_inner_le (linear_center_eq_bot (by decide : 0 < 4))
      (⊤ : Subgroup (MulAut (LinearGroup 4))) le_top
    have hAut : solvableRadical (MulAut (LinearGroup 4)) = ⊥ := by
      rw [←map_solvableRadical_equiv (topEquiv : (⊤ : Subgroup (MulAut (LinearGroup 4))) ≃* _),hh,Subgroup.map_bot]
    apply map_injective (f := eA.toMonoidHom) eA.injective
    rw [map_solvableRadical_equiv,hAut,Subgroup.map_bot]
  let : Group.IsPerfect J := BinaryLinear.sylow_overgroup_radical_free_image_perfect
    (P₀.mapSurjective (f := e.toMonoidHom) e.surjective) r.range hPr f' hf' hrad
  let : Group.IsPerfect (MulAut (LinearGroup 4)) :=
    Group.IsPerfect.ofSurjective (f := eA.toMonoidHom) eA.surjective
  let : Group.IsPerfect (⊤ : Subgroup (MulAut (LinearGroup 4))) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv : (⊤ : Subgroup (MulAut (LinearGroup 4))) ≃* _).symm.toMonoidHom)
      topEquiv.symm.surjective
  have htop := top_unique (le_of_isPerfect_of_index_eq_two
    (⊤ : Subgroup (MulAut (LinearGroup 4))) _ (inner_index (Or.inl rfl)))
  exact graph_not_inner (Or.inl rfl) (htop ▸ mem_top _)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
