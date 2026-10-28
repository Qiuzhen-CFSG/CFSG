module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FiveStarExclusionSource
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.OuterSeven

/-!
# The original degree-four middle-node star parabolic

The local point centralizer acts on the perfect central cover K/O2(K) and
preserves its actual star intersection. If every induced automorphism of
SL5(2) were inner, the full point action Aut(L3(2)) would be a radical-free
image of a full-Sylow overgroup and hence perfect, contradicting its inner
subgroup of index two. Thus an outer automorphism preserves the intersection.

Relative normality in C_G(w) supplies its component Sylow, and the literal
point-residual quotient supplies a factor seven. Intrinsic flag recognition
then identifies the intersection with the stabilizer of a line inside a
hyperplane, exactly the source parabolic determined by the middle two nodes.
The central covering kernel is retained throughout.

`FourMiddleStarSource` applies the embedding to the nonsingular centralizer
and degree-five zeroth-closure consumer. The Sylow-fixed module argument,
ordinary J4 exclusion and retained pure/MS/closure obligations remain open
with their existing owners. Source: Aschbacher--Smith 12.1.1, pp.788--789.
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

theorem doubleNatural_four_adapted_C27_outer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∀ e : starImage K Q K ≃* LinearGroup 5,
        let P := ((starM K Q (B.localPointCentralizer w)).subgroupOf
          (starImage K Q K)).map e.toMonoidHom
        ∃ a : MulAut (LinearGroup 5), P.map a.toMonoidHom = P ∧
          a ∉ MulAut.innerSubgroup (LinearGroup 5) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi e
  let M := B.localPointCentralizer w
  let J := S.setup.stabilizer (Additive.ofMul w)
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
  by_contra houter
  have hti (m : M) : t m ∈ MulAut.innerSubgroup (LinearGroup 5) := by
    by_contra hn
    exact houter ⟨t m,htP m,hn⟩
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
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_four_adapted_C27_star_sylow h B S w hw K hKn hi
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
  change J ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) at eJ
  let eA := eJ.trans (MulAut.congr (projectiveEquivLinear (by decide : 0 < 3)))
  have hrad : solvableRadical J = ⊥ := by
    let := linear_simple (by decide : 3 ≤ 3)
    let : IsQuasisimple (LinearGroup 3) :=
      IsQuasisimple.of_mulEquiv (innerEquiv (by decide : 0 < 3)).symm
        (hG := (inner_isComponent (by decide : 3 ≤ 3)).2)
    have hh := MulAut.radical_free_of_inner_le (linear_center_eq_bot (by decide : 0 < 3))
      (⊤ : Subgroup (MulAut (LinearGroup 3))) le_top
    have hAut : solvableRadical (MulAut (LinearGroup 3)) = ⊥ := by
      rw [←map_solvableRadical_equiv (topEquiv : (⊤ : Subgroup (MulAut (LinearGroup 3))) ≃* _),hh,Subgroup.map_bot]
    apply map_injective (f := eA.toMonoidHom) eA.injective
    rw [map_solvableRadical_equiv,hAut,Subgroup.map_bot]
  let : Group.IsPerfect J := BinaryLinear.sylow_overgroup_radical_free_image_perfect
    (P₀.mapSurjective (f := e.toMonoidHom) e.surjective) r.range hPr f' hf' hrad
  let : Group.IsPerfect (MulAut Matrix.PSL3Two.PSL) :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  let I := MulAut.innerSubgroup Matrix.PSL3Two.PSL
  have hIc : Nat.card I = 168 := by
    let eI := MonoidHom.ofInjective (f := (MulAut.conj : Matrix.PSL3Two.PSL →* _))
      (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.Automorphisms.center_psl_eq_bot)
    rw [←Nat.card_congr eI.toEquiv,←Nat.card_congr Matrix.PSL3Two.equiv.toEquiv,
      Matrix.PSL3Two.card_SL]
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

/-- The literal degree-four star intersection is the middle-node parabolic.
Its full component Sylow is obtained from the original relative normality. -/
theorem doubleNatural_four_adapted_C27_middle
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∀ e : starImage K Q K ≃* LinearGroup 5,
        ∃ b : FiveBasis,
          ((starM K Q (B.localPointCentralizer w)).subgroupOf
            (starImage K Q K)).map e.toMonoidHom = flagStabilizer b {0,3} := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi e
  let P := (starM K Q (B.localPointCentralizer w)).subgroupOf (starImage K Q K)
  obtain ⟨a,ha,hout⟩ := D.doubleNatural_four_adapted_C27_outer h B S w hw K hKn hRK hi e
  obtain ⟨U,hUP⟩ := D.doubleNatural_four_adapted_C27_star_sylow h B S w hw K hKn hi
  have hP : P.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    exact starM_subgroupOf_ne_top hi
      (map_injective e.injective (ht.trans (map_top_of_surjective _ e.surjective).symm))
  have h7 : 7 ∣ Nat.card (P.map e.toMonoidHom) := by
    rw [card_map_of_injective e.injective]
    let A := starImage K Q (B.pointResidual w)
    have hAC : A ≤ starImage K Q K := map_mono (comap_mono hRK)
    have hAP : A.subgroupOf (starImage K Q K) ≤ P := by
      apply comap_mono
      apply map_mono
      apply comap_mono
      exact le_inf (le_inf (B.pointResidual_le_normalizer w)
        ((B.pointResidual_le w).trans inf_le_right)) hRK
    have h7A : 7 ∣ Nat.card A := by
      obtain ⟨_,⟨a⟩⟩ := D.doubleNatural_adapted_C27_residual_marking h B S w hw K hRK hi
      apply dvd_trans _ (card_quotient_dvd_card (pCore 2 A))
      rw [Nat.card_congr a.toEquiv,Matrix.PSL3Two.card_PSL]
      decide
    apply dvd_trans _ (card_dvd_of_le hAP)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
  exact outer_seven_middle_flag
    (U.mapSurjective (f := e.toMonoidHom) e.surjective) (P.map e.toMonoidHom)
    (map_mono hUP) hP h7 a hout ha

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
