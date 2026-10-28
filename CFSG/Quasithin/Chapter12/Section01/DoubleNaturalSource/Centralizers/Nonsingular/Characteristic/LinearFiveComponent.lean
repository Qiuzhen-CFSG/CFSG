module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.MathieuComponent
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.LinearFiveNormalizer

/-!
# Excluding the ordinary binary-five component at a nonsingular point

The original moving subgroup injects into the component central quotient,
has order 64, and is normalized by a full component Sylow subgroup. Its
normalizer has a factor seven from the literal L3(2) residual quotient.
The normalizer obstruction makes every local point-centralizer actor inner.

Perfect central-cover rigidity identifies the kernel of this inner action
as a subgroup centralizing the full component. It therefore fixes the
original point residual and acts trivially on the full H.9 stabilizer.
That stabilizer becomes a radical-free quotient of an actual full-Sylow
overgroup in L5(2), hence perfect. Its genuine Aut(L3(2)) identification
has an inner subgroup of index two, giving the contradiction.

The covering center and the original C_G(w)-relative Sylow intersection
are retained. `JankoSource` applies the exclusion to nonsingular centralizer
control and degree-five zeroth closure, retaining all unresolved branches.
Source: Aschbacher--Smith 12.1.1 and H.9.1(4), printed pp.788 and390.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
open PerfectCentralCovering

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal moving subgroup and full point action exclude an L5(2) central quotient. -/
theorem doubleNatural_four_adapted_component_not_linearFive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ Nonempty ((K ⧸ center K) ≃* (LinearGroup 5)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK ⟨e⟩
  let M := B.localPointCentralizer w
  let J := S.setup.stabilizer (Additive.ofMul w)
  let R := B.pointResidual w
  let W := componentOrbit V (T : Subgroup G)
  let U := ⁅W,R⁆
  obtain ⟨hRK,hKn⟩ := D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK
  have hUK : U ≤ K := (D.doubleNatural_moving_le_residual h B w).trans hRK
  have hMN : M ≤ normalizer (K : Set G) := inf_le_right.trans
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKn)
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hMU : M ≤ normalizer (U : Set G) := by
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ⁅W,R⁆.map (MulAut.conj m).toMonoidHom = ⁅W,R⁆
    rw [map_commutator]
    have hMW : M ≤ normalizer (W : Set G) := by
      apply le_trans inf_le_left
      change normalizer (L : Set G) ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G)
      rw [B.orbit_eq]
      exact le_normalizer_componentOrbit _ _
    have heW : W.map (MulAut.conj m).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp (hMW hm)
    have heR : R.map (MulAut.conj m).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
      (B.localPointCentralizer_normalizes_residual w hm)
    rw [heW,heR]
  let := hK.quasisimple
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let c : Cover K (LinearGroup 5) := {
    toMonoidHom := q
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := hq.le }
  let a : M →* MulAut K := K.normalizerMonoidHom.comp (inclusion hMN)
  let E := (U.subgroupOf K).map q
  obtain ⟨P,hUP,hn,hele,hcard,hi⟩ :=
    D.doubleNatural_four_adapted_component_moving_normalSylow h B S w hw K hK
  let : IsElementaryAbelian 2 (U.subgroupOf K) := hele
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hiq : Function.Injective (q.comp (U.subgroupOf K).subtype) := e.injective.comp hi
  have hE : Nat.card E = 64 := by
    have he : Nat.card E = Nat.card (U.subgroupOf K) := Nat.card_congr
      (MulEquiv.ofBijective (q.subgroupMap (U.subgroupOf K)) ⟨by
        intro x y hxy
        exact hiq (congrArg Subtype.val hxy),q.subgroupMap_surjective _⟩).symm.toEquiv
    exact he.trans hcard
  let H := B.pointCentralizer w
  let K₀ := K.subgroupOf H
  let : K₀.Normal := hKn
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_four_adapted_ambientSylow h B S w hw
  obtain ⟨P₁,hP₁⟩ := P₀.exists_sylow_map_eq_inf_of_normal K₀
  let eK := subgroupOfEquivOfLe hK.1
  let P₂ := P₁.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP₂ : (P₂ : Subgroup K).map K.subtype = B.pointSylow w ⊓ K := by
    change ((P₁ : Subgroup K₀).map eK.toMonoidHom).map K.subtype = _
    rw [map_map]
    have he : K.subtype.comp eK.toMonoidHom = H.subtype.comp K₀.subtype := rfl
    rw [he,←map_map,hP₁,map_inf _ _ _ H.subtype_injective,hP₀,
      map_subgroupOf_eq_of_le hK.1]
  let Q := P₂.mapSurjective (f := q) c.surjective
  have hPM : B.pointSylow w ≤ M := le_inf
    (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hQN : (Q : Subgroup (LinearGroup 5)) ≤ normalizer (E : Set (LinearGroup 5)) := by
    rintro _ ⟨k,hk,rfl⟩
    apply le_normalizer_map q
    apply mem_map_of_mem q
    rw [←subgroupOf_normalizer_eq hUK]
    exact hMU (hPM ((hP₂ ▸ mem_map_of_mem K.subtype hk).1))
  have hseven : 7 ∣ Nat.card (normalizer (E : Set (LinearGroup 5))) := by
    let A := R.subgroupOf K
    let q₀ := QuotientGroup.mk' (center K)
    obtain ⟨hperf,⟨eA⟩,hne,hele,hmove,hAN⟩ :=
      D.doubleNatural_adapted_component_local_marking h B S w hw K hK
    have h7 : 7 ∣ Nat.card (A.map q₀) := by
      apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (A.map q₀)))
      rw [Nat.card_congr (eA.trans Matrix.PSL3Two.equiv.symm).toEquiv,Matrix.PSL3Two.card_SL]
      decide
    have h7q : 7 ∣ Nat.card (A.map q) := by
      rw [show A.map q = (A.map q₀).map e.toMonoidHom from (map_map _ _ _).symm,
        card_map_of_injective e.injective]
      exact h7
    have hANq : A.map q ≤ normalizer (E : Set (LinearGroup 5)) := by
      have hh := (map_mono (f := e.toMonoidHom) hAN).trans (le_normalizer_map e.toMonoidHom)
      simpa only [map_map] using hh
    exact h7q.trans (card_dvd_of_le hANq)
  let t : M →* MulAut (LinearGroup 5) := (c.autMap hq).comp a
  have ht (m : M) : E.map (t m).toMonoidHom = E := by
    apply eq_of_le_of_card_ge ?_ (card_map_of_injective (t m).injective).symm.le
    rintro _ ⟨_,⟨u,hu,rfl⟩,rfl⟩
    refine ⟨a m u,?_,(c.autMap_apply hq (a m) u).symm⟩
    exact (mem_normalizer_iff.mp (hMU m.property) u.val).mp hu
  have hti (m : M) : t m ∈ MulAut.innerSubgroup (LinearGroup 5) :=
    Nonsingular.LinearFive.normalizing_actor_inner Q E hE hQN hseven (t m) (ht m)
  let d : LinearGroup 5 ≃* MulAut.innerSubgroup (LinearGroup 5) :=
    MonoidHom.ofInjective (f := MulAut.conj)
      (MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot (by decide : 0 < 5)))
  let r : M →* LinearGroup 5 := d.symm.toMonoidHom.comp (t.codRestrict _ hti)
  have hr (m : M) (k : K) : r m * q k * (r m)⁻¹ = q (a m k) := by
    change (d (r m) : MulAut (LinearGroup 5)) (q k) = q (a m k)
    change (d (d.symm ⟨t m,hti m⟩) : MulAut (LinearGroup 5)) (q k) = _
    rw [d.apply_symm_apply]
    exact c.autMap_apply hq (a m) k
  have hQr : (Q : Subgroup (LinearGroup 5)) ≤ r.range := by
    rintro _ ⟨k,hk,rfl⟩
    have hkm : (k : G) ∈ M := hPM ((hP₂ ▸ mem_map_of_mem K.subtype hk).1)
    let m : M := ⟨k,hkm⟩
    refine ⟨m,?_⟩
    apply MulAut.conj_injective_of_center_eq_bot (linear_center_eq_bot (by decide : 0 < 5))
    apply MulEquiv.ext
    intro x
    obtain ⟨j,rfl⟩ := c.surjective x
    rw [MulAut.conj_apply,hr]
    change q (k*j*k⁻¹) = q k*q j*(q k)⁻¹
    simp only [map_mul,map_inv]
  let f := S.localPointAction w
  have hker : r.ker ≤ f.ker := by
    intro m hm
    have hb : c.autMap hq (a m) = 1 := by
      have hh := congrArg (fun x : LinearGroup 5 => (d x : MulAut (LinearGroup 5))) hm
      simpa only [r,t,MonoidHom.comp_apply,MonoidHom.codRestrict_apply,OneMemClass.coe_one,
        MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply,map_one] using hh
    have ha : a m = 1 := c.autMap_injective hq (hb.trans (c.autMap hq).map_one.symm)
    have hmc : (m : G) ∈ centralizer (K : Set G) := by
      have hh : inclusion hMN m ∈ K.normalizerMonoidHom.ker := ha
      rwa [normalizerMonoidHom_ker] at hh
    have hfc : f m ∈ centralizer (pResidual 2 J : Set J) := by
      intro j hj
      rw [←S.residual_localPointAction w hw.nonsingular] at hj
      obtain ⟨x,hx,rfl⟩ := hj
      have hh : x * m = m * x := Subtype.ext (hmc x (hRK hx))
      exact congrArg f hh
    rw [S.nonsingular_stabilizer_residual_centralizer_eq_bot w hw.nonsingular] at hfc
    exact hfc
  let f' : r.range →* J := r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective
    ⟨f,by simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have hf' : Function.Surjective f' := by
    intro j
    obtain ⟨m,rfl⟩ := S.localPointAction_surjective w j
    exact ⟨r.rangeRestrict m,r.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ m⟩
  obtain ⟨eJ⟩ := (S.setup.nonsingular_structure
    (show S.setup.quadratic (Additive.ofMul w) = 1 by rw [S.quadratic_eq]; exact hw.nonsingular)).2.2.1
  change J ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) at eJ
  have hrad : solvableRadical J = ⊥ := by
    let eL := projectiveEquivLinear (by decide : 0 < 3)
    let eA := eJ.trans (MulAut.congr eL)
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
    Q r.range hQr f' hf' hrad
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
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
