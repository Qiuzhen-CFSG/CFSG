module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.PointJoinKernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.LocalSetup
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.LocalKernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourSylowMoving
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The literal J4 image of the nonsingular point-residual join

Innerness for the actual J4 carrier gives an action homomorphism from the
original point-residual/Sylow join. On its intersection with the ordinary
component this is precisely the supplied central-quotient map. Faithful
descent for perfect covers puts its kernel inside the original action
kernel, preserving the full H.9 quotient after passage to the image.

The moving subgroup remains elementary and injects with its exact order.
The image normalizes it, its two-core centralizes it, and its commutators
generate it. The original ambient Sylow theorem gives a full J4 Sylow in
the image only in degree four; degree five retains relative placement.
The covering center is retained throughout. JankoActionSource connects
these facts to the original centralizer and closure consumer, with the
finite J4 exclusion still explicit. This is not an exclusion of J4.
Source: Aschbacher--Smith 12.1.1, printed p.788, and H.9.1(4), p.390.
The imported native J4 proofs retain their matrix-certificate attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original point join has a literal J4 image with its full H.9 quotient,
faithful moving subgroup, and only the Sylow containment actually proved in the source. -/
theorem doubleNatural_adapted_jankoFour_pointJoin_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
      ∀ e : (K ⧸ center K) ≃* Janko4.Model,
      let J := B.pointResidual w ⊔ B.pointSylow w
      let U := (⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf J
      ∃ r : J →* Janko4.Model,
        (∀ (x : J) (hx : (x : G) ∈ K),
          r x = e (QuotientGroup.mk' (center K) ⟨x,hx⟩)) ∧
        r.ker ≤ pCore 2 J ∧ Function.Injective (r.comp U.subtype) ∧
        Nonempty ((r.range ⧸ pCore 2 r.range) ≃*
          MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2))) ∧
        IsElementaryAbelian 2 (U.map r) ∧ Nat.card (U.map r) = 2^(2*(n-1)) ∧
        r.range ≤ normalizer (U.map r : Set Janko4.Model) ∧
        r.range.pCoreIn 2 ≤ centralizer (U.map r : Set Janko4.Model) ∧
        U.map r = ⁅U.map r,r.range⁆ ∧
        (n = 4 → ∃ P : Sylow 2 Janko4.Model, (P : Subgroup Janko4.Model) ≤ r.range) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK e J U
  let R := B.pointResidual w
  let W := componentOrbit V (T : Subgroup G)
  let M := B.localPointCentralizer w
  let F := S.setup.stabilizer (Additive.ofMul w)
  have hPM : B.pointSylow w ≤ M := le_inf
    (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hJM : J ≤ M := sup_le hRM hPM
  obtain ⟨hRK,hKn⟩ := D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK
  have hMN : M ≤ normalizer (K : Set G) := inf_le_right.trans
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKn)
  let a : J →* MulAut K := K.normalizerMonoidHom.comp (inclusion (hJM.trans hMN))
  let d : Janko4.Model ≃* MulAut Janko4.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩
  let r : J →* Janko4.Model := d.symm.toMonoidHom.comp
    ((MulAut.centralQuotientAction e).comp a)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hr (x : J) (hx : (x : G) ∈ K) : r x = q ⟨x,hx⟩ := by
    apply d.injective
    change d (d.symm
      (MulAut.centralQuotientAction e (a x))) = _
    rw [d.apply_symm_apply]
    have ha : a x = MulAut.conj (⟨x,hx⟩ : K) := by ext y; rfl
    rw [ha,MulAut.centralQuotientAction_conj]
    rfl
  let := hK.quasisimple
  let f := (S.localPointAction w).comp (inclusion hJM)
  have hf : Function.Surjective f := S.adapted_pointJoin_action_surjective w hw hPM
  have hkf : f.ker = pCore 2 J := D.doubleNatural_adapted_pointJoin_action_kernel h B S w hw hJM
  have hker : r.ker ≤ f.ker := by
    intro x hx
    have hb : MulAut.centralQuotientAction e (a x) = 1 :=
      d.symm.injective (hx.trans d.symm.map_one.symm)
    have ha : a x = 1 := MulAut.centralQuotientAction_injective e
      (hb.trans (MulAut.centralQuotientAction e).map_one.symm)
    have hxc : (x : G) ∈ centralizer (K : Set G) := by
      have hh : inclusion (hJM.trans hMN) x ∈ K.normalizerMonoidHom.ker := ha
      rwa [normalizerMonoidHom_ker] at hh
    have hfc : f x ∈ centralizer (pResidual 2 F : Set F) := by
      intro y hy
      rw [←S.residual_localPointAction w hw.nonsingular] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      have he : z * inclusion hJM x = inclusion hJM x * z :=
        Subtype.ext (hxc z (hRK hz))
      exact congrArg (S.localPointAction w) he
    rw [S.nonsingular_stabilizer_residual_centralizer_eq_bot w hw.nonsingular] at hfc
    exact hfc
  have hkr : r.ker ≤ pCore 2 J := hker.trans hkf.le
  have hkr' : IsPGroup 2 r.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact pCore_isPGroup.to_le hkr
  let er := r.rangeRestrict.pCoreQuotientEquiv r.rangeRestrict_surjective hkr'
  let ef : (J ⧸ pCore 2 J) ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hkf.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  obtain ⟨eF⟩ := (S.setup.nonsingular_structure
    (show S.setup.quadratic (Additive.ofMul w) = 1 by rw [S.quadratic_eq]; exact hw.nonsingular)).2.2.1
  have hUR : ⁅W,R⁆ ≤ R := D.doubleNatural_moving_le_residual h B w
  have hUJ : ⁅W,R⁆ ≤ J := hUR.trans le_sup_left
  have hUK : ⁅W,R⁆ ≤ K := hUR.trans hRK
  have hUW : ⁅W,R⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (B.pointResidual_normalizes_orbit w)
  let i : U →* W := (inclusion hUW).comp (subgroupOfEquivOfLe hUJ).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective i
    ((inclusion_injective hUW).comp (subgroupOfEquivOfLe hUJ).injective)
  have hi : Function.Injective (r.comp U.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro u hu
    have he : q ⟨u.val,hUK u.property⟩ = 1 := (hr u.val (hUK u.property)).symm.trans hu
    have hz : (⟨u.val,hUK u.property⟩ : K) ∈ center K :=
      (QuotientGroup.eq_one_iff _).mp (e.injective (he.trans e.map_one.symm))
    have hc : (u.val : G) ∈ centralizer (K : Set G) := by
      intro k hk
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k,hk⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact mem_bot.mp ((D.doubleNatural_adapted_component_moving_centralizer h B S w hw K hK) ▸
      (show (u.val : G) ∈ ⁅W,R⁆ ⊓ centralizer (K : Set G) from ⟨u.property,hc⟩))
  have hcard : Nat.card (U.map r) = 2^(2*(n-1)) := by
    have hinj : Function.Injective (r.subgroupMap U) := fun x y he => hi (congrArg Subtype.val he)
    rw [←Nat.card_congr (MulEquiv.ofBijective (r.subgroupMap U)
      ⟨hinj,r.subgroupMap_surjective U⟩).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hUJ).toEquiv]
    exact S.nonsingular_moving_card w hw.nonsingular
  have hJN : J ≤ normalizer (⁅W,R⁆ : Subgroup G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator]
    have hW : x ∈ normalizer (W : Set G) := by
      have hMW : M ≤ normalizer (W : Set G) := by
        apply le_trans inf_le_left
        change normalizer (L : Set G) ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G)
        rw [B.orbit_eq]
        exact le_normalizer_componentOrbit _ _
      exact hMW (hJM hx)
    rw [mem_normalizer_iff_map_conj_eq.mp hW,
      mem_normalizer_iff_map_conj_eq.mp (B.localPointCentralizer_normalizes_residual w (hJM hx))]
  have hUn : U.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hN : r.range ≤ normalizer (U.map r : Set Janko4.Model) := by
    let := hUn
    rintro _ ⟨x,rfl⟩
    exact le_normalizer_map r (mem_map_of_mem r (U.normalizer_eq_top ▸ mem_top x))
  have hcore : r.range.pCoreIn 2 ≤ centralizer (U.map r : Set Janko4.Model) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := r.rangeRestrict_surjective x
    have hycore : y ∈ pCore 2 J := by
      rw [←r.rangeRestrict.comap_pCore_of_ker_isPGroup r.rangeRestrict_surjective hkr']
      change r.rangeRestrict y ∈ pCore 2 r.range
      rw [hy]
      exact hx
    have hyQ : (y : G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      D.doubleNatural_adapted_pointJoin_twoCore h B S w hw ▸ mem_map_of_mem J.subtype hycore
    rw [←D.doubledOrbit_sylow_centralizer h] at hyQ
    rintro _ ⟨u,hu,rfl⟩
    have he : u * y = y * u := Subtype.ext (hyQ.2 u (hUW hu))
    have hh := congrArg r he
    change r u * (x : Janko4.Model) = (x : Janko4.Model) * r u
    simpa only [map_mul,show r y = (x : Janko4.Model) from congrArg Subtype.val hy] using hh
  have hmove : U.map r = ⁅U.map r,r.range⁆ := by
    have he : U = ⁅U,⊤⁆ := by
      apply map_injective J.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
        ←MonoidHom.range_eq_map,range_subtype]
      apply le_antisymm
      · calc
          ⁅W,R⁆ = ⁅⁅W,R⁆,R⁆ := (commutator_isPPerfect_idempotent R W
            (B.pointResidual_isPPerfect w) (IsElementaryAbelian.isPGroup 2 W)
            (B.pointResidual_normalizes_orbit w)).symm
          _ ≤ ⁅⁅W,R⁆,J⁆ := commutator_mono le_rfl le_sup_left
      · exact le_normalizer_iff_commutator_le_left.mp hJN
    have hh := congrArg (map r) he
    simpa only [map_commutator,←MonoidHom.range_eq_map] using hh
  refine ⟨r,hr,hkr,hi,⟨er.symm.trans (ef.trans eF)⟩,
    IsElementaryAbelian.map r,hcard,hN,hcore,hmove,?_⟩
  intro hn
  subst n
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
  let P := P₂.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨P,?_⟩
  rintro _ ⟨k,hk,rfl⟩
  have hkP : (k : G) ∈ B.pointSylow w := (hP₂ ▸ mem_map_of_mem K.subtype hk).1
  exact ⟨⟨k,mem_sup_right hkP⟩,hr ⟨k,mem_sup_right hkP⟩ k.property⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
