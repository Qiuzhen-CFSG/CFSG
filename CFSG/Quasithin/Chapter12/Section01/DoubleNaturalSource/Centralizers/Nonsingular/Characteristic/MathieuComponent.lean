module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourSylowMoving
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.LocalKernel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.MathieuNormalizer
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.AutomorphismOvergroupRadical
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# Excluding the ordinary Mathieu component at a nonsingular point

The moving subgroup injects into K/Z(K) and has order64. All automorphisms
of the actual M24 quotient are inner, giving a homomorphism from the local
point centralizer to its moving-subgroup normalizer. Perfect central-cover
rigidity identifies its kernel with a subgroup centralizing K. This kernel
fixes the original point residual, and hence acts trivially on the entire
source stabilizer. The full Aut(L3(2)) action is therefore a radical-free
section of that native normalizer, contradicting `MathieuNormalizer`.

The center of K is retained throughout; neither K itself nor the relative
Sylow is silently replaced by its quotient. `TwoModelSource` applies the
exclusion to the actual nonsingular-centralizer and degree-five closure
consumer. The other component and parabolic branches remain with
qt-d-double-natural-centralizers.
Source: Aschbacher--Smith12.1.1 and H.9.1(4), printed pp.788 and390.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
open PerfectCentralCovering
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal moving subgroup and full point action exclude an M24 central quotient. -/
theorem doubleNatural_four_adapted_component_not_mathieu
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ Nonempty ((K ⧸ center K) ≃* M24) := by
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
  let c : Cover K M24 := {
    toMonoidHom := q
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := hq.le }
  have hzc : center M24 = ⊥ := by
    apply bot_unique
    intro z hz
    have hh := (centerCongr e.symm ⟨z,hz⟩).property
    change e.symm z ∈ center (K ⧸ center K) at hh
    rw [Group.IsPerfect.center_quotient_center_eq_bot K,mem_bot] at hh
    exact mem_bot.mpr (e.symm.injective (hh.trans e.symm.map_one.symm))
  let d : M24 ≃* MulAut M24 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot hzc,M24OuterRestriction.conj_surjective⟩
  let a : M →* MulAut K := K.normalizerMonoidHom.comp (inclusion hMN)
  let r : M →* M24 := d.symm.toMonoidHom.comp ((c.autMap hq).comp a)
  have hr (m : M) (k : K) : r m * q k * (r m)⁻¹ = q (a m k) := by
    change d (r m) (q k) = q (a m k)
    change d (d.symm (c.autMap hq (a m))) (q k) = _
    rw [d.apply_symm_apply]
    exact c.autMap_apply hq (a m) k
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
  have hNE : r.range ≤ normalizer (E : Set M24) := by
    rintro _ ⟨m,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (by
      have he : Nat.card (E.map (MulAut.conj (r m)).toMonoidHom) = Nat.card E :=
        card_map_of_injective (MulAut.conj (r m)).injective
      exact he.symm.le)
    rintro _ ⟨_,⟨u,hu,rfl⟩,rfl⟩
    refine ⟨a m u,?_,(hr m u).symm⟩
    exact (mem_normalizer_iff.mp (hMU m.property) u.val).mp hu
  let f := S.localPointAction w
  have hker : r.ker ≤ f.ker := by
    intro m hm
    have hb : c.autMap hq (a m) = 1 := d.symm.injective
      (hm.trans d.symm.map_one.symm)
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
  have hcJ : Nat.card J = 336 := by
    rw [Nat.card_congr eJ.toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
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
  exact Nonsingular.mathieu_no_full_three_action r.range.subtype r.range.subtype_injective
    E hE (by simpa only [range_subtype] using hNE) f' hf' hrad hcJ
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
