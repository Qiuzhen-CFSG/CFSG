module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourMiddleStar
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarNormalizerAction

/-!
# A simultaneous outer actor on the original degree-four star component

Restrict the local point action to the join of the point residual and its
actual point Sylow. This join normalizes both the component and the original
core. If all its component automorphisms were inner, its full Aut(L3(2))
point action would be a radical-free image of an SL5(2) Sylow overgroup,
hence perfect. The inner subgroup of index two contradicts that conclusion.
The actual actor will select the natural-plus-dual module in `FourStarModule`.

Relative normality supplies the component Sylow, and the full central cover
is retained. Source: Aschbacher--Smith 12.1.1, printed pp.788--789.
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
/-- A literal actor in the point-residual/Sylow join induces an outer
automorphism of the actual star component and normalizes the original core. -/
theorem doubleNatural_four_adapted_C27_outer_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∀ _e : starImage K Q K ≃* LinearGroup 5,
        ∃ (a : G) (hK : a ∈ normalizer (K : Set G))
          (hQ : a ∈ normalizer (Q : Set G)),
          a ∈ B.pointResidual w ⊔ B.pointSylow w ∧
          starComponentAut K Q a hK hQ ∉ MulAut.innerSubgroup (starImage K Q K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi e
  let M := B.pointResidual w ⊔ B.pointSylow w
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hMM : M ≤ B.localPointCentralizer w := sup_le
    (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)) hPM
  have hMLT : M ≤ L ⊔ (T : Subgroup G) := sup_le
    ((B.pointResidual_le w).trans (inf_le_left.trans le_sup_left))
    (inf_le_left.trans le_sup_right)
  have hMQ : M ≤ normalizer (Q : Set G) := hMLT.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  let J := S.setup.stabilizer (Additive.ofMul w)
  have hMN : M ≤ normalizer (K : Set G) := (hMM.trans inf_le_right).trans
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
  have htstar (m : M) : t m = MulAut.congr e
      (starComponentAut K Q m (hMN m.property) (hMQ m.property)) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨k,rfl⟩ := (e.surjective.comp (toStarImage_surjective K Q)) y
    change t m (q k) = _
    rw [htq]
    change e (toStarImage K Q _) =
      e (starComponentAut K Q m (hMN m.property) (hMQ m.property)
        (e.symm (e (toStarImage K Q k))))
    rw [e.symm_apply_apply,starComponentAut_toStarImage]
    rfl
  by_contra houter
  have hti (m : M) : t m ∈ MulAut.innerSubgroup (LinearGroup 5) := by
    have hin : starComponentAut K Q m (hMN m.property) (hMQ m.property) ∈
        MulAut.innerSubgroup (starImage K Q K) := by
      by_contra hn
      exact houter ⟨m,hMN m.property,hMQ m.property,m.property,hn⟩
    obtain ⟨g,hg⟩ := hin
    rw [htstar,←hg,MulAut.congr_conj]
    exact ⟨e g,rfl⟩
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
  let f := (S.localPointAction w).comp (inclusion hMM)
  have hker : r.ker ≤ f.ker := by
    intro m hm
    have hb : c.autMap hc (a m) = 1 := by
      have hh := congrArg (fun x : LinearGroup 5 => (d x : MulAut (LinearGroup 5))) hm
      simpa only [r,t,MonoidHom.comp_apply,MonoidHom.codRestrict_apply,OneMemClass.coe_one,
        MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply,map_one] using hh
    have ha := c.autMap_injective hc (hb.trans (c.autMap hc).map_one.symm)
    exact D.doubleNatural_adapted_coreAction_kernel h B S w hw K hRK
      (inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hi.component.1).mp hKn)) ha
  let f' : r.range →* J := r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective
    ⟨f,by simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have hf' : Function.Surjective f' := by
    intro j
    obtain ⟨m,rfl⟩ := S.adapted_pointJoin_action_surjective w hw hPM j
    exact ⟨r.rangeRestrict m,r.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ m⟩
  let H := B.pointCentralizer w
  let K₀ := K.subgroupOf H
  let : K₀.Normal := hKn
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_four_adapted_ambientSylow h B S w hw
  obtain ⟨P₁,hP₁⟩ := P₀.exists_sylow_map_eq_inf_of_normal K₀
  let eK := subgroupOfEquivOfLe hi.component.1
  let P₂ := P₁.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP₂ : (P₂ : Subgroup K).map K.subtype = B.pointSylow w ⊓ K := by
    change ((P₁ : Subgroup K₀).map eK.toMonoidHom).map K.subtype = _
    rw [map_map]
    have he : K.subtype.comp eK.toMonoidHom = H.subtype.comp K₀.subtype := rfl
    rw [he,←map_map,hP₁,map_inf _ _ _ H.subtype_injective,hP₀,
      map_subgroupOf_eq_of_le hi.component.1]
  let P := P₂.mapSurjective (f := q) (e.surjective.comp (toStarImage_surjective K Q))
  have hPr : (P : Subgroup (LinearGroup 5)) ≤ r.range := by
    rintro _ ⟨k,hk,rfl⟩
    have hkP : (k : G) ∈ B.pointSylow w := (hP₂ ▸ mem_map_of_mem K.subtype hk).1
    have hkM : (k : G) ∈ M := mem_sup_right hkP
    exact ⟨⟨k,hkM⟩,hr k hkM⟩
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
    P r.range hPr f' hf' hrad
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
