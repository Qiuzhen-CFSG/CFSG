module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.LocalComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Fixed

/-!
# The ordinary component at a pure point

The moved subgroup U = [W,O²(C_L(w))] lies in the literal residual. Any
ordinary component of C_G(w) distinct from its containing C-component
centralizes U, hence lies in C_M(w). Characteristic two of C_M(w) excludes
that possibility. Thus the ordinary component is the containing component
and is normal, with the original residual and both moved summands inside it.

The marked point stabilizer fixes exactly the natural point line. Transport
through the actual residual image gives C_W(O²(C_L(w))) = ⟨w⟩ and therefore
U ∩ Z(K) = ⟨w⟩. In particular the original point is a central involution of K.
The marked ambient Sylow remains explicit; the existing dimension-five
result supplies it. Model exclusion and the dimension-four Sylow argument
remain with `qt-d-double-natural-pure-fusion`.

Source: Aschbacher--Smith, 12.1.6, printed p.791, using 1.2.1--4 and H.9.1.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

theorem pure_moving_le_residual
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ B.pointResidual w := by
  have hWM : componentOrbit V (T : Subgroup G) ≤ B.localPointCentralizer w := by
    refine le_inf ((componentOrbit V (T : Subgroup G)).le_normalizer.trans_eq hNM) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : componentOrbit V (T : Subgroup G)) w))
  have hWN := hWM.trans (B.localPointCentralizer_normalizes_residual w)
  have hc := le_normalizer_iff_commutator_le_right.mp hWN
  obtain ⟨h₁,h₂⟩ := S.pure_residual_commutators hNM w hw hp
  exact sup_le (h₁.symm.le.trans ((commutator_mono B.naturalSummand_le le_rfl).trans hc))
    (h₂.symm.le.trans ((commutator_mono B.dualSummand_le le_rfl).trans hc))

include S in
theorem pure_component_eq_containing
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hns : B.NonsingularCentralizers)
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hc : HasCharacteristicTwo ((normalizer (L : Set G)).subgroupOf (B.pointCentralizer w)))
    (K J : Subgroup (B.pointCentralizer w)) (hK : IsComponent (B.pointCentralizer w) K)
    (hJ : J.IsCComponent)
    (hXJ : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ J) : K = J := by
  rcases hK.subnormal_dichotomy J hJ.subnormal with hKJ | hcomm
  · exact hK.isCComponent.eq_of_le hJ hKJ
  · have hX : B.pointResidual w ≤ J.map (B.pointCentralizer w).subtype := by
      have hm := map_mono (f := (B.pointCentralizer w).subtype) hXJ
      rwa [map_subgroupOf_eq_of_le ((B.pointResidual_le w).trans inf_le_right)] at hm
    have hU := (pure_moving_le_residual S hNM w hw hp).trans hX
    have hm := congrArg (map (B.pointCentralizer w).subtype) hcomm
    rw [map_commutator, Subgroup.map_bot] at hm
    have hKM : K.map (B.pointCentralizer w).subtype ≤ normalizer (L : Set G) := by
      have hk := (commutator_eq_bot_iff_le_centralizer.mp hm).trans (centralizer_le hU)
      rw [S.pure_moving_centralizer hNM hns (S.summandCentralizers hNM) w hw hp] at hk
      exact hk.trans ((Subgroup.centralizer_le_normalizer _).trans_eq hNM)
    have hk : K ≤ (normalizer (L : Set G)).subgroupOf (B.pointCentralizer w) := by
      intro k hk
      exact hKM (mem_map_of_mem _ hk)
    exact (not_isComponent_of_twoCore hc _ (hK.subgroupOf hk)).elim

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup n M E)

theorem pure_fixed_eq_point (u : S.natural) (hu : (u : E) ≠ 0) :
    S.fixed (S.residual u) = Submodule.span (ZMod 2) {(u : E)} := by
  apply le_antisymm
  · intro v hv
    have hf : ∀ g : BinaryNaturalDual.VectorStabilizers.Pure.pointStabilizer
        (S.naturalCoordinates u),
        BinaryLinear.NaturalDualFlag.action g.val (S.model.coordinates v) = S.model.coordinates v := by
      intro g
      let a := (S.purePointEquiv u hu).symm g
      have ha : a.val ∈ S.residual u := (S.pure_stabilizer_eq_residual u hu).1 ▸ a.property
      have he := congrArg S.model.coordinates (hv ⟨a.val,ha⟩)
      change S.model.coordinates (S.representation a.val v) = S.model.coordinates v at he
      rw [S.model.equivariant, ← S.pureInnerEquiv_apply u hu a,
        BinaryNaturalDual.VectorStabilizers.Pure.inner_action] at he
      change BinaryLinear.NaturalDualFlag.action ((S.purePointEquiv u hu) a).val
        (S.model.coordinates v) = S.model.coordinates v at he
      simpa only [a, MulEquiv.apply_symm_apply] using he
    have hf' := (BinaryNaturalDual.VectorStabilizers.Pure.point_fixed_iff
      (by simp only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin];
          have := S.degree; omega)
      (S.naturalCoordinates_ne_zero u hu) (S.model.coordinates v)).mp hf
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hf'.1
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,S.model.coordinates.injective ?_⟩
    rw [map_smul,S.model.natural_marking]
    exact Prod.ext hc (by simpa only [Prod.smul_snd, smul_zero] using hf'.2.symm)
  · apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    intro a
    change S.representation a.val u = u
    exact (S.pure_stabilizer_eq_residual u hu).1.ge a.property

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
theorem pure_residual_fixed_eq_point
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    componentOrbit V (T : Subgroup G) ⊓ centralizer (B.pointResidual w : Set G) =
      zpowers (w : G) := by
  apply le_antisymm
  · intro x hx
    let v : componentOrbit V (T : Subgroup G) := ⟨x,hx.1⟩
    let u : S.setup.natural := ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩
    have hf : Additive.ofMul v ∈ S.setup.fixed (S.setup.residual u) := by
      intro a
      have ha := (S.pointResidual_image w).ge a.property
      obtain ⟨l,hl,he⟩ := ha
      change S.setup.representation a.val (Additive.ofMul v) = Additive.ofMul v
      rw [←he,S.representation_eq]
      apply congrArg Additive.ofMul
      apply Subtype.ext
      have hc := hx.2 l (show (l : G) ∈ B.pointResidual w from mem_map_of_mem _ hl)
      change (l : G) * x * (l : G)⁻¹ = x
      rw [hc,mul_inv_cancel_right]
    rw [S.setup.pure_fixed_eq_point u hw] at hf
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hf
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp only [zero_smul] at hc
      have he : x = 1 := (congrArg (fun a : Additive (componentOrbit V (T : Subgroup G)) => (a.toMul : G)) hc).symm
      exact he ▸ (zpowers (w : G)).one_mem
    · simp only [one_smul] at hc
      have he : x = (w : G) := (congrArg (fun a : Additive (componentOrbit V (T : Subgroup G)) => (a.toMul : G)) hc).symm
      exact he ▸ mem_zpowers (w : G)
  · refine le_inf (zpowers_le.mpr w.property) ?_
    apply zpowers_le.mpr
    intro a ha
    exact mem_centralizer_singleton_iff.mp ((B.pointResidual_le w ha).2)

omit [Finite G] in
theorem pure_component_central_point
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (K : Subgroup (B.pointCentralizer w))
    (hU : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype) :
    ∃ v : K, ((v : B.pointCentralizer w) : G) = (w : G) ∧
      v ∈ center K ∧ orderOf v = 2 := by
  let wH : B.pointCentralizer w := ⟨w,mem_centralizer_singleton_iff.mpr rfl⟩
  have hwK : wH ∈ K := by
    obtain ⟨x,hx,he⟩ := hU ((show B.naturalSummand ≤ B.naturalSummand ⊔ S.pureDualHyperplane w hp from le_sup_left) ((B.mem_naturalSummand w).mpr hp))
    have he' : x = wH := Subtype.ext he
    exact he' ▸ hx
  let v : K := ⟨wH,hwK⟩
  refine ⟨v,rfl,?_,?_⟩
  · apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp x.val.property
  · rw [← orderOf_injective ((B.pointCentralizer w).subtype.comp K.subtype)
      ((B.pointCentralizer w).subtype_injective.comp K.subtype_injective)]
    exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
      (fun he => hw (Subtype.ext he))

theorem pure_moving_center_intersection
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (K : Subgroup (B.pointCentralizer w))
    (hX : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K)
    (hU : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype) :
    (B.naturalSummand ⊔ S.pureDualHyperplane w hp) ⊓
      ((center K).map K.subtype).map (B.pointCentralizer w).subtype = zpowers (w : G) := by
  apply le_antisymm
  · intro x hx
    apply (S.pure_residual_fixed_eq_point w hw hp).le
    refine ⟨(sup_le B.naturalSummand_le
      ((S.pureDualHyperplane_le_dualSummand w hp).trans B.dualSummand_le)) hx.1,?_⟩
    obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hx.2
    intro l hl
    let lH : B.pointCentralizer w := ⟨l,(B.pointResidual_le w hl).2⟩
    have hh := mem_center_iff.mp hb (⟨lH,hX hl⟩ : K)
    exact congrArg (fun k : K => ((k : B.pointCentralizer w) : G)) hh
  · apply zpowers_le.mpr
    obtain ⟨v,he,hv,_⟩ := S.pure_component_central_point w hw hp K hU
    refine ⟨(show B.naturalSummand ≤ B.naturalSummand ⊔ S.pureDualHyperplane w hp from le_sup_left) ((B.mem_naturalSummand w).mpr hp),?_⟩
    rw [←he]
    exact mem_map_of_mem _ (mem_map_of_mem _ hv)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem doubleNatural_pure_local_characteristicTwo_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      HasCharacteristicTwo ((normalizer (L : Set G)).subgroupOf (B.pointCentralizer w)) := by
  let := D.doubledOrbit_elementary h
  intro w hw
  let M := normalizer (L : Set G)
  let H := B.pointCentralizer w
  have hw2 : orderOf (w : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    (fun he => hw (Subtype.ext he))
  have hMc : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (h.simpleQTKE.evenCharacteristic T M (D.doubledNormalizer_unique h).1
      D.sylow_normalizes_component)
  have hwM : zpowers (w : G) ≤ M := zpowers_le.mpr
    (D.sylow_normalizes_component ((D.doubledOrbit_E322 h).le_sylow w.property))
  have hMHC : M ⊓ H ∈ Chapter1.He G := by
    have hc := pCoreIn_selfCentralizing_centralizer hMc
      (IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hw2)) hwM
    change (M ⊓ H) ⊓ centralizer ((M ⊓ H).pCoreIn 2 : Set G) ≤ (M ⊓ H).pCoreIn 2
    simpa only [H,DoubledBranch.pointCentralizer,zpowers_eq_closure,centralizer_closure] using hc
  have hMH : HasCharacteristicTwo (M ⊓ H : Subgroup G) := Chapter1.mem_He_iff.mp hMHC
  have hh := hMH.of_equiv
    (subgroupOfEquivOfLe (H := M ⊓ H) inf_le_right).symm
  exact hh.of_equiv (MulEquiv.subgroupCongr (inf_subgroupOf_right M H))

theorem doubleNatural_pure_component_identification_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ K : Subgroup (B.pointCentralizer w), IsComponent (B.pointCentralizer w) K →
        K.Normal ∧ (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧
          B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hp hfix K hK
  obtain ⟨J,⟨hJ,hXJ,hnJ⟩,_⟩ :=
    D.doubleNatural_pure_containing_component_of_many h hmany B S hs w hw hp hfix
  have he := DoubledBranch.SourceModel.pure_component_eq_containing S (D.doubledOrbit_normalizer_eq h B.orbit_eq)
    hns w hw hp (D.doubleNatural_pure_local_characteristicTwo_of_many h hmany B w hw)
    K J hK hJ hXJ
  subst J
  refine ⟨hnJ,hXJ,?_⟩
  have hm := map_mono (f := (B.pointCentralizer w).subtype) hXJ
  rw [map_subgroupOf_eq_of_le ((B.pointResidual_le w).trans inf_le_right)] at hm
  exact (DoubledBranch.SourceModel.pure_moving_le_residual S (D.doubledOrbit_normalizer_eq h B.orbit_eq) w hw hp).trans hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

