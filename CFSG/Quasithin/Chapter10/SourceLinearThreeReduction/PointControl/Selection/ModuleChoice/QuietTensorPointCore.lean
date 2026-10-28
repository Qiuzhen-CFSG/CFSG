module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorCoordinates
public import Theory.Representation.BinaryTensorThree.PointFlag
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The original five-space in the tensor point centralizer

Transport the two invariant intervals of the point stabilizer through the
actual tensor marking. The five-space and the original point then satisfy
G.2.1 inside C_G(z). G.2.2 puts its entire normal closure in the point two-core
and gives the reduced central quotient with the original kernel retained.
Irreducibility of the upper layer identifies V intersect O₂(C_G(z)) with
this five-space whenever V is not already in the core.

This is the first reduction of 8.3.12; the contrary-case module argument
and the original tensor recognition remain source obligations.
Source: Aschbacher--Smith H.4.9(2), G.2.2 and 8.3.12, printed pp.384,332,726.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 Chapter8.Section03 Chapter1 BinaryTensorThree
variable {G : Type*} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private def tensorSubgroup (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
    (W : Submodule (ZMod 2) Space) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ D.fullModule, b (Additive.ofMul ⟨x,hx⟩) ∈ W}
  one_mem' := ⟨D.fullModule.one_mem,by
    change b 0 ∈ W
    rw [map_zero]
    exact W.zero_mem⟩
  mul_mem' := by
    rintro x y ⟨hx,hxW⟩ ⟨hy,hyW⟩
    refine ⟨D.fullModule.mul_mem hx hy,?_⟩
    change b (Additive.ofMul ⟨x,hx⟩ + Additive.ofMul ⟨y,hy⟩) ∈ W
    rw [map_add]
    exact W.add_mem hxW hyW
  inv_mem' := by
    rintro x ⟨hx,hxW⟩
    refine ⟨D.fullModule.inv_mem hx,?_⟩
    change b (-Additive.ofMul ⟨x,hx⟩) ∈ W
    rw [map_neg]
    exact W.neg_mem hxW

/-- The literal five-space in the original full module, including the point line. -/
def quietTensorFive (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) : Subgroup G :=
  tensorSubgroup D b PointFlag.five

theorem quietTensorFive_le (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) :
    quietTensorFive D b ≤ D.fullModule := fun _ h => h.choose

theorem mem_quietTensorFive (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) (v : D.fullModule) :
    (v : G) ∈ quietTensorFive D b ↔ b (Additive.ofMul v) ∈ PointFlag.five := by
  constructor
  · rintro ⟨_,h⟩; exact h
  · intro h; exact ⟨v.property,h⟩

private theorem point_line (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
    {z : G} (hz : z ∈ D.fullModule)
    (hb : b (Additive.ofMul ⟨z,hz⟩) = point) :
    tensorSubgroup D b PointFlag.line = zpowers z := by
  apply le_antisymm
  · rintro x ⟨hx,hh⟩
    rcases (PointFlag.mem_line_iff _).mp hh with h0 | h1
    · have he := b.injective (h0.trans b.map_zero.symm)
      have hx1 : x = 1 := congrArg (fun v : Additive D.fullModule => (v.toMul : G)) he
      rw [hx1]; exact one_mem _
    · have he := b.injective (h1.trans hb.symm)
      have hxz : x = z := congrArg (fun v : Additive D.fullModule => (v.toMul : G)) he
      rw [hxz]; exact mem_zpowers z
  · apply zpowers_le.mpr
    exact ⟨hz,(PointFlag.mem_line_iff _).mpr (Or.inr hb)⟩

private def image (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
    (A : Subgroup G) : AddSubgroup Space :=
  (A.subgroupOf D.fullModule).toAddSubgroup.map b.toAddMonoidHom

private theorem mem_image (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
    (A : Subgroup G) (v : Additive D.fullModule) :
    b v ∈ image D b A ↔ (v.toMul : G) ∈ A := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact b.injective he ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

private theorem image_subspace (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
    (W : Submodule (ZMod 2) Space) : image D b (tensorSubgroup D b W) = W.toAddSubgroup := by
  ext X
  obtain ⟨v,rfl⟩ := b.surjective X
  rw [mem_image]
  exact ⟨fun h => h.choose_spec,fun h => ⟨v.toMul.property,h⟩⟩

private theorem image_injective (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
    {A B : Subgroup G} (hA : A ≤ D.fullModule) (hB : B ≤ D.fullModule)
    (he : image D b A = image D b B) : A = B := by
  ext x
  constructor
  · intro hx
    exact (mem_image D b B (Additive.ofMul ⟨x,hA hx⟩)).mp
      (he ▸ (mem_image D b A (Additive.ofMul ⟨x,hA hx⟩)).mpr hx)
  · intro hx
    exact (mem_image D b A (Additive.ofMul ⟨x,hB hx⟩)).mp
      (he.symm ▸ (mem_image D b B (Additive.ofMul ⟨x,hB hx⟩)).mpr hx)

variable (q : localJoin T L →* PointParabolic.Actor) (hq : Function.Surjective q)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))

include hb hbz in
private theorem fixes_iff (a : localJoin T L) :
    action (PointParabolic.tensorHom (q a)) point = point ↔
      (a : G) ∈ centralizer ({z} : Set G) := by
  have he := hb a (Additive.ofMul ⟨z,hzV⟩)
  rw [quietTensorLinearAction_apply,hbz] at he
  rw [←he,←hbz,b.injective.eq_iff]
  change (Additive.ofMul _) = Additive.ofMul _ ↔ _
  rw [Additive.ofMul.injective.eq_iff,Subtype.ext_iff]
  change (a:G)*z*(a:G)⁻¹ = z ↔ _
  rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]

include hb hbz hzT in
/-- The original XT preserves the actual five-space. -/
theorem quiet_tensor_point_five_normalized :
    CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤ normalizer (quietTensorFive D b : Set G) := by
  rw [quiet_XT_eq_point_centralizer hzT]
  apply le_normalizer_iff.mpr
  rintro a ⟨ha,haz⟩ v ⟨hv,hv5⟩
  have hAN : localJoin T L ≤ normalizer (D.fullModule : Set G) :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule
  have hw : a*v*a⁻¹ ∈ D.fullModule := le_normalizer_iff.mp hAN a ha v hv
  refine ⟨hw,?_⟩
  have hh := PointFlag.preserves_five (PointParabolic.tensorHom (q ⟨a,ha⟩))
    ((fixes_iff D q b hb hzV hbz _).mpr haz) hv5
  rw [←hb,quietTensorLinearAction_apply] at hh
  exact hh

include hq hb hbz hzT in
private theorem image_stable {A : Subgroup G}
    (hA : CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤ normalizer (A : Set G)) :
    ∀ g : BinaryTensorThree.Group, action g point = point →
      ∀ X ∈ image D b A, action g X ∈ image D b A := by
  intro g hg X hX
  obtain ⟨c,hc⟩ := PointParabolic.actorEquiv.surjective g
  obtain ⟨a,ha⟩ := hq c
  have he : PointParabolic.tensorHom (q a) = g := by
    rw [ha,←PointParabolic.actorEquiv_apply,hc]
  have haz := (fixes_iff D q b hb hzV hbz a).mp (he ▸ hg)
  have haXT : (a : G) ∈ CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ := by
    rw [quiet_XT_eq_point_centralizer hzT]
    exact ⟨a.property,haz⟩
  obtain ⟨v,rfl⟩ := b.surjective X
  rw [←he,←hb,quietTensorLinearAction_apply,mem_image]
  exact le_normalizer_iff.mp hA a haXT v.toMul ((mem_image D b A v).mp hX)

include hq hb hbz hzT in
/-- The genuine lower invariant interval through the original point. -/
theorem quiet_tensor_point_lower_irreducible (A : Subgroup G)
    (hza : zpowers z ≤ A) (ha5 : A ≤ quietTensorFive D b)
    (hA : CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤ normalizer (A : Set G)) :
    A = zpowers z ∨ A = quietTensorFive D b := by
  have hl : PointFlag.line.toAddSubgroup ≤ image D b A := by
    rw [←image_subspace D b PointFlag.line,point_line D b hzV hbz]
    exact AddSubgroup.map_mono (show (zpowers z).subgroupOf D.fullModule ≤ A.subgroupOf D.fullModule
      from subgroupOf_mono _ hza)
  have hf : image D b A ≤ PointFlag.five.toAddSubgroup := by
    rw [←image_subspace D b PointFlag.five]
    exact AddSubgroup.map_mono (show A.subgroupOf D.fullModule ≤
      (quietTensorFive D b).subgroupOf D.fullModule from subgroupOf_mono _ ha5)
  have hzle : zpowers z ≤ D.fullModule := zpowers_le.mpr hzV
  rcases PointFlag.lower_irreducible (image D b A) hl hf
    (image_stable D q hq b hb hzV hbz hzT hA) with hh | hh
  · exact Or.inl (image_injective D b (ha5.trans (quietTensorFive_le D b)) hzle
      (hh.trans ((image_subspace D b PointFlag.line).symm.trans
        (congrArg (image D b) (point_line D b hzV hbz)))))
  · exact Or.inr (image_injective D b (ha5.trans (quietTensorFive_le D b))
      (quietTensorFive_le D b) (hh.trans (image_subspace D b PointFlag.five).symm))

include hq hb hbz hzT in
/-- The genuine upper invariant interval above the original five-space. -/
theorem quiet_tensor_point_upper_irreducible (A : Subgroup G)
    (h5a : quietTensorFive D b ≤ A) (haV : A ≤ D.fullModule)
    (hA : CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤ normalizer (A : Set G)) :
    A = quietTensorFive D b ∨ A = D.fullModule := by
  have hf : PointFlag.five.toAddSubgroup ≤ image D b A := by
    rw [←image_subspace D b PointFlag.five]
    exact AddSubgroup.map_mono (show (quietTensorFive D b).subgroupOf D.fullModule ≤
      A.subgroupOf D.fullModule from subgroupOf_mono _ h5a)
  rcases PointFlag.upper_irreducible (image D b A) hf
    (image_stable D q hq b hb hzV hbz hzT hA) with hh | hh
  · exact Or.inl (image_injective D b haV (quietTensorFive_le D b)
      (hh.trans (image_subspace D b PointFlag.five).symm))
  · apply Or.inr
    apply image_injective D b haV le_rfl
    rw [hh]
    symm
    apply top_unique
    intro X _
    obtain ⟨v,rfl⟩ := b.surjective X
    exact (mem_image D b D.fullModule v).mpr v.toMul.property

/-- The original marked five-space has binary rank five. -/
theorem quietTensorFive_rank (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) :
    rank (quietTensorFive D b) = 5 := by
  let c : quietTensorFive D b ≃ PointFlag.five :=
    { toFun := fun v => ⟨b (Additive.ofMul ⟨v,(quietTensorFive_le D b) v.property⟩),
        (mem_quietTensorFive D b _).mp v.property⟩
      invFun := fun w => ⟨(b.symm w.val).toMul,
        (mem_quietTensorFive D b _).mpr (by
          change b (b.symm w.val) ∈ PointFlag.five
          rw [b.apply_symm_apply]
          exact w.property)⟩
      left_inv := by intro v; apply Subtype.ext; exact congrArg (fun w : Additive D.fullModule =>
        (w.toMul : G)) (b.symm_apply_apply _)
      right_inv := by intro w; apply Subtype.ext; exact b.apply_symm_apply _ }
  rw [rank,Nat.card_congr c,Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod,PointFlag.finrank_five,Nat.log_pow Nat.one_lt_two]

/-- G.2 uses the original point line, local orbit, Sylow and point centralizer. -/
@[expose] def quietTensorPointFlagSetup (b : Additive D.fullModule ≃ₗ[ZMod 2] Space) (z : G) :
    ChapterG.Section02.Setup G :=
  ⟨quietTensorFive D b,zpowers z,localOrbit T L,(T : Subgroup G),centralizer ({z} : Set G)⟩

include hq hb hbz hzT in
/-- The hypotheses of G.2.1 are proved on the original marked tensor flag. -/
theorem quiet_tensor_point_flag_hypothesis (hz1 : z ≠ 1) :
    (quietTensorPointFlagSetup D b z).Hypothesis := by
  let s := quietTensorPointFlagSetup D b z
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hnorm : normalizer (zpowers z : Set G) = centralizer ({z} : Set G) :=
    normalizer_zpowers_eq_centralizer_of_order_two z hz2
  have hlocal : s.L₁ ⊔ s.T = d.XT := by
    have hI : s.L ⊓ s.G₁ = localOrbit T L ⊓ d.Gz :=
      congrArg (fun N : Subgroup G => localOrbit T L ⊓ N) hnorm
    have he := congrArg (fun I : Subgroup G => (pResidual 2 I).map I.subtype) hI
    exact congrArg (fun X : Subgroup G => X ⊔ (T : Subgroup G)) he
  have hz5 : zpowers z ≤ quietTensorFive D b := by
    rw [←point_line D b hzV hbz]
    rintro x ⟨hx,hh⟩
    exact ⟨hx,PointFlag.line_le_five hh⟩
  have hn5 := quiet_tensor_point_five_normalized D q b hb hzV hbz hzT
  have hchar := mem_He_iff.mp (twoLocal_mem_He_of_sylow_le T
    (D.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hzT)
  refine ⟨⟨IsElementaryAbelian.of_le (quietTensorFive_le D b),?_,hz5,D.orbit_residual,
    (quietTensorFive_le D b).trans (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)),
    ?_,le_sup_right.trans hn5,le_normalizer_componentOrbit L T,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · change zpowers z ≠ ⊥
    intro he
    have hh := mem_zpowers z
    rw [he,mem_bot] at hh
    exact hz1 hh
  · change (T : Subgroup G) ≤ normalizer (zpowers z : Set G)
    rwa [hnorm]
  · exact ⟨T.subtype le_sup_right,by
      rw [Sylow.coe_subtype]
      exact map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)⟩
  · change centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G)
    rw [hnorm]
  · rw [hlocal]
    exact sup_le (d.X_le.trans inf_le_right) hzT
  · exact ⟨T.subtype hzT,by rw [Sylow.coe_subtype]; exact map_subgroupOf_eq_of_le hzT⟩
  · exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr hchar
  · rw [hlocal]
    exact hn5
  · intro he
    change zpowers z = quietTensorFive D b at he
    obtain ⟨v,hv⟩ := b.surjective (leftProbe 0)
    have hv5 : (v.toMul : G) ∈ quietTensorFive D b := by
      apply (mem_quietTensorFive D b v.toMul).mpr
      change b v ∈ PointFlag.five
      rw [hv]
      intro i j hi hj
      simp [leftProbe,coordinates_tmul,basisVector,hj]
    have hline : b v ∈ PointFlag.line := by
      have hh : (v.toMul : G) ∈ tensorSubgroup D b PointFlag.line :=
        (point_line D b hzV hbz).symm ▸ (he.symm ▸ hv5)
      exact hh.choose_spec
    have hh := hline 1 0 (Or.inl (by decide))
    rw [hv] at hh
    norm_num [leftProbe,coordinates_tmul,basisVector] at hh
  · intro A hzA hA hnA
    rw [hlocal] at hnA
    exact quiet_tensor_point_lower_irreducible D q hq b hb hzV hbz hzT A hzA hA hnA

include hq hb hbz hzT in
/-- The whole original five-space closure lies in O₂(C_G(z)); G.2.2
also retains its actual central, reduced image modulo the original point. -/
theorem quiet_tensor_point_five_closure (hz1 : z ≠ 1) :
    let s := quietTensorPointFlagSetup D b z
    s.U ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      s.tilde s.U ≤ omegaOneAmbient ((center (s.tilde s.QH)).map (s.tilde s.QH).subtype) ∧
      IsPReduced 2 ((s.tilde s.U).subgroupOf (s.tilde s.H)) := by
  have h := quiet_tensor_point_flag_hypothesis D q hq b hb hzV hbz hzT hz1
  exact ⟨le_pCoreIn_of_normalizes h.U_isPGroup h.U_le_H
    (le_normalizer_conjugateSpanBy _ _),h.tilde_U_central.2,h.tilde_U_reduced⟩

include hb hbz hzT in
/-- Once G_z=K_zT is known, this is literally the source closure by K_z;
the original Sylow supplement preserves the five-space. -/
theorem quiet_tensor_point_five_closure_eq
    (hG : CentralizerSetup.Gz ⟨T,localOrbit T L,z⟩ =
      CentralizerSetup.KzT ⟨T,localOrbit T L,z⟩) :
    (quietTensorPointFlagSetup D b z).U = conjugateSpanBy (quietTensorFive D b)
      (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  change conjugateSpanBy (quietTensorFive D b) d.Gz = _
  rw [hG]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    (le_sup_right.trans (quiet_tensor_point_five_normalized D q b hb hzV hbz hzT))
    (hzT.trans (le_normalizer_conjugateSpanBy _ _))

include hq hb hbz hzT in
/-- In the contrary branch of 8.3.12 the five-space is exactly the original
module's intersection with the point two-core. -/
theorem quiet_tensor_point_core_intersection (hz1 : z ≠ 1)
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2) :
    D.fullModule ⊓ (centralizer ({z} : Set G)).pCoreIn 2 = quietTensorFive D b := by
  let Q := (centralizer ({z} : Set G)).pCoreIn 2
  have h5 : quietTensorFive D b ≤ Q :=
    (le_conjugateSpanBy _ _).trans
      (quiet_tensor_point_five_closure D q hq b hb hzV hbz hzT hz1).1
  have hXV : CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤
      normalizer (D.fullModule : Set G) := by
    rw [quiet_XT_eq_point_centralizer hzT]
    exact inf_le_left.trans
      ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
        D.maximalLocal_normalizes_fullModule)
  have hXQ : CentralizerSetup.XT ⟨T,localOrbit T L,z⟩ ≤ normalizer (Q : Set G) := by
    have hGQ : centralizer ({z} : Set G) ≤ normalizer (Q : Set G) := by
      simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
        using (pCore 2 (centralizer ({z} : Set G))).le_normalizer_map
          (centralizer ({z} : Set G)).subtype
    exact (sup_le ((CentralizerSetup.X_le _).trans inf_le_right) hzT).trans hGQ
  rcases quiet_tensor_point_upper_irreducible D q hq b hb hzV hbz hzT
    (D.fullModule ⊓ Q) (le_inf (quietTensorFive_le D b) h5) inf_le_left
    ((le_inf hXV hXQ).trans inf_normalizer_le_normalizer_inf) with he | he
  · exact he
  · exact (hcore (he.symm.le.trans inf_le_right)).elim

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
