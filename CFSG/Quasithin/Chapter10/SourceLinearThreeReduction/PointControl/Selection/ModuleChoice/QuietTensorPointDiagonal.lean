module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointCubic
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.AlternatingFiveSquareCubic

/-!
# The original diagonal-cubic point-core contradiction

The original cubic plane maps injectively through the full point two-core.
The natural eight-space decomposition selects an individual cubic in that
image and lifts it back to the same plane in X, hence in XT. It fixes no
nonzero vector in U/⟨z⟩, and its centralizer contains no nonidentity
involution in the literal K_z image. The original V-image lies there, so
both alternatives forced by H.4.12(1) are impossible.

The Source consumer constructs the natural decomposition and the original
cubic plane, and thereby proves V ≤ O₂(C_G(z)). No tensor coordinates or
full action kernels are replaced by numerical recognition.
Source: Aschbacher--Smith 8.3.12, printed p.726, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 Chapter8.Section03 Chapter1 Chapter1.XiEmbedding BinaryTensorThree
variable {G : Type*} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance quietTensorPointDiagonalFullModuleElementary : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
variable (q : localJoin T L →* PointParabolic.Actor) (hq : Function.Surjective q)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) (hz1 : z ≠ 1)

include hq hb hbz hzT hz1 in
/-- The individual diagonal cubic contradicts both original fixed-vector alternatives. -/
theorem quiet_tensor_point_diagonal_contradiction
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H))))
    (P : Subgroup G) (hPX : P ≤ CentralizerSetup.X ⟨T,localOrbit T L,z⟩)
    (eP : P ≃* Plane 3)
    (hAN : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      let π := QuotientGroup.mk' (pCore 2 d.Gz)
      (D.fullModule.subgroupOf d.Gz).map π ≤ (d.Kz.subgroupOf d.Gz).map π)
    (m : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      let N := (d.Kz.subgroupOf d.Gz).map (QuotientGroup.mk' (pCore 2 d.Gz))
      ChapterB.SourceInduction.AlternatingFiveSquare.NaturalEightDecomposition (σ.comp N.subtype)) :
    False := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let s := quietTensorPointFlagSetup D b z
  let π := QuotientGroup.mk' (pCore 2 s.H)
  let N := (d.Kz.subgroupOf s.H).map π
  have hPH : P ≤ s.H := hPX.trans (d.X_le.trans inf_le_right)
  let i : P →* s.H := inclusion hPH
  let f : P →* N := (π.comp i).codRestrict N (fun a =>
    mem_map_of_mem π (show i a ∈ d.Kz.subgroupOf s.H from d.X_le_Kz (hPX a.property)))
  let : IsElementaryAbelian 3 (Plane 3) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    have he : f.ker = (pCore 2 s.H).comap i := by
      ext a
      change f a = 1 ↔ i a ∈ pCore 2 s.H
      rw [←Subtype.coe_inj]
      exact QuotientGroup.eq_one_iff (i a)
    have htwo : IsPGroup 2 f.ker := by
      rw [he]
      exact (pCore_isPGroup (p := 2) (G := s.H)).comap_of_injective i (inclusion_injective hPH)
    have hthree : IsPGroup 3 f.ker := (IsElementaryAbelian.isPGroup 3 P).to_subgroup _
    simpa only [inf_idem] using (IsPGroup.disjoint_of_coprime htwo hthree (by decide)).eq_bot
  have hcard : Nat.card f.range = 9 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_congr eP.toEquiv]
    simp [Plane]
  have hcube : ∀ a ∈ f.range, a^3 = 1 := by
    rintro a ⟨x,rfl⟩
    rw [←map_pow,show x^3 = 1 from Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 3) (x:G) x.property),map_one]
  change ChapterB.SourceInduction.AlternatingFiveSquare.NaturalEightDecomposition (σ.comp N.subtype) at m
  obtain ⟨a,⟨p,hpa⟩,ha3,hfree,hcentral⟩ := m.exists_cubic f.range hcard hcube
  have hP3 : (p:G)^3 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 3) (p:G) p.property
  let ap : d.XT := ⟨p,(show d.X ≤ d.XT from le_sup_left) (hPX p.property)⟩
  have hVH := (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
  have hpH := (sup_le (d.X_le.trans inf_le_right) hzT) ap.property
  have hpa' : π ⟨ap,hpH⟩ = (a : s.H ⧸ pCore 2 s.H) := congrArg Subtype.val hpa
  rcases quiet_tensor_point_cubic_fixed_layers D q b hb hq hzV hbz hzT hz1 hcore σ c ap hP3 with
      ⟨v,hv,hcomm⟩ | ⟨v,hv,hfix⟩
  · let x : N := ⟨π ⟨v,hVH v.property⟩,hAN (mem_map_of_mem π v.property)⟩
    have hx2 : x^2 = 1 := by
      apply Subtype.ext
      change (π ⟨v,hVH v.property⟩)^2 = 1
      rw [←map_pow,show (⟨v,hVH v.property⟩ : s.H)^2 = 1 from
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v:G) v.property),map_one]
    have hax : Commute a x := by
      change a*x = x*a
      apply Subtype.ext
      change (a : s.H ⧸ pCore 2 s.H) * π ⟨v,hVH v.property⟩ =
        π ⟨v,hVH v.property⟩ * (a : s.H ⧸ pCore 2 s.H)
      rwa [hpa'] at hcomm
    exact hv (congrArg Subtype.val (hcentral x hx2 hax))
  · have hz := hfree (c.coordinates ⟨v,le_conjugateSpanBy _ _ v.property⟩).toAdd (by
      change σ (a : s.H ⧸ pCore 2 s.H) _ = _
      rwa [hpa'] at hfix)
    exact hv (Multiplicative.toAdd.injective hz)
end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
