module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPointSpan
public import Theory.Representation.BinaryTensorThree.CubicFixed

/-!
# The individual cubic obstruction on both original point layers

Every element with cube one fixes at least eight vectors in the marked
nine-dimensional tensor module. Thus it fixes a vector outside the original
point line. In the contrary point-core branch, this vector either survives
in V O₂(G_z)/O₂(G_z), or belongs to V intersect O₂(G_z), which is the original
five-space. In the latter case its nonzero image is fixed in the literal
closure quotient U/⟨z⟩. Both actions and their full kernels are retained.

The Source consumer attaches this dichotomy to the completed eight-space
reduction. Recognition of its natural summands still must produce one
individual diagonal cubic excluding both alternatives. Fixing only the
whole cubic square does not give this contradiction.
Source: Aschbacher--Smith H.4.12(1) and 8.3.12, pp.385,726,
refs/quasithin.pdf.
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
variable (q : localJoin T L →* PointParabolic.Actor)
  (b : Additive D.fullModule ≃ₗ[ZMod 2] Space)
  (hb : ∀ (a : localJoin T L) (v : Additive D.fullModule),
    quietTensorLinearAction D b a (b v) = action (PointParabolic.tensorHom (q a)) (b v))

include hb in
private theorem fixed_iff (a : localJoin T L) (v : D.fullModule) :
    action (PointParabolic.tensorHom (q a)) (b (Additive.ofMul v)) = b (Additive.ofMul v) ↔
      (v : G) ∈ centralizer ({(a : G)} : Set G) := by
  rw [←hb,quietTensorLinearAction_apply,b.injective.eq_iff,
    Additive.ofMul.injective.eq_iff,Subtype.ext_iff]
  change (a:G)*(v:G)*(a:G)⁻¹ = (v:G) ↔ _
  rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff]
  exact eq_comm

include hb in
/-- Every original cubic fixes at least eight vectors, allowing its full action kernel. -/
theorem quiet_tensor_cubic_fixed_card (a : localJoin T L) (ha : (a:G)^3 = 1) :
    8 ≤ Nat.card (D.fullModule ⊓ centralizer ({(a:G)} : Set G) : Subgroup G) := by
  let C := D.fullModule ⊓ centralizer ({(a:G)} : Set G)
  let F := fixedSpace action (zpowers (PointParabolic.tensorHom (q a)))
  let e : C ≃ F := {
    toFun := fun v => ⟨b (Additive.ofMul ⟨v,v.property.1⟩),
      (mem_fixedSpace_zpowers_iff _ _ _).mpr ((fixed_iff D q b hb a _).mpr v.property.2)⟩
    invFun := fun w => ⟨(b.symm w.val).toMul,
      (b.symm w.val).toMul.property,(fixed_iff D q b hb a _).mp (by
        change action _ (b (b.symm w.val)) = b (b.symm w.val)
        rw [b.apply_symm_apply]
        exact (mem_fixedSpace_zpowers_iff _ _ _).mp w.property)⟩
    left_inv := by
      intro v
      apply Subtype.ext
      exact congrArg (fun w : Additive D.fullModule => (w.toMul : G)) (b.symm_apply_apply _)
    right_inv := by intro w; apply Subtype.ext; exact b.apply_symm_apply _ }
  rw [Nat.card_congr e]
  apply CubicFixed.cube_fixed_card_ge_eight
  rw [←map_pow,←map_pow,show a^3 = 1 from Subtype.ext ha,map_one,map_one]

include hb in
/-- A fixed point line cannot be the whole fixed space of an individual cubic. -/
theorem quiet_tensor_cubic_fixed_outside_point
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (a : localJoin T L) (ha : (a:G)^3 = 1) :
    ∃ v ∈ D.fullModule, v ∈ centralizer ({(a:G)} : Set G) ∧ v ∉ zpowers z := by
  have hc := quiet_tensor_cubic_fixed_card D q b hb a ha
  have hzcard : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hn : ¬ D.fullModule ⊓ centralizer ({(a:G)} : Set G) ≤ zpowers z := by
    intro hl
    have hh := card_le_of_le hl
    rw [hzcard] at hh
    omega
  obtain ⟨v,hv,hvz⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨v,hv.1,hv.2,hvz⟩

variable (hq : Function.Surjective q)
  {z : G} (hzV : z ∈ D.fullModule)
  (hbz : b (Additive.ofMul ⟨z,hzV⟩) = point)
  (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) (hz1 : z ≠ 1)

include hq hb hbz hzT hz1 in
/-- An individual cubic fixes a nonzero vector on at least one of the two
literal source layers. The lower witness comes from the original five-space,
inside its closure, and the upper witness uses the full point two-core. -/
theorem quiet_tensor_point_cubic_fixed_layers
    (hcore : ¬ D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2)
      ((quietTensorPointFlagSetup D b z).H ⧸ pCore 2 (quietTensorPointFlagSetup D b z).H) W)
    (c : Representation.BinaryConjugationSection (quietTensorPointFlagSetup D b z).H
      (quietTensorPointFlagSetup D b z).U (zpowers z)
      (σ.comp (QuotientGroup.mk' (pCore 2 (quietTensorPointFlagSetup D b z).H))))
    (a : CentralizerSetup.XT ⟨T,localOrbit T L,z⟩) (ha : (a:G)^3 = 1) :
    let s := quietTensorPointFlagSetup D b z
    let π := QuotientGroup.mk' (pCore 2 s.H)
    let hVH := (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
    let haH := (sup_le ((CentralizerSetup.X_le ⟨T,localOrbit T L,z⟩).trans inf_le_right) hzT) a.property
    (∃ v : D.fullModule, π ⟨v,hVH v.property⟩ ≠ 1 ∧
      π ⟨a,haH⟩ * π ⟨v,hVH v.property⟩ = π ⟨v,hVH v.property⟩ * π ⟨a,haH⟩) ∨
    (∃ v : quietTensorFive D b,
      c.coordinates ⟨v,le_conjugateSpanBy _ _ v.property⟩ ≠ 1 ∧
      σ (π ⟨a,haH⟩) (c.coordinates ⟨v,le_conjugateSpanBy _ _ v.property⟩).toAdd =
        (c.coordinates ⟨v,le_conjugateSpanBy _ _ v.property⟩).toAdd) := by
  dsimp only
  let s := quietTensorPointFlagSetup D b z
  let π := QuotientGroup.mk' (pCore 2 s.H)
  have haR : (a:G) ∈ localJoin T L := by
    exact ((quiet_XT_eq_point_centralizer (T := T) (L := L) hzT).le a.property).1
  obtain ⟨v,hv,hva,hvz⟩ := quiet_tensor_cubic_fixed_outside_point D q b hb hzV hz1 ⟨a,haR⟩ ha
  have hVH := (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)).trans hzT
  have haH := (sup_le ((CentralizerSetup.X_le ⟨T,localOrbit T L,z⟩).trans inf_le_right) hzT) a.property
  let av : s.H := ⟨a,haH⟩
  let vv : s.H := ⟨v,hVH hv⟩
  have hcomm : (a:G)*v = v*(a:G) := (mem_centralizer_singleton_iff.mp hva).symm
  by_cases hQ : v ∈ s.H.pCoreIn 2
  · right
    have hv5 : v ∈ quietTensorFive D b := by
      rw [←quiet_tensor_point_core_intersection D q hq b hb hzV hbz hzT hz1 hcore]
      exact ⟨hv,hQ⟩
    let u : s.U := ⟨v,le_conjugateSpanBy _ _ hv5⟩
    refine ⟨⟨v,hv5⟩,fun he => hvz ((c.coordinates_eq_one_iff u).mp he),?_⟩
    have he := c.equivariant av u
    have hh : (⟨av*u*(av:G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized av.property) u).mp u.property⟩ : s.U) = u := by
      apply Subtype.ext
      change (a:G)*v*(a:G)⁻¹ = v
      rw [hcomm,mul_inv_cancel_right]
    rw [hh] at he
    exact he.symm
  · left
    refine ⟨⟨v,hv⟩,?_,?_⟩
    · intro he
      exact hQ (mem_map_of_mem s.H.subtype ((QuotientGroup.eq_one_iff vv).mp he))
    · change π av * π vv = π vv * π av
      rw [←map_mul,←map_mul]
      exact congrArg π (Subtype.ext hcomm)
end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
