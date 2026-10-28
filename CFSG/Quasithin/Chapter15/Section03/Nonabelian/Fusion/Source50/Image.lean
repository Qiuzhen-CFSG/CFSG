module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.AlmostSpecialIntersection

/-!
# The actual image of the centralizer span on V

Frattini containment in the central point makes the image of U elementary
abelian. The specified Sylow group normalizes that image. Commutator
generation of the two-perfect residual lifts through its own two-core;
no assumption that the full centralizer in M is a two-group is needed.

Source: Aschbacher–Smith, 15.3.51(2–3), printed p.1145.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50

variable {G : Type*} [Group G] [Finite G]

/-- Every nontrivial normal subgroup of the Sylow actor generates the
entire cubic residual by commutators. -/
theorem wreath_residual_commutator (P : Sylow 2 OrthogonalActor)
    (R : Subgroup OrthogonalActor) (hRP : R ≤ (P : Subgroup OrthogonalActor))
    (hPR : (P : Subgroup OrthogonalActor) ≤ normalizer (R : Set OrthogonalActor))
    (hR : R ≠ ⊥) : pResidual 2 OrthogonalActor = ⁅pResidual 2 OrthogonalActor,R⁆ := by
  obtain ⟨r,hr,_,hinv⟩ :=
    Theory.GroupTheory.WreathTwoResidual.exists_normal_sylow_inverter P R hRP hPR hR
  obtain ⟨e⟩ := Theory.GroupTheory.WreathTwoResidual.residual_equiv_elementaryNine
  have cube : ∀ x ∈ pResidual 2 OrthogonalActor, x ^ 3 = 1 := by
    intro x hx
    have cert : ∀ a : Multiplicative (Fin 2 → ZMod 3), a^3=1 := by decide +kernel
    have hx3 : (⟨x,hx⟩ : pResidual 2 OrthogonalActor)^3=1 := by
      apply e.injective
      rw [map_pow,map_one]
      exact cert _
    exact congrArg Subtype.val hx3
  apply le_antisymm ?_ (commutator_le_left _ _)
  intro x hx
  have hp : x*x*x=1 := by simpa only [pow_succ,pow_zero,one_mul] using cube x hx
  have he : x⁻¹*x⁻¹=x := by
    rw [← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right hp
  have hh : ⁅r,x⁆=x := by rw [commutatorElement_def,hinv x hx,he]
  rw [commutator_comm]
  exact hh ▸ commutator_mem_commutator hr hx

variable (d : CharacteristicTwo.LocalData G) (H : Subgroup G)
  (h : (⟨d.T,d.Y,d.V,d.ZS,d.Z,H⟩ : ChapterF.Section09.Setup G).Hypothesis)
include h

theorem span_image_le_sylow :
    d.action.image (localSpan d.ZS H) ≤ d.action.image d.T :=
  map_mono (comap_mono (h.UH_le_QH.trans h.QH_le_T))

theorem sylow_normalizes_span_image :
    d.action.image d.T ≤ normalizer (d.action.image (localSpan d.ZS H) : Set OrthogonalActor) := by
  have ht : (d.T : Subgroup G) ≤ normalizer (localSpan d.ZS H : Set G) :=
    h.T_le_H.trans (le_normalizer_conjugateSpanBy d.ZS H)
  exact (map_mono ((comap_mono ht).trans
    (le_normalizer_comap d.M.subtype))).trans (le_normalizer_map d.action.actor)

/-- The Frattini subgroup acts trivially on V because it lies in Z≤V. -/
theorem span_image_elementary : IsElementaryAbelian 2 (d.action.image (localSpan d.ZS H)) := by
  let U := localSpan d.ZS H
  have hUM : U ≤ d.M := h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le)
  let f : U →* OrthogonalActor := d.action.actor.comp (inclusion hUM)
  have hr : f.range = d.action.image U := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨⟨u,hUM u.property⟩,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu⟩,rfl⟩
  have hp : IsPGroup 2 U := d.T.isPGroup'.to_le (h.UH_le_QH.trans h.QH_le_T)
  let : Fact (IsPGroup 2 U) := ⟨hp⟩
  have hZV : d.Z ≤ d.V := le_conjugateSpanBy _ _
  let : IsElementaryAbelian 2 d.V := h.elementary
  have hf : frattini U ≤ f.ker := by
    intro u hu
    have hz : (u : G) ∈ d.Z := h.frattini_UH_le_point (mem_map_of_mem U.subtype hu)
    have hc : (u : G) ∈ centralizer (d.V : Set G) := d.V.le_centralizer (hZV hz)
    change d.action.actor ⟨u,hUM u.property⟩ = 1
    exact (show (⟨u,hUM u.property⟩ : d.M) ∈ d.action.actor.ker from
      by rw [d.action.ker_actor]; exact hc)
  have hs : ∀ u : U, f u ^ 2 = 1 := by
    intro u
    rw [← map_pow]
    exact hf (pth_power_mem_frattini_of_isPGroup (p := 2) u)
  have hc : ∀ a b : f.range, a * b = b * a := by
    intro a b
    have hsq : ∀ x : f.range, x ^ 2 = 1 := by
      rintro ⟨x,u,rfl⟩
      exact Subtype.ext (hs u)
    have hinv : ∀ x : f.range, x⁻¹ = x := by
      intro x
      exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsq x)
    calc
      a*b = (a*b)⁻¹ := (hinv _).symm
      _ = b*a := by rw [mul_inv_rev,hinv,hinv]
  have he : IsElementaryAbelian 2 f.range := {
    toIsMulCommutative := ⟨⟨hc⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      rintro ⟨x,u,rfl⟩
      exact Subtype.ext (hs u)) }
  exact hr ▸ he

/-- Lift Y=[Y,U] from the actual orthogonal image. Only the intersection
of the action kernel with Y is required to be its two-core. -/
theorem residual_commutator_of_image
    (hYn : d.M ≤ normalizer (d.Y : Set G))
    (hYC : d.Y ⊓ centralizer (d.V : Set G) = d.Y.pCoreIn 2)
    (hi : d.action.image d.Y =
      ⁅d.action.image d.Y, d.action.image (localSpan d.ZS H)⁆) :
    d.Y = ⁅d.Y, localSpan d.ZS H⁆ := by
  let U := localSpan d.ZS H
  let C := ⁅d.Y,U⁆
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hUM : U ≤ d.M := h.UH_le_QH.trans (h.QH_le_T.trans d.sylow_le)
  have hCY : C ≤ d.Y := le_normalizer_iff_commutator_le_left.mp (hUM.trans hYn)
  have hCM : C ≤ d.M := hCY.trans hYM
  have hmap : d.action.image d.Y = d.action.image C := by
    rw [show d.action.image C =
      ⁅d.action.image d.Y,d.action.image U⁆ from ?_]
    exact hi
    change (C.subgroupOf d.M).map d.action.actor =
      ⁅(d.Y.subgroupOf d.M).map d.action.actor,(U.subgroupOf d.M).map d.action.actor⁆
    rw [← map_commutator]
    congr 1
    apply map_injective d.M.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hYM,
      map_subgroupOf_eq_of_le hUM, map_subgroupOf_eq_of_le hCM]
  let : (C.subgroupOf d.Y).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)
  have hs' : (⊤ : Subgroup d.Y) ≤ C.subgroupOf d.Y ⊔ pCore 2 d.Y := by
    intro y _
    have hyim : d.action.actor ⟨y,hYM y.property⟩ ∈ d.action.image C :=
      hmap ▸ mem_map_of_mem d.action.actor y.property
    obtain ⟨c,hc,he⟩ := hyim
    let q : G := c⁻¹*(y : G)
    have hqY : q ∈ d.Y := d.Y.mul_mem (d.Y.inv_mem (hCY hc)) y.property
    have hqker : (⟨q,d.M.mul_mem (d.M.inv_mem c.property) (hYM y.property)⟩ : d.M) ∈
        d.action.actor.ker := by
      change d.action.actor (c⁻¹*⟨y,hYM y.property⟩) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hqC : q ∈ centralizer (d.V : Set G) := by
      rw [d.action.ker_actor] at hqker
      exact hqker
    have hqQ : q ∈ d.Y.pCoreIn 2 := hYC ▸ ⟨hqY,hqC⟩
    have hqQ' : (⟨q,hqY⟩ : d.Y) ∈ pCore 2 d.Y := by
      obtain ⟨q',hq',heq⟩ := hqQ
      exact (show q' = ⟨q,hqY⟩ from Subtype.ext heq) ▸ hq'
    have hm := mul_mem_sup
      (show (⟨c,hCY hc⟩ : d.Y) ∈ C.subgroupOf d.Y from hc) hqQ'
    have heq : (⟨c,hCY hc⟩ : d.Y)*⟨q,hqY⟩=y :=
      Subtype.ext (mul_inv_cancel_left _ _)
    exact heq ▸ hm
  have hp : IsPPerfect 2 (⊤ : Subgroup d.Y) :=
    (residualY_isPPerfect d.M d.Mc).of_surjective
      (topEquiv : (⊤ : Subgroup d.Y) ≃* d.Y).symm.toMonoidHom
      (topEquiv : (⊤ : Subgroup d.Y) ≃* d.Y).symm.surjective
  have hle := le_normal_of_isPPerfect_of_le_sup_pGroup (⊤ : Subgroup d.Y)
    (C.subgroupOf d.Y) (pCore 2 d.Y) hp pCore_isPGroup hs'
  apply le_antisymm ?_ hCY
  intro y hy
  exact hle (mem_top (⟨y,hy⟩ : d.Y))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
