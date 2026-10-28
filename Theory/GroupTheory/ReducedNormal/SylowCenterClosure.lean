module

public import Theory.GroupTheory.ReducedNormal.Inheritance
public import Stellmacher.OmegaOneCenterMap

/-!
# Reduced closures of central Sylow seeds

An elementary central subgroup is reduced. Sylow inheritance then makes
its normal closure reduced whenever the closure is abelian. In a group
of characteristic two, the Sylow omega-center lies in the two-core and
centralizes it, so its full normal closure is elementary abelian.

This proves the reducedness assertion of B.2.14 on the literal omega-center
orbit, including its actual centralizer quotient. The commutator splitting
assertion is independent and is not used here.
Source: Aschbacher–Smith, Lemmas B.2.13–14, combined manuscript
of 1 March 2004, printed p.78.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A central elementary subgroup is reduced, with trivial conjugation quotient. -/
theorem isPReduced_of_le_center {p : ℕ} (Z : Subgroup G)
    [IsElementaryAbelian p Z] (hz : Z ≤ center G) : IsPReduced p Z := by
  let : Z.Normal := ⟨by
    intro z hz' g
    have hh := (mem_center_iff.mp (hz hz')) g
    simpa only [hh, mul_inv_cancel_right] using hz'⟩
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hc : centralizer (Z : Set G) = ⊤ := by
    apply top_unique
    intro g _ z hz'
    exact ((mem_center_iff.mp (hz hz')) g).symm
  apply bot_unique
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (Z : Set G)) x
  exact (QuotientGroup.eq_one_iff g).mpr (hc.symm ▸ mem_top g)

/-- Sylow inheritance constructs the reduced closure of a central elementary seed. -/
theorem isPReduced_normalClosure_of_sylow_central
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) (Z : Subgroup G) [IsElementaryAbelian p Z]
    (hZT : Z ≤ T) (hc : Z ≤ centralizer (T : Set G))
    [IsMulCommutative (normalClosure (Z : Set G))] :
    IsPReduced p (normalClosure (Z : Set G)) := by
  let E := Z.subgroupOf (T : Subgroup G)
  let : IsElementaryAbelian p E := IsElementaryAbelian.subgroupOf hZT
  have hEZ : E ≤ center (T : Subgroup G) := by
    intro z hz
    exact mem_center_iff.mpr fun t => Subtype.ext (hc hz t t.property)
  have hh := (isPReduced_of_le_center E hEZ).normalClosure_of_sylow_le
    T (T : Subgroup G) le_rfl E
  rw [map_subgroupOf_eq_of_le hZT] at hh
  exact hh (IsElementaryAbelian.normalClosure_of_isMulCommutative Z)

/-- The orbit of the Sylow omega-center is reduced in characteristic two. -/
theorem omegaCenter_normalClosure_reduced
    (T : Sylow 2 G) (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    IsPReduced 2 (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) := by
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hc : Z ≤ centralizer (T : Set G) := by
    intro z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hZQ : Z ≤ pCore 2 G := fun z hz => hchar
    (fun y hy => hc hz y (pCore_isPGroup.le_sylow_of_normal T hy))
  let W := normalClosure (Z : Set G)
  have hWQ : W ≤ pCore 2 G := normalClosure_le_normal hZQ
  have hWC : W ≤ centralizer (pCore 2 G : Set G) := normalClosure_le_normal
    (hc.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal T)))
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWC.trans (centralizer_le hWQ))
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  exact isPReduced_normalClosure_of_sylow_central T Z hZT hc

end Theory.GroupTheory
