module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.TorusControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.LieBorels
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.FactorControl
public import Theory.GroupAction.CubicBorelRigidity
public import Theory.SpecificGroups.PSL2.CubicBorelRigidity
public import Theory.SpecificGroups.PSL3.CubicBorelRigidity

/-!
# Nonbinary linear exclusions through intrinsic cubic rigidity

For every actual T-conjugate star component, the intersection with T₀*
is a Sylow two-subgroup, and its entire intrinsic normalizer embeds in B*.
The commuting-family normalizer theorem retains all factors and allows
central intersections. Thus the source three-free bound passes to each
factor normalizer, while the source action fixes its quotient by the Sylow.

If the component satisfies `MulAut.CubicBorelRigid`, every order-three
generator of Y₀* centralizes it. Theta generation then contradicts the
source identity L = [L,Y₀] and the nontrivial component image. No equality
L₀ = L, centerlessness, inner action, or field specialization is assumed.

The checked cubic Borel rigidity calculations for the actual nonbinary PSL₂
and SL₃ carriers transport through the supplied model equivalences. Thus
`false_of_linear_two` and `false_of_linear_three` exclude both alternatives
under the source noncontainment and solvable-Borel hypotheses. The SL₃
calculation retains its center and does not replace its carrier by PSL₃.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
`refs/quasithin.pdf`, printed p.1144, proof of 15.3.49(k), with the group
alternatives of B.4.2, B.5.1 and B.5.6 on printed pp.86, 99 and 105.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.LinearField
open ModelSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- Every conjugate retains its exact Sylow intersection and its full
intrinsic normalizer inside the source star Borel. -/
theorem conjugate_sylow_borel_data
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (C : ↥(conjugateFactors H L T)) :
    ∃ P : Sylow 2 C.val,
      (∀ x : C.val, x ∈ P ↔ (x : H ⧸ pCore 2 H) ∈ starImage H (sylowIntersection L T)) ∧
      (∀ x : C.val, x ∈ normalizer (P : Set C.val) →
        (x : H ⧸ pCore 2 H) ∈ starImage H (relativeBorel L T)) := by
  classical
  let _ := Fintype.ofFinite ↥(conjugateFactors H L T)
  obtain ⟨R, hR, hN⟩ := Sylow.factor_normalizer_control
    (LieBorels.factor (H := H) (L := L) (T := T)) (LieBorels.factor_commute d hq)
    (LieBorels.factor_sup d) (LieBorels.closureSylow d) C
  let e : LieBorels.factor C ≃* C.val :=
    subgroupOfEquivOfLe (conjugateFactors_properties d C.val C.property).2.1
  let P : Sylow 2 C.val := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup C.val) = (R : Subgroup (LieBorels.factor C)).map e.toMonoidHom := rfl
  refine ⟨P, ?_, ?_⟩
  · intro x
    change x ∈ (P : Subgroup C.val) ↔ _
    rw [hP, mem_map_equiv, hR, LieBorels.closureSylow_coe]
    rfl
  · intro x hx
    have heN := R.normalizer_map_surjective e.toMonoidHom e.surjective
    change (normalizer (R : Set (LieBorels.factor C))).map e.toMonoidHom =
      normalizer (P : Set C.val) at heN
    rw [← heN] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hw := hN (mem_map_of_mem (LieBorels.factor C).subtype hz)
    change (z : starImage H (localSpan L T)) ∈ normalizer
      ((LieBorels.closureSylow d : Subgroup (starImage H (localSpan L T))) :
        Set (starImage H (localSpan L T))) at hw
    rw [LieBorels.closureSylow_coe] at hw
    change (z : starImage H (localSpan L T)) ∈ normalizer
      ((starImage H (sylowIntersection L T)).subgroupOf
        (starImage H (localSpan L T)) : Set (starImage H (localSpan L T))) at hw
    rw [← star_borel_eq_normalizer d] at hw
    exact hw


/-- The actual star Borel inherits the order bound before any factor is selected. -/
theorem star_borel_three_free [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    ¬ 3 ∣ Nat.card (starImage H (relativeBorel L T)) := by
  have hB := (d.borel_control (relativeBorel L T) hout rfl).2.2.2.1
  exact fun h => hB (h.trans (card_dvd_of_surjective
    (starProjection H (relativeBorel L T) (inf_le_left.trans (closure_le d)))
    (starProjection_surjective H (relativeBorel L T) (inf_le_left.trans (closure_le d)))))

/-- The source action on any one of the actual conjugate components is
trivial as soon as the intrinsic cubic model calculation is available. -/
theorem conjugate_centralizes_of_cubicBorelRigid
    [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    (C : ↥(conjugateFactors H L T)) (hrigid : MulAut.CubicBorelRigid C.val) :
    ⁅C.val, starImage H Y0⁆ = ⊥ := by
  obtain ⟨P, hP, hN⟩ := conjugate_sylow_borel_data d hq C
  let N := normalizer (P : Set C.val)
  let B := starImage H (relativeBorel L T)
  let f : N →* B := (C.val.subtype.comp N.subtype).codRestrict B
    (fun x => hN x x.property)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun z : B => z.val) h
    change x.val.val = y.val.val at hh
    exact hh
  have hthree : ¬ 3 ∣ Nat.card N := fun h =>
    star_borel_three_free d hout (h.trans (card_dvd_of_injective f hf))
  have hCY := (conjugateFactors_properties d C.val C.property).2.2.1
  let r : starImage H Y0 →* normalizer (C.val : Set (H ⧸ pCore 2 H)) :=
    (starImage H Y0).subtype.codRestrict _ (fun y => hCY y.property)
  let α : starImage H Y0 →* MulAut C.val := C.val.normalizerMonoidHom.comp r
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  rw [← star_theta_eq_self H M Y0 d.theta_eq]
  apply (Subgroup.closure_le _).mpr
  rintro y ⟨hy, hy3⟩
  let y0 : starImage H Y0 := ⟨y, hy⟩
  have hy0 : y0 ^ 3 = 1 := Subtype.ext (hy3 ▸ pow_orderOf_eq_one y)
  have ha3 : α y0 ^ 3 = 1 := by rw [← map_pow, hy0, map_one]
  have ha := hrigid P hthree (α y0) ha3 (by
    intro x hx
    apply (hP _).mpr
    change y * (x : H ⧸ pCore 2 H) * y⁻¹ ∈ starImage H (sylowIntersection L T)
    exact (mem_normalizer_iff.mp (star_sylow_normalized d hout hy) x).mp
      ((hP x).mp hx)) (by
    intro x hx
    apply (hP _).mpr
    change y * (x : H ⧸ pCore 2 H) * y⁻¹ * (x : H ⧸ pCore 2 H)⁻¹ ∈
      starImage H (sylowIntersection L T)
    have hb := star_borel_commutator_le d hout
    rw [commutator_comm] at hb
    exact hb (commutator_mem_commutator hy (hN x hx)))
  intro x hx
  have hh := congrArg (fun a : MulAut C.val =>
    (a ⟨x, hx⟩ : H ⧸ pCore 2 H)) ha
  change y * x * y⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The cubic model calculation contradicts the source component generation.
The intrinsic rigidity premise is a separate model obligation. -/
theorem false_of_cubicBorelRigid
    [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    (hrigid : MulAut.CubicBorelRigid (starImage H L)) : False := by
  have hmem : starImage H L ∈ conjugateFactors H L T :=
    mem_conjugateFactors.mpr ⟨1, by
      have he : (MulAut.conj ((1 : T) : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [he, Subgroup.map_id]⟩
  have hc := conjugate_centralizes_of_cubicBorelRigid d hq hout
    ⟨starImage H L, hmem⟩ hrigid
  change ⁅starImage H L, starImage H Y0⁆ = ⊥ at hc
  rw [← starImage_commutator H L Y0 (component_le d)
    ((d.theta_eq ▸ theta_le _).trans inf_le_right), ← d.commutator_eq] at hc
  exact component_star_nontrivial H L L d.component_in_H le_rfl hc

/-- The nonbinary PSL₂ alternative is incompatible with source noncontainment.
The equivalence identifies the actual star component with the matrix carrier. -/
theorem false_of_linear_two
    [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {F : Type*} [Field F] [Finite F] {e : ℕ} (he : 2 ≤ e)
    (hF : Nat.card F = 2 ^ e)
    (model : Nonempty (starImage H L ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) : False := by
  obtain ⟨f⟩ := model
  exact false_of_cubicBorelRigid d hq hout
    ((Matrix.ProjectiveSpecialLinearGroup.cubicBorelRigid F e he hF).of_mulEquiv f)

/-- The nonbinary SL₃ alternative is incompatible with source noncontainment,
including fields whose special linear group has nontrivial center. -/
theorem false_of_linear_three
    [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {F : Type*} [Field F] [Finite F] {e : ℕ} (he : 1 < e)
    (hF : Nat.card F = 2 ^ e)
    (model : Nonempty (starImage H L ≃*
      Matrix.SpecialLinearGroup (Fin 3) F)) : False := by
  obtain ⟨f⟩ := model
  exact false_of_cubicBorelRigid d hq hout
    ((Matrix.PSL3.CubicBorelRigidity.specialLinear F he hF).of_mulEquiv f)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.LinearField
