module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment.Factors
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse

/-!
# Torus and field control with the solvable contained-offender base

The exact component Sylow normalizer embeds in the Borel of the whole
conjugate closure. The base-solvability proof makes this Borel prime to
three, and mutual normalization gives a trivial action on its Sylow
quotient. Cubic rigidity then forces every theta generator to centralize
the component, contradicting L = [L,Y₀].

The nonbinary PSL₂ and SL₃ calculations are reused directly. For derived
Sp₄ and G₂ we convert the published intrinsic torus rigidity to cubic
rigidity; the G₂ coverage theorem discharges its full automorphism premise.
All actual conjugate factors are retained in the normalizer calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
p.1144, proof of 15.3.49(k). The action adapters follow AutomorphismCollapse
with the base-solvability Borel control established in Containment.Setup.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment
open Subgroup ComponentReduction ModelReduction BorelInner
open AutomorphismCollapse ModelSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z E upper : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

lemma star_borel_eq_normalizer :
    (starImage H (relativeBorel L T)).subgroupOf (starImage H (localSpan L T)) =
      normalizer ((starImage H (sylowIntersection L T)).subgroupOf
        (starImage H (localSpan L T)) : Set (starImage H (localSpan L T))) := by
  rw [← ModelSelection.starProjection_map H (localSpan L T) (relativeBorel L T)
    d.closure_le inf_le_left]
  exact ModelSelection.starProjection_normalizer_map H (localSpan L T)
    (sylowIntersection L T) d.closure_le inf_le_right
    (closure_projection_ker_le_inter d)

/-- Noncontainment makes the actual Sylow image Y₀*-invariant. -/
lemma star_sylow_normalized (hout : ¬ Y0 ≤ localSpan L T) :
    starImage H Y0 ≤ normalizer (starImage H (sylowIntersection L T) :
      Set (H ⧸ pCore 2 H)) := by
  have hn := (replacement_sylow_intersection H M Y0 L T d.replacement d.placed.t_le_m
    d.placed.theta_eq d.normalizes d.component.commutator_eq d.quotient_card_in hout).2
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← starImage_commutator H (sylowIntersection L T) Y0
    (inf_le_right.trans d.closure_le)
    ((d.placed.theta_eq ▸ theta_le _).trans inf_le_right)]
  exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans hn)))

lemma star_borel_commutator_le [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    ⁅starImage H (relativeBorel L T), starImage H Y0⁆ ≤
      starImage H (sylowIntersection L T) := by
  rw [← starImage_commutator H (relativeBorel L T) Y0
    (inf_le_left.trans d.closure_le)
    ((d.placed.theta_eq ▸ theta_le _).trans inf_le_right)]
  exact map_mono (comap_mono (borel_control d hout).2.2.2.2.2)

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
    (LieBorels.factor (H := H) (L := L) (T := T)) (factor_commute d hq)
    (factor_sup d) (closureSylow d) C
  let e : LieBorels.factor C ≃* C.val :=
    subgroupOfEquivOfLe (conjugateFactors_properties d C.val C.property).2.1
  let P : Sylow 2 C.val := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup C.val) = (R : Subgroup (LieBorels.factor C)).map e.toMonoidHom := rfl
  refine ⟨P, ?_, ?_⟩
  · intro x
    change x ∈ (P : Subgroup C.val) ↔ _
    rw [hP, mem_map_equiv, hR, closureSylow_coe]
    rfl
  · intro x hx
    have heN := R.normalizer_map_surjective e.toMonoidHom e.surjective
    change (normalizer (R : Set (LieBorels.factor C))).map e.toMonoidHom =
      normalizer (P : Set C.val) at heN
    rw [← heN] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hw := hN (mem_map_of_mem (LieBorels.factor C).subtype hz)
    change (z : starImage H (localSpan L T)) ∈ normalizer
      ((closureSylow d : Subgroup (starImage H (localSpan L T))) :
        Set (starImage H (localSpan L T))) at hw
    rw [closureSylow_coe] at hw
    change (z : starImage H (localSpan L T)) ∈ normalizer
      ((starImage H (sylowIntersection L T)).subgroupOf
        (starImage H (localSpan L T)) : Set (starImage H (localSpan L T))) at hw
    rw [← star_borel_eq_normalizer d] at hw
    exact hw


/-- The actual star Borel inherits the order bound before any factor is selected. -/
theorem star_borel_three_free [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    ¬ 3 ∣ Nat.card (starImage H (relativeBorel L T)) := by
  have hB := (borel_control d hout).2.2.2.1
  exact fun h => hB (h.trans (card_dvd_of_surjective
    (starProjection H (relativeBorel L T) (inf_le_left.trans d.closure_le))
    (starProjection_surjective H (relativeBorel L T) (inf_le_left.trans d.closure_le))))

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
  rw [← star_theta_eq_self H M Y0 d.placed.theta_eq]
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
The model calculations in `exponent_eq_one` discharge intrinsic rigidity. -/
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
  rw [← starImage_commutator H L Y0 d.l_le
    ((d.placed.theta_eq ▸ theta_le _).trans inf_le_right), ← d.component.commutator_eq] at hc
  exact component_star_nontrivial H L L d.component_in_H le_rfl hc


omit d in
private theorem cubicRigid_of_torusRigid {D : Type*} [Group D] [Finite D]
    (h : RankTwoField.TorusRigid D) : MulAut.CubicBorelRigid D := by
  intro P hthree a ha hP hB
  have hmap : (P : Subgroup D).map a.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨y, hy, rfl⟩
      exact hP y hy
    · exact (Nat.card_congr (P.equivMapOfInjective a.toMonoidHom a.injective).toEquiv).le
  have hdisp (b : D) (hb : b ∈ normalizer (P : Set D)) : b⁻¹ * a b ∈ P := by
    have hx := (P : Subgroup D).inv_mem (hB b⁻¹ ((normalizer (P : Set D)).inv_mem hb))
    change b⁻¹ * a b ∈ (P : Subgroup D)
    simpa only [map_inv, inv_inv, mul_inv_rev] using hx
  obtain ⟨g, hg⟩ := h P a hmap hdisp
  have hgN : g ∈ normalizer (P : Set D) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hg]
    exact hmap
  let I := (normalizer (P : Set D)).map (MulAut.conj : D →* MulAut D)
  have haI : a ∈ I := ⟨g, hgN, hg⟩
  have hI : ¬ 3 ∣ Nat.card I := fun hd =>
    hthree (hd.trans ((normalizer (P : Set D)).card_map_dvd _))
  have hd : orderOf (⟨a, haI⟩ : I) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext ha)
  have ho : orderOf (⟨a, haI⟩ : I) = 1 :=
    ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_right
      (fun he => hI (he ▸ orderOf_dvd_natCard _))
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp ho)

/-- All nonbinary fields are excluded by the actual source Borel action. -/
theorem exponent_eq_one [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) {e : ℕ}
    (hmodel : LieComponentModel (starImage H L) e) : e = 1 := by
  have hq := d.component.quasisimple
  cases hmodel with
  | linear_two he F hF model =>
    obtain ⟨f⟩ := model
    exact (false_of_cubicBorelRigid d hq hout
      ((Matrix.ProjectiveSpecialLinearGroup.cubicBorelRigid F e he hF).of_mulEquiv f)).elim
  | linear_three he F hF model =>
    by_contra hne
    obtain ⟨f⟩ := model
    exact false_of_cubicBorelRigid d hq hout
      ((Matrix.PSL3.CubicBorelRigidity.specialLinear F (by omega) hF).of_mulEquiv f)
  | symplectic he F hF model =>
    by_contra hne
    obtain ⟨f⟩ := model
    exact false_of_cubicBorelRigid d hq hout
      (cubicRigid_of_torusRigid ((RankTwoField.derived_symplectic_torusRigid hF
        (by omega)).of_equiv f))
  | g2 he F hF model =>
    by_contra hne
    obtain ⟨f⟩ := model
    let _ := Fintype.ofFinite F
    let _ : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hcard : 2 < Nat.card F := by
      rw [hF]
      exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega : 1 < e)
    exact false_of_cubicBorelRigid d hq hout
      (cubicRigid_of_torusRigid ((RankTwoField.derived_g2_torusRigid_of_coverage hcard
        (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hcard)).of_equiv f))
  | binary_linear he _ _ _ => exact he

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment
