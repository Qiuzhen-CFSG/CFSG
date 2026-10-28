module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.SchurLinear.InnerDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.SchurLinear.OuterDisplacement
public import Theory.Representation.SchurDisplacement
public import Theory.Representation.SL2.SchurOuterPeriod
public import Theory.Combinatorics.BinaryEvenOrbit
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic

/-!
# Degree of Schur-linear outer actors

The actual ambient Schur-linear actor forces the Schur degree of its marked
SL₂ restriction to divide half the defining degree. The existing binary
highest-weight parameters consequently have even repetition.

Inner involutions move at least half the binary module, and Schur-linear
outer involutions move at least a quarter, by the actual highest-weight and
paired-tensor calculations in the two displacement modules. For actor rank
greater than one, outer geometry supplies a nontrivial inner involution.
Rank at most one uses the outer estimate. Both give the coarse bound
`dim V ≤ 2*r + 4`; even repetition then forces `dim V = 2*r`.

The final assembly discharges both displacement premises on the original
ambient module. Its degree-window corollary retains the cubic-actor and rank
hypotheses of the Chapter K consumer, although the equality needs neither.

Source: Aschbacher--Smith, K.3.1, printed pp.451,453--454;
Guralnick--Malle, Classification of 2F-modules II, §3.5, equations (3.3)--(3.5),
manuscript p.20, and Proposition 4.1(2), p.22.
-/

public section

open scoped MatrixGroups MonoidAlgebra
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

include h e

omit [Finite G] [FiniteDimensional (ZMod 2) V] [Finite K] [CharP K 2] in
private theorem marked_action_nontrivial :
    ∃ g, ((ρ.comp L.subtype).comp e.symm.toMonoidHom) g ≠ 1 := by
  let g : SL(2,K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨g, fun hg => ?_⟩
  have hf : Function.Injective ((ρ.comp L.subtype).comp e.symm.toMonoidHom) :=
    h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hg1 : g = 1 := hf (hg.trans (map_one _).symm)
  have he := congrArg (fun a : SL(2,K) => a.val 0 1) hg1
  simp [g] at he

/-- The orbit parameters of the actual marked layer have even repetition
when an outer actor is linear over its endomorphism algebra. -/
theorem psl2_even_orbit_parameters_of_schurLinear_actor {r : ℕ}
    (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) (heven : Even r)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L)
    (hlin : ∀ t ∈ A, IsSchurLinear ρ L t) :
    let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    let s := schurDegree 2 σ
    0 < s ∧ ∃ t a : ℕ, 0 < t ∧ 0 < a ∧ Even t ∧ r = s * t ∧
      Module.finrank (ZMod 2) V = s * (2 ^ a) ^ t := by
  let σ : Representation (ZMod 2) SL(2,K) V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : L.Normal := h.layer_normal
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨x, hxA, hxL⟩ := SetLike.not_le_iff_exists.mp hAL
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxA
  have hdiv := Representation.SL2.schurDegree_dvd_half_of_outer_actor ρ L e
    (by omega : 0 < r) hc (h.psl2_centralizer_eq_bot e) x hx2 hxL (hlin x hxA)
  obtain ⟨hs, t, a, ht, ha, hrt, hv⟩ :=
    CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.exists_binary_orbit_parameters
      σ (h.marked_action_nontrivial e) r (by omega) hc
  refine ⟨hs, t, a, ht, ha, ?_, hrt, hv⟩
  obtain ⟨m, hm⟩ := hdiv
  have hmod : r % 2 = 0 := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp heven)
  have hhalf : r = 2 * (r / 2) := by omega
  refine ⟨m, ?_⟩
  change r / 2 = Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule) * m at hm
  nlinarith

/-- The source's Schur-linear actor has degree `2*r` once the inner and
outer involution displacement calculations are supplied. The unconditional
assembly below supplies both calculations. -/
theorem psl2_degree_eq_of_schurLinear_involution_bounds
    (hinner : ∀ x : G, x ∈ L → x ≠ 1 → x ^ 2 = 1 →
      Module.finrank (ZMod 2) V ≤
        2 * Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)))
    (houter : ∀ x : G, x ∉ L → x ^ 2 = 1 → IsSchurLinear ρ L x →
      Module.finrank (ZMod 2) V ≤
        4 * Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)))
    {r : ℕ} (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) (heven : Even r)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hd : fixedCodim ρ A ≤ 2 * rank A) (hAL : ¬ A ≤ L)
    (hlin : ∀ t ∈ A, IsSchurLinear ρ L t) :
    Module.finrank (ZMod 2) V = 2 * r := by
  let : IsElementaryAbelian 2 A := hA.2
  have hcoarse : Module.finrank (ZMod 2) V ≤ 2 * r + 4 := by
    have hgeom := h.psl2_outer_actor_rank e hr hc hA hAL
    by_cases hsmall : rank A ≤ 1
    · obtain ⟨x, hxA, hxL⟩ := SetLike.not_le_iff_exists.mp hAL
      have hx := houter x hxL (elemPow_eq_one_of_isElementaryAbelian x hxA) (hlin x hxA)
      have hdisp := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A hxA
      change Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) ≤ _ at hdisp
      omega
    · obtain ⟨x, hx, hx1⟩ := (A ⊓ L).bot_or_exists_ne_one.resolve_left
        (hgeom.2 (by omega))
      have hxbound := hinner x hx.2 hx1 (elemPow_eq_one_of_isElementaryAbelian x hx.1)
      have hdisp := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A hx.1
      change Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) ≤ _ at hdisp
      omega
  obtain ⟨hs, t, a, ht, ha, hteven, hrt, hv⟩ :=
    h.psl2_even_orbit_parameters_of_schurLinear_actor e hr hc heven hA hAL hlin
  have hnumeric := hcoarse
  rw [hv, hrt] at hnumeric
  obtain ⟨rfl, rfl⟩ := Nat.binary_even_orbit_of_coarse hs ht ha hteven hnumeric
  norm_num at hv hrt
  omega

/-- A Schur-linear outer ratio-two actor forces degree `2*r`. The inner
and outer displacement bounds are proved for the actual ambient action;
no tensor, recognition, or degree premise remains. -/
theorem psl2_degree_eq_of_schurLinear_actor {r : ℕ}
    (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) (heven : Even r)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    (hd : fixedCodim ρ A ≤ 2 * rank A) (hAL : ¬ A ≤ L)
    (hlin : ∀ t ∈ A, IsSchurLinear ρ L t) :
    Module.finrank (ZMod 2) V = 2 * r := by
  exact h.psl2_degree_eq_of_schurLinear_involution_bounds e
    (h.psl2_inner_involution_displacement e)
    (h.psl2_schur_outer_involution_displacement e hr hc)
    hr hc heven hA hd hAL hlin

/-- The Schur-linear branch of the Chapter K outer-actor degree window,
with the literal source actor and its full consumer hypotheses. -/
theorem psl2_degree_window_of_schurLinear_actor {r : ℕ}
    (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r) (heven : Even r)
    {A : Subgroup G} (hA : IsElementaryTwo A) (_hC : IsCubic ρ A)
    (hd : fixedCodim ρ A ≤ 2 * rank A) (_hR : rank A ≤ r) (hAL : ¬ A ≤ L)
    (hlin : ∀ t ∈ A, IsSchurLinear ρ L t) :
    Module.finrank (ZMod 2) V ≤ 2 * (r + 1) := by
  rw [h.psl2_degree_eq_of_schurLinear_actor e hr hc heven hA hd hAL hlin]
  omega

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
