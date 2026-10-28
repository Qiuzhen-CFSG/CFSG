module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.Geometry
public import Theory.Representation.SL2.SchurOuterPeriod
public import Theory.Representation.SL2.SchurTensorDisplacement
public import Theory.Representation.SL2.SchurTensorDisplacement.HighestWeightPair

/-!
# Actual Schur-linear outer involutions: tensor reduction and descent

An outer actor of the self-centralizing marked SL₂ layer induces inner times
the literal half-degree Frobenius. Its Schur linearity forces the Schur degree
to divide that half-degree. The genuine highest-weight classification then
supplies a positive weight with the required half-period.

The coefficient-linear polynomial multiplication construction supplies its
paired tensor equivalence. The actual marked operator extends linearly,
squares to one, and intertwines this specific automorphism.
`SchurTensorDisplacement` identifies its displacement with tensor interchange
and descends through the original Schur field to the original binary space.
The resulting estimate has exactly the form of `houter` in
`psl2_degree_eq_of_schurLinear_involution_bounds`.

The final theorem discharges the paired highest-weight premise and proves
the ambient estimate without a degree window or recognition assumption.
Source: Aschbacher--Smith K.3.1, printed pp.451,453--454;
Guralnick--Malle, Classification of 2F-modules II, §3.5 and Proposition 4.1(2),
manuscript pp.20,22.
-/

public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v w
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type w} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

include h e
omit [Finite G] [FiniteDimensional (ZMod 2) V] [Finite K] [CharP K 2] in
private theorem outer_marked_nontrivial :
    ∃ g, ((ρ.comp L.subtype).comp e.symm.toMonoidHom) g ≠ 1 := by
  let g : SL(2,K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨g, fun hg => ?_⟩
  have hf : Function.Injective ((ρ.comp L.subtype).comp e.symm.toMonoidHom) :=
    h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hg1 : g = 1 := hf (hg.trans (map_one _).symm)
  have he := congrArg (fun a : SL(2,K) => a.val 0 1) hg1
  simp [g] at he

/-- The literal ambient estimate, conditional only on constructing the
paired highest-weight tensor. The final theorem below supplies that
construction; this reduction retains the operator identification and descent. -/
theorem psl2_schur_outer_displacement_of_paired_highestWeights
    {r : ℕ} (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r)
    (hpairs : Even r → ∀ (F : Type v) [Field F] [CharP F 2]
      (j : K →+* F) (n : ℕ), 0 < n → n < Nat.card K →
      (Nat.card K - 1) ∣ n * (2 ^ (r / 2) - 1) →
      ∃ d : ℕ, 2 ≤ d ∧ ∃ τ : Representation F SL(2,K) (Fin d → F),
        Nonempty ((Representation.SL2.highestWeightSpan j n).toRepresentation.Equiv
          (τ.tprod (τ.comp (Theory.PSL2.sl2FieldAut
            (iterateFrobeniusEquiv K 2 (r / 2))).toMonoidHom))))
    (x : G) (hxL : x ∉ L) (hx2 : x ^ 2 = 1) (hlin : IsSchurLinear ρ L x) :
    Module.finrank (ZMod 2) V ≤
      4 * Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  let σ : Representation (ZMod 2) SL(2,K) V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : L.Normal := h.layer_normal
  let a := MulAut.congr e (MulAut.conjNormal (H := L) x)
  have ha : a ^ 2 = 1 := by
    dsimp [a]
    rw [← map_pow, ← map_pow, hx2, map_one, map_one]
  have hout : a ∉ MulAut.innerSubgroup SL(2,K) := by
    intro hh
    change MulAut.congr e (MulAut.conjNormal (H := L) x) ∈ _ at hh
    rw [← MulAut.map_innerSubgroup_congr e, Subgroup.mem_map_equiv] at hh
    have hi : x ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := by
      change MulAut.conjNormal (H := L) x ∈ MulAut.innerSubgroup L
      simpa only [MulEquiv.symm_apply_apply] using hh
    rw [MulAut.conjNormal_comap_innerSubgroup, h.psl2_centralizer_eq_bot e,
      sup_bot_eq] at hi
    exact hxL hi
  obtain ⟨heven, c, hform⟩ := Theory.PSL2.sl2_outer_involution_formula
    (by omega : 0 < r) hc a ha hout
  let δ := Theory.PSL2.sl2FieldAut (iterateFrobeniusEquiv K 2 (r / 2))
  have hδ : δ ^ 2 = 1 := by
    have hhalf : r / 2 + r / 2 = r := by
      have := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp heven)
      omega
    ext g i j
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    change iterateFrobeniusEquiv K 2 (r / 2)
      (iterateFrobeniusEquiv K 2 (r / 2) (g.val i j)) = g.val i j
    simp only [iterateFrobeniusEquiv_def]
    rw [← pow_mul, ← pow_add, hhalf, ← hc]
    let : Fintype K := Fintype.ofFinite K
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card (g.val i j)
  have hsdiv := Representation.SL2.schurDegree_dvd_half_of_outer_actor ρ L e
    (by omega : 0 < r) hc (h.psl2_centralizer_eq_bot e) x hx2 hxL hlin
  obtain ⟨_, n, hn, _, hperiod, _, j, ⟨φ⟩⟩ :=
    CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.exists_binary_highestWeight_parameters
      σ (h.outer_marked_nontrivial e) r hc
  let E := Module.End (ZMod 2)[SL(2,K)] σ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Finite σ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) σ.asModule)
  let : Module.Finite E σ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars F σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep F
  have hperiodHalf : (Nat.card K - 1) ∣ n.val * (2 ^ (r / 2) - 1) :=
    hperiod.trans (Nat.mul_dvd_mul_left n.val (Nat.pow_sub_one_dvd_pow_sub_one 2 hsdiv))
  obtain ⟨d, hd, τ, ⟨ψ⟩⟩ := hpairs heven F j n.val hn n.isLt hperiodHalf
  let T := (schurLinearMarkedEquiv ρ L e.symm x hlin).toLinearMap
  have hTapply (v : σ.asModule) : σ.asModuleEquiv (T v) = ρ x (σ.asModuleEquiv v) := by
    change σ.asModuleEquiv (schurLinearMarkedEquiv ρ L e.symm x hlin v) = _
    rw [schurLinearMarkedEquiv_apply, σ.asModuleEquiv.apply_symm_apply]
  have hT2 : T * T = 1 := by
    apply LinearMap.ext
    intro v
    apply σ.asModuleEquiv.injective
    change σ.asModuleEquiv (T (T v)) = σ.asModuleEquiv v
    rw [hTapply, hTapply]
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hx2, map_one, Module.End.one_apply]
  have hT (g : SL(2,K)) : T * σ.endFieldRep g =
      σ.endFieldRep (c * δ g * c⁻¹) * T := by
    apply LinearMap.ext
    intro v
    have hh := schurLinearMarkedEquiv_intertwines ρ L e.symm x hlin g v
    change T (σ.endFieldRep g v) = σ.endFieldRep (a g) (T v) at hh
    rw [hform] at hh
    exact hh
  have hb := Representation.SL2.SchurTensorDisplacement.involution_bound_of_paired_scalarExtension
    (k := ZMod 2) σ.endFieldRep δ hδ c T hT2 hT hd τ (φ.trans ψ)
  have hmove := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv σ.asModuleEquiv
    (T.restrictScalars (ZMod 2)) (ρ x) (by
      intro v
      exact hTapply v)
  rwa [σ.asModuleEquiv.finrank_eq, hmove] at hb

/-- A Schur-linear outer involution of the actual marked SL₂ layer moves at
least a quarter of the original binary module. The half-period tensor pair
is constructed from the genuine highest weight, with no recognition or
degree-window premise. -/
theorem psl2_schur_outer_involution_displacement
    {r : ℕ} (hr : 2 ≤ r) (hc : Nat.card K = 2 ^ r)
    (x : G) (hxL : x ∉ L) (hx2 : x ^ 2 = 1) (hlin : IsSchurLinear ρ L x) :
    Module.finrank (ZMod 2) V ≤
      4 * Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  apply h.psl2_schur_outer_displacement_of_paired_highestWeights e hr hc
    (fun heven F _ _ j n hn hlt hperiod =>
      Representation.SL2.exists_highestWeight_pairedTensor j hr heven hc n hn hlt hperiod)
    x hxL hx2 hlin

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
