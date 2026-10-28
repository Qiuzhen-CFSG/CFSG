module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.Restriction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.OctonionLocals
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Coordinates

open Atlas.G2 Atlas.G2.Explicit Matrix
open scoped MatrixGroups
open Atlas.G2.ConwayRootFour.OctonionLocals

/-!
# Coordinates on the marked short-root displacement space

For a specified conjugator placing the actual marked involution in the C-root
family, the off-diagonal octonion coordinates identify its displacement space
with the first three coordinates. This proves equality with its fixed space
and constructs a genuine linear equivalence with K plus a two-dimensional
space. The A/B translations and C roots fix this space pointwise; the actual
SL₂ block acts as the identity on K and naturally on the two coordinates.
Thus the splitting is proved by the intertwiner, without a semisimplicity claim.

The final two theorems apply the same coordinates to the literal centralFour,
under its inclusion in the conjugate short-root group. GroupComparison supplies
that independent group calculation; this file neither assumes a dimension nor
asserts an abstract product isomorphism to be an equivariant comparison.

Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471, using B.4.6(6).
The explicit octonion formulas are from the attributed ATLAS modules imported
above; no additional upstream source is copied here.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction.CentralizerCoordinates

variable {K : Type*} [Field K] [CharP K 2]

def shortRootChart (g : Model K) : Natural.Space K ≃ₗ[K] (Fin 6 → K) :=
  coordinates.trans (action g⁻¹)

private theorem coordinates_action (h : Model K) (v : Natural.Space K) :
    coordinates (Natural.action K h v) = action h (coordinates v) := by
  rw [action_apply, LinearEquiv.symm_apply_apply]

theorem shortRootChart_conj (g h : Model K) (v : Natural.Space K) :
    shortRootChart g (Natural.action K (MulAut.conj g h) v) = action h (shortRootChart g v) := by
  change action g⁻¹ (coordinates (Natural.action K (MulAut.conj g h) v)) = _
  rw [coordinates_action]
  change (action g⁻¹ * action (MulAut.conj g h)) (coordinates v) =
    (action h * action g⁻¹) (coordinates v)
  rw [← map_mul, ← map_mul]
  congr 2
  simp [MulAut.conj_apply, mul_assoc]

private theorem root_difference (r : K) (v : Fin 6 → K) :
    action (rootC r) v - v = ![r^2*v 5,r*v 3,r*v 4,0,0,0] := by
  rw [action_rootC]
  ext i
  fin_cases i <;> simp

private theorem root_fixed_iff (r : K) (hr : r ≠ 0) (v : Fin 6 → K) :
    action (rootC r) v = v ↔ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  rw [← sub_eq_zero, root_difference]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Pi.zero_apply] at h0 h1 h2
    exact ⟨(mul_eq_zero.mp h1).resolve_left hr,
      (mul_eq_zero.mp h2).resolve_left hr,
      (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hr)⟩
  · rintro ⟨h3,h4,h5⟩
    ext i
    fin_cases i <;> simp [h3,h4,h5]

private theorem root_range_iff (r : K) (hr : r ≠ 0) (v : Fin 6 → K) :
    (∃ w, action (rootC r) w - w = v) ↔ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    simp [action_rootC]
  · rintro ⟨h3,h4,h5⟩
    refine ⟨![0,0,0,v 1/r,v 2/r,v 0/r^2], ?_⟩
    rw [root_difference]
    ext i
    fin_cases i <;> simp [h3,h4,h5] <;> field_simp

omit [CharP K 2] in
private theorem upper_form (v : Fin 6 → K) (h : v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0) :
    v = ![v 0,v 1,v 2,0,0,0] := by
  ext i
  fin_cases i <;> simp [h.1,h.2.1,h.2.2]

private theorem factor_action (p : Multiplicative (K × K)) (r : K) (M : SL(2,K))
    (s t u : K) :
    action (longRootHom p * rootC r * PairStabilizer.blockHom M)
      ![s,t,u,0,0,0] =
      ![s,M 0 0*t+M 0 1*u,M 1 0*t+M 1 1*u,0,0,0] := by
  rw [action_lift]
  ext i
  fin_cases i <;> simp [Natural.binaryOffDiagonal, liftSix,
    longRootHom, rootA, rootAEquiv, rootALinear, rootAApply,
    rootB, rootBEquiv, rootBLinear, rootBApply, rootC, rootCEquiv, rootCLinear,
    rootCApply, PairStabilizer.blockHom, PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear, CharTwo.neg_eq, CharTwo.sub_eq_add]

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction.CentralizerCoordinates

namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction.CentralizerCoordinates
open Subgroup Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
variable {K : Type*} [Field K] [CharP K 2]
open NaturalLocalAction Sporadic.LeechRelated.J2.InnerInvolutionCores
variable {G V : Type*} [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

theorem shortRootChart_carrier_a (g : Model K) (r : K)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) (v : Natural.Space K) :
    shortRootChart g (D.naturalCarrierKAction a v) = ConwayRootFour.OctonionLocals.action (rootC r) (shortRootChart g v) := by
  change shortRootChart g (Natural.action K (D.carrierEmbedding a) v) = _
  rw [he, shortRootChart_conj]

theorem mem_localW_shortRootChart (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) (v : Natural.Space K) :
    v ∈ D.localW ↔ shortRootChart g v 3 = 0 ∧ shortRootChart g v 4 = 0 ∧ shortRootChart g v 5 = 0 := by
  rw [← root_range_iff r hr]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨shortRootChart g w, ?_⟩
    rw [← D.shortRootChart_carrier_a g r he, ← map_sub]
    exact congrArg (shortRootChart g) hw
  · rintro ⟨w, hw⟩
    refine ⟨(shortRootChart g).symm w, ?_⟩
    apply (shortRootChart g).injective
    change shortRootChart g (D.naturalCarrierKAction a ((shortRootChart g).symm w) - (shortRootChart g).symm w) = _
    rw [map_sub, D.shortRootChart_carrier_a g r he, LinearEquiv.apply_symm_apply, hw]

theorem localW_eq_fixedSpace_a (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) :
    D.localW.toSubmodule.restrictScalars (ZMod 2) =
      fixedSpace D.naturalCarrierAction (zpowers a) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  change (v ∈ D.localW) ↔ D.naturalCarrierKAction a v = v
  rw [D.mem_localW_shortRootChart g r hr he, ← (shortRootChart g).injective.eq_iff,
    D.shortRootChart_carrier_a g r he, root_fixed_iff r hr]

private def localCoordinateMap (g : Model K) : D.localW.toSubmodule →ₗ[K] K × (Fin 2 → K) where
  toFun w := (shortRootChart g w.val 0, ![shortRootChart g w.val 1, shortRootChart g w.val 2])
  map_add' w z := by
    apply Prod.ext
    · simp
    · ext i; fin_cases i <;> simp
  map_smul' r w := by
    apply Prod.ext
    · simp
    · ext i; fin_cases i <;> simp

private theorem localCoordinateMap_bijective (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) :
    Function.Bijective (D.localCoordinateMap g) := by
  constructor
  · intro w z hwz
    apply Subtype.ext
    apply (shortRootChart g).injective
    have hw := (D.mem_localW_shortRootChart g r hr he w.val).mp w.property
    have hz := (D.mem_localW_shortRootChart g r hr he z.val).mp z.property
    have h0 := congrArg Prod.fst hwz
    have h1 := congrArg (fun v : K × (Fin 2 → K) => v.2 0) hwz
    have h2 := congrArg (fun v : K × (Fin 2 → K) => v.2 1) hwz
    change shortRootChart g w.val 0 = shortRootChart g z.val 0 at h0
    change shortRootChart g w.val 1 = shortRootChart g z.val 1 at h1
    change shortRootChart g w.val 2 = shortRootChart g z.val 2 at h2
    ext i
    fin_cases i <;> simp [h0,h1,h2,hw.1,hw.2.1,hw.2.2,hz.1,hz.2.1,hz.2.2]
  · intro v
    let w := (shortRootChart g).symm ![v.1,v.2 0,v.2 1,0,0,0]
    have hw : w ∈ D.localW := by
      rw [D.mem_localW_shortRootChart g r hr he]
      simp [w]
    refine ⟨⟨w,hw⟩, ?_⟩
    apply Prod.ext
    · simp [localCoordinateMap, w]
    · ext i; fin_cases i <;> simp [localCoordinateMap, w]

def localWCoordinates (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) :
    D.localW.toSubmodule ≃ₗ[K] K × (Fin 2 → K) :=
  LinearEquiv.ofBijective (D.localCoordinateMap g) (D.localCoordinateMap_bijective g r hr he)



theorem localWCoordinates_action_factor (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r))
    (x : E4 × A5) (p : Multiplicative (K × K)) (t : K) (M : SL(2,K))
    (hf : D.carrierEmbedding (centralizerEmbedding x) =
      MulAut.conj g (longRootHom p * rootC t * PairStabilizer.blockHom M))
    (w : D.localW.toSubmodule) :
    D.localWCoordinates g r hr he (D.localW.toRepresentation x w) =
      ((D.localWCoordinates g r hr he w).1,
        M.val *ᵥ (D.localWCoordinates g r hr he w).2) := by
  have hw := (D.mem_localW_shortRootChart g r hr he w.val).mp w.property
  have hc : shortRootChart g (D.localW.toRepresentation x w).val =
      ![shortRootChart g w.val 0,
        M 0 0 * shortRootChart g w.val 1 + M 0 1 * shortRootChart g w.val 2,
        M 1 0 * shortRootChart g w.val 1 + M 1 1 * shortRootChart g w.val 2, 0,0,0] := by
    rw [D.localW_action_val, hf, shortRootChart_conj, upper_form (shortRootChart g w.val) hw, factor_action]
    simp
  change (shortRootChart g (D.localW.toRepresentation x w).val 0,
    ![shortRootChart g (D.localW.toRepresentation x w).val 1,
      shortRootChart g (D.localW.toRepresentation x w).val 2]) = _
  rw [hc]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [localWCoordinates, localCoordinateMap,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem centralFour_root_action (g : Model K)
    (hC : centralFour.map D.carrierEmbedding ≤
      (ShortRootProducts.CentralizerCore.shortRootGroup (F := K)).map
        (MulAut.conj g).toMonoidHom)
    (c : Carrier) (hc : c ∈ centralFour) :
    ∃ t : K, D.carrierEmbedding c = MulAut.conj g (rootC t) := by
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hC (Subgroup.mem_map_of_mem D.carrierEmbedding hc)
  exact ⟨t.toAdd, ht.symm⟩

theorem localW_eq_centralFour_fixed (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r))
    (hC : centralFour.map D.carrierEmbedding ≤
      (ShortRootProducts.CentralizerCore.shortRootGroup (F := K)).map
        (MulAut.conj g).toMonoidHom) :
    D.localW.toSubmodule.restrictScalars (ZMod 2) =
      fixedSpace D.naturalCarrierAction centralFour := by
  apply le_antisymm
  · intro w hw
    change ∀ c : centralFour, D.naturalCarrierAction c w = w
    intro c
    obtain ⟨t,ht⟩ := D.centralFour_root_action g hC c c.property
    apply (shortRootChart g).injective
    change shortRootChart g (Natural.action K (D.carrierEmbedding c) w) = shortRootChart g w
    rw [ht, shortRootChart_conj, action_rootC]
    have hz := (D.mem_localW_shortRootChart g r hr he w).mp hw
    ext i
    fin_cases i <;> simp [hz.1,hz.2.1,hz.2.2]
  · intro w hw
    rw [D.localW_eq_fixedSpace_a g r hr he]
    exact (mem_fixedSpace_zpowers_iff _ a w).mpr (hw ⟨a, a_mem_centralFour⟩)

theorem localW_eq_centralFour_commutator (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r))
    (hC : centralFour.map D.carrierEmbedding ≤
      (ShortRootProducts.CentralizerCore.shortRootGroup (F := K)).map
        (MulAut.conj g).toMonoidHom) :
    D.localW.toSubmodule.restrictScalars (ZMod 2) =
      subspaceCommutator D.naturalCarrierAction ⊤ centralFour := by
  apply le_antisymm
  · rintro w ⟨v, hv⟩
    exact Submodule.subset_span ⟨a, a_mem_centralFour, v, Submodule.mem_top, hv.symm⟩
  · apply Submodule.span_le.mpr
    rintro w ⟨c,hc,v,_,rfl⟩
    obtain ⟨t,ht⟩ := D.centralFour_root_action g hC c hc
    change D.naturalCarrierKAction c v - v ∈ D.localW
    rw [D.mem_localW_shortRootChart g r hr he, map_sub]
    change (shortRootChart g (Natural.action K (D.carrierEmbedding c) v) - shortRootChart g v) 3 = 0 ∧
      (shortRootChart g (Natural.action K (D.carrierEmbedding c) v) - shortRootChart g v) 4 = 0 ∧
      (shortRootChart g (Natural.action K (D.carrierEmbedding c) v) - shortRootChart g v) 5 = 0
    rw [ht, shortRootChart_conj, root_difference]
    simp

end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
