module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.QuotientReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Action
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Generation
public import Theory.Quasithin.EvenCharacteristic

/-!
# Assembly of the intrinsic HS normalizer geometry

The structural calculation constructs the characteristic elementary eight in
the marked Sylow subgroup and proves characteristic two for its normalizer.
An inner involution fixing that Sylow pointwise is conjugation by `e0`.
Sylow conjugacy transports the normalizer, quotient, fixed subgroup, and full
automorphism invariance to every Sylow subgroup of the exact HS carrier.

The checked finite calculations prove surjectivity of the normalizer action
on the elementary eight and generation with `C(e0)`. The quotient reduction
identifies the action kernel with the two-core and constructs the actual
`SL_3(2)` quotient. The final theorem `geometry` combines these calculations
with Sylow transport to establish every field of `Geometry` without extra premises.
Source: Aschbacher–Smith 2.3.9(7), printed p.526; GLS3 Table 5.3m.
-/

public section
open Subgroup

namespace Sporadic.LeechRelated.HS.BlockNormalizer
open EvenLocalCandidates

private theorem map_congr_transport (K : Subgroup Carrier) (e β : MulAut Carrier) :
    (K.map (MulAut.congr e.symm β).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map β.toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change e (e.symm (β (e x))) = β (e x)
  exact e.apply_symm_apply _

private theorem fixedSubgroup_map_congr (e : MulAut Carrier) (α : MulAut Carrier) :
    (MulAut.congr e.symm α).fixedSubgroup.map e.toMonoidHom = α.fixedSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (MulAut.mem_fixedSubgroup α (e y)).mpr
    have hy' := (MulAut.mem_fixedSubgroup (MulAut.congr e.symm α) y).mp hy
    change e.symm (α (e y)) = y at hy'
    exact e.symm_apply_eq.mp hy'
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (MulAut.mem_fixedSubgroup (MulAut.congr e.symm α) (e.symm x)).mpr
    have hx' := (MulAut.mem_fixedSubgroup α x).mp hx
    change e.symm (α (e (e.symm x))) = e.symm x
    rw [e.apply_symm_apply, hx']

/-- Sylow conjugacy assembles the intrinsic geometry once the actual marked
quotient and centralizer generation calculations have been supplied. -/
theorem geometry_of_baseCalculations
    (hq : Nonempty ((baseNormalizer ⧸ pCore 2 baseNormalizer) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hgen : centralizer ({e0} : Set Carrier) ⊔ baseNormalizer = ⊤) : Geometry := by
  refine ⟨center_carrier_eq_bot, ?_⟩
  intro R α hα hi hfix
  obtain ⟨q⟩ := hq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier baseSylow R
  let e := MulAut.conj g
  have hR : subgroup.map e.toMonoidHom = R := congrArg Sylow.toSubgroup hg
  let δ := MulAut.congr e.symm α
  have hδorder : orderOf δ = 2 := ((MulAut.congr e.symm).orderOf_eq α).trans hα
  have hδinner : δ ∈ (MulAut.conj (G := Carrier)).range := by
    obtain ⟨a, rfl⟩ := hi
    exact ⟨e.symm a, (MulAut.congr_conj e.symm a).symm⟩
  have hδfix : ∀ r ∈ (baseSylow : Subgroup Carrier), δ r = r := by
    intro r hr
    have her : e r ∈ (R : Subgroup Carrier) := hR ▸ mem_map_of_mem e.toMonoidHom hr
    change e.symm (α (e r)) = r
    rw [hfix _ her, e.symm_apply_apply]
  have hδ : δ = MulAut.conj e0 := base_inner_eq_conj_e0 δ hδorder hδinner hδfix
  refine ⟨{
    localSubgroup := baseNormalizer.map e.toMonoidHom
    sylow_le := ?_
    invariant := ?_
    selfCentralizing := ?_
    quotientIso := ?_
    generated := ?_
  }⟩
  · rw [← hR]
    exact map_mono baseSylow_le_normalizer
  · intro β hβ
    have hb : subgroup.map (MulAut.congr e.symm β).toMonoidHom = subgroup := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_congr_transport, hR, hβ]
    rw [← map_congr_transport, baseNormalizer_invariant _ hb]
  · exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e baseNormalizer).mpr
      baseNormalizer_selfCentralizing
  · let f := e.subgroupMap baseNormalizer
    exact (QuotientGroup.congr (pCore 2 baseNormalizer)
      (pCore 2 (baseNormalizer.map e.toMonoidHom)) f (pCore_map_iso 2 f)).symm.trans q
  · have hh : δ.fixedSubgroup ⊔ baseNormalizer = ⊤ := by
      rw [hδ, MulAut.fixedSubgroup_conj]
      exact hgen
    have hm := congrArg (Subgroup.map e.toMonoidHom) hh
    rw [Subgroup.map_sup, fixedSubgroup_map_congr, map_top_of_surjective _ e.surjective] at hm
    exact hm

/-- The two concrete calculations suffice for the full source-facing geometry. -/
theorem geometry_of_action_and_generation
    (hact : Function.Surjective baseElementary.normalizerMonoidHom)
    (hgen : centralizer ({e0} : Set Carrier) ⊔ baseNormalizer = ⊤) : Geometry :=
  geometry_of_baseCalculations (baseNormalizer_quotient_of_surjective hact) hgen

/-- The exact degree-100 HS carrier is centerless and has the invariant
normalizer seed for every Sylow two-subgroup and inner involution fixing it
pointwise, with characteristic two, actual `SL_3(2)` quotient, and generation. -/
theorem geometry : Geometry :=
  geometry_of_action_and_generation baseNormalizer_action_surjective
    centralizer_sup_baseNormalizer_eq_top

end Sporadic.LeechRelated.HS.BlockNormalizer
