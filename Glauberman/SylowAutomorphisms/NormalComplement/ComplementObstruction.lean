module

public import Glauberman.SylowAutomorphisms.NormalComplement.InvariantComplement
public import Glauberman.SylowAutomorphisms.NormalComplement.Contracts
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The complement obstruction in the actual semidirect product

A base-group element normalizing a subgroup of the actor factor must fix
that subgroup pointwise: project its conjugates to the actor factor.
Combined with the relative averaging argument, this is the final contradiction
in Glauberman's normal-complement proof. The Sylow-invariant complement,
local normalizers and source mover remain explicit geometric premises.

The subgroup of actors is literally the image under `SemidirectProduct.inr`;
the base subgroup is literally the range of `SemidirectProduct.inl`.

Source: Glauberman, Math. Z. 93 (1966), proof of Theorem 1(b), p.158,
DOI 10.1007/BF01111033.
-/

public section

namespace Glauberman.SylowAutomorphisms.NormalComplement

open Subgroup SemidirectProduct

variable {G A : Type*} [Group G] [Group A]

/-- Normalization by a base-group element forces pointwise fixation of actors. -/
theorem actor_fixed_of_base_normalizer (φ : A →* MulAut G)
    (U : Subgroup A) (h : G ⋊[φ] A)
    (hbase : h ∈ (inl : G →* G ⋊[φ] A).range)
    (hnorm : h ∈ normalizer (U.map (inr : A →* G ⋊[φ] A) : Set (G ⋊[φ] A)))
    (u : A) (hu : u ∈ U) : h * inr u * h⁻¹ = inr u := by
  have hm : h * inr u * h⁻¹ ∈ U.map (inr : A →* G ⋊[φ] A) :=
    (mem_normalizer_iff.mp hnorm _).mp (mem_map.mpr ⟨u, hu, rfl⟩)
  obtain ⟨v, _, hv⟩ := mem_map.mp hm
  have hr : (rightHom : G ⋊[φ] A →* A) h = 1 := by
    rwa [range_inl_eq_ker_rightHom] at hbase
  have hvu : v = u := by
    simpa only [map_mul, map_inv, rightHom_inr, hr, one_mul, inv_one, mul_one]
      using congrArg (rightHom : G ⋊[φ] A →* A) hv
  exact hv.symm.trans (congrArg inr hvu)

/-- Apply Lemma 4 to the actual actor displacement subgroup in a semidirect
product. A mover in the base group and the local normalizer J fixes that subgroup.
The source fusion configuration must still supply the displayed premises. -/
theorem actor_fixed_of_complement_geometry [Finite G] [Finite A]
    (φ : A →* MulAut G) (d : OddDisplacement A)
    (J V W : Subgroup (G ⋊[φ] A)) [IsElementaryAbelian 2 V]
    (hJV : J ≤ normalizer (V : Set (G ⋊[φ] A)))
    (hJW : J ≤ normalizer (W : Set (G ⋊[φ] A)))
    (hUV : d.subgroup.map (inr : A →* G ⋊[φ] A) ≤ V)
    (hcompl : IsCompl (W.subgroupOf V)
      ((d.subgroup.map (inr : A →* G ⋊[φ] A)).subgroupOf V))
    (P : Sylow 2 J)
    (hPU : ∀ a : J, a ∈ P → (a : G ⋊[φ] A) ∈
      normalizer (d.subgroup.map (inr : A →* G ⋊[φ] A) : Set (G ⋊[φ] A)))
    (hxJ : (inr d.actor : G ⋊[φ] A) ∈ J)
    (hxW : (inr d.actor : G ⋊[φ] A) ∈ centralizer (W : Set (G ⋊[φ] A)))
    (h : G ⋊[φ] A) (hhJ : h ∈ J)
    (hhG : h ∈ (inl : G →* G ⋊[φ] A).range)
    (u : A) (hu : u ∈ d.subgroup) : h * inr u * h⁻¹ = inr u := by
  let : Finite (G ⋊[φ] A) := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  apply actor_fixed_of_base_normalizer φ d.subgroup h hhG _ u hu
  apply normalizes_of_surjective_displacement J V W
    (d.subgroup.map (inr : A →* G ⋊[φ] A)) hJV hJW hUV hcompl P hPU
    ⟨inr d.actor, hxJ⟩ hxW _ hhJ
  intro v hv
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hv
  obtain ⟨b, hb, he⟩ := d.surjective_displacement a ha
  refine ⟨inr b, hUV (mem_map.mpr ⟨b, hb, rfl⟩), ?_⟩
  simpa only [map_mul, map_inv] using congrArg (inr : A →* G ⋊[φ] A) he

end Glauberman.SylowAutomorphisms.NormalComplement
