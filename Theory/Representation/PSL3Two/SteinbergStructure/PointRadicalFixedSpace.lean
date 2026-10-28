module

public import Theory.Representation.PSL3Two.SteinbergStructure.PointRadicalFixedSpace.Coordinates
public import Theory.Representation.PSL3Two.SteinbergStructure.PointRadicalFixedSpace.NaturalParabolics
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient

/-!
# The point-radical fixed plane in the actual Steinberg module

The point radical fixes the two-space of trace-zero endomorphisms with image
in the marked point and vanishing on that point. A nonzero such endomorphism
has that point as its image, so an actor sending it back into the fixed plane
must preserve the point. In a parabolic-invariant plane, the flag Sylow fixes
a nonzero vector; its parabolic orbit then gives the entire radical-fixed plane.

Conjugacy transport is proved for an abstract representation before specializing
to the concrete adjoint action. This keeps the transport proof independent of
the implementation of trace-zero matrices. The Chapter J consumer identifies
U/V with this unique plane through the specified common Ru1 marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(8,9), printed p.433 (PDF p.444), using H.6.3(4).
-/

public section
open Subgroup Representation Representation.BinaryOffender Matrix.PSL3Two
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
namespace BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace
noncomputable section
/-- A nonzero fixed vector can move back into this fixed plane only within its parabolic. -/
theorem transporter_mem_parabolic (g : Group) (v : Steinberg)
    (hv : v ∈ fixedSpace S MarkedAutomorphisms.pointV) (hn : v ≠ 0)
    (hgv : S g v ∈ fixedSpace S MarkedAutomorphisms.pointV) : g ∈ pointParabolicSL := by
  obtain ⟨x,hx⟩ := fixed_preimage v hv hn
  have ha : (S g v).val (W g x) = W g ![1,0,0] := by
    change W g (v.val (W g⁻¹ (W g x))) = _
    rw [Representation.inv_self_apply,hx]
  have hf := fixed_image (S g v) hgv (W g x)
  rw [ha] at hf
  apply (mem_pointParabolicSL_iff g).mpr
  change (g.val.mulVec ![1,0,0]) 1 = 0 ∧ (g.val.mulVec ![1,0,0]) 2 = 0 at hf
  simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_three] using hf

private theorem eq_of_le_card (A B : Submodule (ZMod 2) Steinberg) [Finite B]
    (h : A ≤ B) (hc : Nat.card B ≤ Nat.card A) : A = B := by
  apply Submodule.toAddSubgroup_injective
  exact AddSubgroup.eq_of_le_of_card_ge h hc
/-- The radical-fixed plane is the unique parabolic-invariant plane. -/
theorem eq_fixed_of_card_four (A : Submodule (ZMod 2) Steinberg)
    (hc : Nat.card A = 4)
    (hs : ∀ g ∈ pointParabolicSL, ∀ v ∈ A, S g v ∈ A) :
    A = fixedSpace S MarkedAutomorphisms.pointV := by
  let B : Subrepresentation (S.comp (FanoDecomposition.flagSylow : Subgroup Group).subtype) := {
    toSubmodule := A
    apply_mem_toSubmodule := fun g v hv => hs g (by
      have hg := g.property
      change (g : Group) ∈ (FanoDecomposition.flagSylow : Subgroup Group) at hg
      have he : (FanoDecomposition.flagSylow : Subgroup Group) = borelSL :=
        FanoDecomposition.flagSylow_coe.trans FanoDecomposition.markedFlag_stabilizer
      exact (show (g : Group) ∈ borelSL from he ▸ hg).1) v hv }
  have hcard : Nat.card B = 4 := hc
  let : Finite B := Nat.finite_of_card_ne_zero (by omega)
  let : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v,hv,hf⟩ := binary_pGroup_fixed_vector B.toRepresentation FanoDecomposition.flagSylow.isPGroup'
  have hvA : (v : Steinberg) ∈ A := v.property
  have hvnz : (v : Steinberg) ≠ 0 := fun h => hv (Subtype.ext h)
  have hvfixed : (v : Steinberg) ∈ fixedSpace S MarkedAutomorphisms.pointV := by
    intro a
    have hgt : (a : Group) ∈ (FanoDecomposition.flagSylow : Subgroup Group) := by
      rw [FanoDecomposition.flagSylow_coe, FanoDecomposition.markedFlag_stabilizer]
      have ha := a.property
      change (a : Group).val 0 0 = 1 ∧ (a : Group).val 1 0 = 0 ∧
        (a : Group).val 2 0 = 0 ∧ (a : Group).val 1 1 = 1 ∧
        (a : Group).val 1 2 = 0 ∧ (a : Group).val 2 1 = 0 ∧
        (a : Group).val 2 2 = 1 at ha
      exact (mem_borelSL_iff _).mpr ⟨ha.2.1,ha.2.2.1,ha.2.2.2.2.2.1⟩
    exact congrArg Subtype.val (hf ⟨a,hgt⟩)
  apply (eq_of_le_card _ _ ?_ (by rw [hc,card_fixed])).symm
  intro w hw
  by_cases hz : w = 0
  · exact hz.symm ▸ A.zero_mem
  · obtain ⟨g,hg,he⟩ := fixed_orbit w v hw hvfixed hz hvnz
    exact he ▸ hs g hg _ hvA

section Transport
variable {K M : Type*} [_root_.Group K] [AddCommGroup M] [Module (ZMod 2) M]
private theorem fixed_back (ρ : Representation (ZMod 2) K M) (R : Subgroup K) (g : K) (v : M)
    (hv : v ∈ fixedSpace ρ (R.map (MulAut.conj g).toMonoidHom)) :
    ρ g⁻¹ v ∈ fixedSpace ρ R := by
  intro a
  have ha : g * (a : K) * g⁻¹ ∈
      R.map (MulAut.conj g).toMonoidHom :=
    mem_map.mpr ⟨a,a.property,rfl⟩
  have h := congrArg (ρ g⁻¹) (hv ⟨_,ha⟩)
  change ρ (a : K) (ρ g⁻¹ v) = ρ g⁻¹ v
  change ρ g⁻¹ (ρ (g*(a:K)*g⁻¹) v) = ρ g⁻¹ v at h
  simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using h

private theorem fixed_forward (ρ : Representation (ZMod 2) K M) (R : Subgroup K) (g : K) (v : M)
    (hv : v ∈ fixedSpace ρ R) :
    ρ g v ∈ fixedSpace ρ (R.map (MulAut.conj g).toMonoidHom) := by
  intro a
  obtain ⟨b,hb,he⟩ := a.property
  change ρ (a : K) (ρ g v) = ρ g v
  rw [← he]
  change ρ (g*b*g⁻¹) (ρ g v) = ρ g v
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  exact congrArg (ρ g) (hv ⟨b,hb⟩)

/-- The corresponding fixed plane in every conjugate parabolic, with the literal action. -/
private theorem fixed_plane_conjugate (ρ : Representation (ZMod 2) K M)
    (P R : Subgroup K)
    (hunique : ∀ A : Submodule (ZMod 2) M, Nat.card A = 4 →
      (∀ a ∈ P, ∀ v ∈ A, ρ a v ∈ A) → A = fixedSpace ρ R) (g : K) (A : Submodule (ZMod 2) M)
    (hc : Nat.card A = 4)
    (hs : ∀ a ∈ P.map (MulAut.conj g).toMonoidHom,
      ∀ v ∈ A, ρ a v ∈ A) :
    A = fixedSpace ρ (R.map (MulAut.conj g).toMonoidHom) := by
  let B := A.comap (ρ g)
  let f : B → A := fun v => ⟨ρ g v,v.property⟩
  have hi : Function.Injective f := by
    intro v w h
    exact Subtype.ext ((ρ.apply_bijective g).injective (congrArg Subtype.val h))
  have hsur : Function.Surjective f := by
    intro v
    have hv : ρ g⁻¹ v ∈ B := by
      change ρ g (ρ g⁻¹ v) ∈ A
      rw [Representation.self_inv_apply]
      exact v.property
    exact ⟨⟨ρ g⁻¹ v,hv⟩, Subtype.ext (Representation.self_inv_apply ρ g v)⟩
  have hb : B = fixedSpace ρ R := by
    have hcard : Nat.card B = 4 :=
      (Nat.card_congr (Equiv.ofBijective f ⟨hi,hsur⟩)).trans hc
    apply hunique B hcard
    intro a ha v hv
    have h := hs (g*a*g⁻¹) (mem_map.mpr ⟨a,ha,rfl⟩) (ρ g v) hv
    change ρ g (ρ a v) ∈ A
    simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using h
  ext v
  constructor
  · intro hv
    have hback : ρ g⁻¹ v ∈ B := by
      change ρ g (ρ g⁻¹ v) ∈ A
      rw [Representation.self_inv_apply]
      exact hv
    rw [hb] at hback
    have hf := fixed_forward ρ R g (ρ g⁻¹ v) hback
    simpa only [Representation.self_inv_apply] using hf
  · intro hv
    have hback := fixed_back ρ R g v hv
    rw [← hb] at hback
    change ρ g (ρ g⁻¹ v) ∈ A at hback
    simpa only [Representation.self_inv_apply] using hback

/-- Distinct conjugate point planes have zero intersection. -/
private theorem transporter_conjugate (ρ : Representation (ZMod 2) K M)
    (P R : Subgroup K)
    (htrans : ∀ (g : K) (v : M), v ∈ fixedSpace ρ R → v ≠ 0 →
      ρ g v ∈ fixedSpace ρ R → g ∈ P) (g a : K) (v w : M)
    (hv : v ∈ fixedSpace ρ (R.map (MulAut.conj g).toMonoidHom))
    (hn : v ≠ 0)
    (hw : w ∈ fixedSpace ρ (R.map (MulAut.conj g).toMonoidHom))
    (ha : ρ a v = w) : a ∈ P.map (MulAut.conj g).toMonoidHom := by
  have hback : ρ g⁻¹ v ∈ fixedSpace ρ R := fixed_back ρ R g v hv
  have hn' : ρ g⁻¹ v ≠ 0 := by
    intro h
    apply hn
    calc
      v = ρ g (ρ g⁻¹ v) := (Representation.self_inv_apply ρ g v).symm
      _ = 0 := by rw [h,map_zero]
  have hbacka : ρ g⁻¹ (ρ a v) ∈ fixedSpace ρ R := by
    rw [ha]
    exact fixed_back ρ R g w hw
  have hconj : ρ (g⁻¹*a*g) (ρ g⁻¹ v) ∈ fixedSpace ρ R := by
    simpa only [map_mul, Module.End.mul_apply, Representation.self_inv_apply] using hbacka
  exact mem_map.mpr ⟨g⁻¹*a*g, htrans _ _ hback hn' hconj,
    by simp [MulAut.conj_apply, mul_assoc]⟩
end Transport

/-- The fixed plane of every conjugate point parabolic, using its literal action. -/
theorem conjugate_eq_fixed_of_card_four (g : Group) (A : Submodule (ZMod 2) Steinberg)
    (hc : Nat.card A = 4)
    (hs : ∀ a ∈ pointParabolicSL.map (MulAut.conj g).toMonoidHom,
      ∀ v ∈ A, S a v ∈ A) :
    A = fixedSpace S (MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom) :=
  fixed_plane_conjugate S pointParabolicSL MarkedAutomorphisms.pointV
    eq_fixed_of_card_four g A hc hs

/-- A nonzero vector of a conjugate fixed plane can return to that plane only
under its corresponding point parabolic. -/
theorem conjugate_transporter (g a : Group) (v w : Steinberg)
    (hv : v ∈ fixedSpace S (MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom))
    (hn : v ≠ 0)
    (hw : w ∈ fixedSpace S (MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom))
    (ha : S a v = w) : a ∈ pointParabolicSL.map (MulAut.conj g).toMonoidHom :=
  transporter_conjugate S pointParabolicSL MarkedAutomorphisms.pointV
    transporter_mem_parabolic g a v w hv hn hw ha
end
end BinaryLinearThree.SteinbergStructure.PointRadicalFixedSpace
