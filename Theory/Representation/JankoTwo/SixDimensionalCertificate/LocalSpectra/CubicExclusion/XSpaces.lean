module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion.LinearAlgebra
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.WeightTraces
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicDivisibility

/-!
# The actual x-lines and x-planes of a six-dimensional J₂ action

Decompose each x-eigenspace under y to identify its dimension with the finite
weight certificate. On a line the prescribed word d acts trivially. On a plane
it has a nonidentity fifth-root weight. The literal (3,5,2) relations therefore
make c trivial on the lines and nontrivial on the planes.

Source: the local argument in ../../Source.md for Aschbacher–Smith K.4.5,
printed p.460, and Hiss–Malle corrected Table 2.
-/

@[expose] public noncomputable section
open Module
open scoped DirectSum BigOperators
namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
variable {E : Type*} [Field E]
open Sporadic.LeechRelated.J2
variable {U : Type*} [AddCommGroup U] [Module E U]

lemma x_spaces_internal [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    DirectSum.IsInternal (fun e : Fin 5 => Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)) := by
  apply power_eigenspaces_internal _ ((CharP.cast_eq_zero_iff E 2 5).not.mpr (by decide))
    (by rw [← map_pow, TraceGeometry.x_pow_five, map_one]) hζ

lemma x_space_dimension [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w) (e : Fin 5) :
    Module.finrank E (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)) =
      Weights.xMultiplicity i (e.val : ZMod 5) := by
  have hc : Commute (ρ TraceGeometry.y) (ρ TraceGeometry.x) := by
    change ρ TraceGeometry.y * ρ TraceGeometry.x = ρ TraceGeometry.x * ρ TraceGeometry.y
    rw [← map_mul, ← map_mul, TraceGeometry.x_y_commute]
  have hp : ∀ v ∈ Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val),
      ρ TraceGeometry.y v ∈ Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val) :=
    by
      intro v hv
      apply Module.End.mem_eigenspace_iff.mpr
      have hh := Module.End.mem_eigenspace_iff.mp hv
      rw [← Module.End.mul_apply, hc.symm.eq, Module.End.mul_apply, hh, map_smul]
  have hd := finrank_invariant_eq_sum (ρ TraceGeometry.y)
    ((CharP.cast_eq_zero_iff E 2 5).not.mpr (by decide))
    (by rw [← map_pow, TraceGeometry.y_pow_five, map_one]) hζ _ hp
  have he : Module.finrank E (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)) =
      ∑ b : Fin 5, weightMultiplicity ρ ζ ((e.val : ZMod 5), (b.val : ZMod 5)) := by
    rw [hd]
    apply Finset.sum_congr rfl
    intro b _
    unfold weightMultiplicity
    apply congrArg (fun S : Submodule E U => Module.finrank E S)
    rw [ZMod.val_natCast_of_lt e.isLt, ZMod.val_natCast_of_lt b.isLt]
  rw [he]
  simp_rw [hi]
  exact (by decide +kernel : ∀ (i : Fin 4) (e : Fin 5),
    (∑ b : Fin 5, Weights.pattern i ((e.val : ZMod 5), (b.val : ZMod 5))) =
      Weights.xMultiplicity i (e.val : ZMod 5)) i e

private lemma exists_weight (i : Fin 4) (e : Fin 5)
    (h : 0 < Weights.xMultiplicity i (e.val : ZMod 5)) :
    ∃ b : Fin 5, Weights.pattern i ((e.val : ZMod 5), (b.val : ZMod 5)) = 1 :=
  (by decide +kernel : ∀ (i : Fin 4) (e : Fin 5),
    0 < Weights.xMultiplicity i (e.val : ZMod 5) →
      ∃ b : Fin 5, Weights.pattern i ((e.val : ZMod 5), (b.val : ZMod 5)) = 1) i e h

lemma d_on_line [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) (hdim : Weights.xMultiplicity i (e.val : ZMod 5) = 1) :
    dOnXEigenspace ρ (ζ ^ e.val) = 1 := by
  obtain ⟨b, hb⟩ := exists_weight i e (by omega)
  let w : Weights.Weight := ((e.val : ZMod 5), (b.val : ZMod 5))
  have hd := Weights.line_trivial_on_d i w hb hdim
  have hle : weightSpace ρ ζ w ≤ Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val) := by
    simpa only [weightSpace, w, ZMod.val_natCast_of_lt e.isLt] using
      (inf_le_left : weightSpace ρ ζ w ≤ Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ w.1.val))
  have he : weightSpace ρ ζ w = Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_weightSpace, hi, hb, x_space_dimension ρ hζ i hi, hdim]
  ext v
  change ρ TraceGeometry.d v.val = v.val
  have hv : v.val ∈ weightSpace ρ ζ w := he.symm ▸ v.property
  rw [d_action ρ hζ w hv, hd]
  simp

lemma d_on_plane_ne_one [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) (hdim : Weights.xMultiplicity i (e.val : ZMod 5) = 2) :
    dOnXEigenspace ρ (ζ ^ e.val) ≠ 1 := by
  obtain ⟨b, hb⟩ := exists_weight i e (by omega)
  let w : Weights.Weight := ((e.val : ZMod 5), (b.val : ZMod 5))
  have hw : weightSpace ρ ζ w ≠ ⊥ := by
    intro h
    have hh := hi w
    change Module.finrank E (weightSpace ρ ζ w) = _ at hh
    rw [h, finrank_bot, hb] at hh
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hx : v ∈ Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val) := by
    have hh := hv.1
    change v ∈ Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ (e.val : ZMod 5).val) at hh
    rwa [ZMod.val_natCast_of_lt e.isLt] at hh
  intro he
  have hh := congrArg (fun f : Module.End E (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)) =>
    (f ⟨v, hx⟩ : U)) he
  change ρ TraceGeometry.d v = v at hh
  rw [d_action ρ hζ w hv] at hh
  have heigen : ζ ^ (Weights.dExponent w).val = 1 :=
    (smul_left_injective E hv0) (hh.trans (one_smul E v).symm)
  have hnonzero : (Weights.dExponent w).val ≠ 0 := by
    intro hz
    apply Weights.plane_nontrivial_on_d i w hb hdim
    exact ZMod.val_injective 5 hz
  exact hζ.pow_ne_one_of_pos_of_lt hnonzero (ZMod.val_lt _) heigen

lemma c_on_plane_ne_one [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) (hdim : Weights.xMultiplicity i (e.val : ZMod 5) = 2) :
    cOnXEigenspace ρ (ζ ^ e.val) ≠ 1 := by
  intro hc
  obtain ⟨_, hd, hcd⟩ := xEigenspace_triangle_relations ρ (ζ ^ e.val)
  rw [hc, one_mul] at hcd
  apply d_on_plane_ne_one ρ hζ i hi e hdim
  have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd) (orderOf_dvd_of_pow_eq_one hcd)
  norm_num at hh
  exact hh

lemma c_on_line [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) (hdim : Weights.xMultiplicity i (e.val : ZMod 5) = 1) :
    cOnXEigenspace ρ (ζ ^ e.val) = 1 := by
  obtain ⟨hc, _, hcd⟩ := xEigenspace_triangle_relations ρ (ζ ^ e.val)
  rw [d_on_line ρ hζ i hi e hdim, mul_one] at hcd
  have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc) (orderOf_dvd_of_pow_eq_one hcd)
  norm_num at hh
  exact hh


end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
