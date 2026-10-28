module

public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.SpecificGroups.Triality.RadicalCoordinates
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers

/-!
# The full arms parabolic has trivial center above the binary field

A central element of the full arms parabolic lies in its self-centralizing
radical, hence in the highest-root subgroup. The independent base-field
torus coordinate scales that root parameter. A unit other than one forces
the parameter to vanish whenever the fixed field has more than two elements.

The proof retains the actual graph-field carrier, its root radical and its
full torus. The bound on the fixed field is essential: the binary arms
parabolic centralizes its highest-root subgroup.

Sources: GLS3 §2.4 and Theorem 2.6.5(e–g)
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.12(I)(4),
printed pp.263–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace Triality.Standard.Parabolics
open Subgroup RadicalCoordinates.Centers NormalizedRootCentralizers ConcreteBruhat

/-- The full arms parabolic has trivial center when its fixed field has
more than two elements. -/
theorem arms_parabolic_center_eq_bot (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) : center (parabolic P .arms) = ⊥ := by
  have hu : 1 < Nat.card (fixedField P)ˣ := by
    rw [Nat.card_units, card_fixedField]
    omega
  let : Nontrivial (fixedField P)ˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨c, hc⟩ := exists_ne (1 : (fixedField P)ˣ)
  have hc1 : (c : fixedField P) ≠ 1 := fun he => hc (Units.ext he)
  apply bot_unique
  intro z hz
  have hzc : z.val ∈ centralizer (radical P .arms : Set (Carrier P)) := by
    apply mem_centralizer_iff.mpr
    intro r hr
    exact congrArg Subtype.val
      (mem_center_iff.mp hz ⟨r, radical_le_parabolic P .arms hr⟩)
  have hzr : z.val ∈ radical P .arms :=
    parabolic_centralizer_radical_le P hp .arms ⟨z.property, hzc⟩
  have hzh : z.val ∈ highestRoot P := by
    rw [← RadicalCoordinates.embedded_center_radical_arms P hp]
    refine ⟨⟨z.val, hzr⟩, mem_center_iff.mpr (fun r => ?_), rfl⟩
    apply Subtype.ext
    change r.val * z.val = z.val * r.val
    exact congrArg (fun k : parabolic P .arms => (k : Carrier P))
      (mem_center_iff.mp hz ⟨r.val, radical_le_parabolic P .arms r.property⟩)
  rw [← highestHom_range P hp] at hzh
  obtain ⟨a, ha⟩ := hzh
  let g := ConcreteBruhat.TorusCoordinates.torusMulEquiv P hp (1, c)
  have hg : g.val ∈ parabolic P .arms :=
    borel_le_parabolic P .arms (torus_le_borel P g.property)
  have hfix : g.val * highestHom P hp a * g.val⁻¹ = highestHom P hp a := by
    rw [ha]
    exact (mul_inv_eq_iff_eq_mul).mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨g.val, hg⟩))
  have hscalar : c.val * a.toAdd = a.toAdd := by
    exact congrArg Multiplicative.toAdd
      (highestHom_injective P hp
        ((torus_conjugate_highestHom P hp (1, c) a.toAdd).symm.trans hfix))
  have ha0 : a.toAdd = 0 :=
    (mul_eq_mul_right_iff.mp (hscalar.trans (one_mul a.toAdd).symm)).resolve_left hc1
  change z = 1
  apply Subtype.ext
  rw [← ha, show a = 1 from congrArg Multiplicative.ofAdd ha0, map_one]
  rfl

end Triality.Standard.Parabolics
