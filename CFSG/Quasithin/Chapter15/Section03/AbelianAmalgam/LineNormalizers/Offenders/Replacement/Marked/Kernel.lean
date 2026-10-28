module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.Residual
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Inheritance

/-!
# The original residual and the section kernel

A singular four-subgroup in the natural orthogonal four-space is a graph
between its two definite planes. If independent plane rotations act trivially
modulo that graph, testing the two coordinate planes forces both rotations to
be the identity. Thus the original `Y_E` section kernel centralizes `V`.
The earlier action-kernel identity and relative normality place it in the
original `Q_E`, without any replacement-core assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.66 and
proof of 15.3.67, printed pp.1152–1153, PDF pp.1169–1170.
-/

@[expose] public section
open Subgroup Stellmacher OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped commutatorElement Pointwise IsMulCommutative

private theorem rotation_quotient_faithful (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0)
    (g : IsometryGroup) (hg : g ∈ lineResidual E)
    (hfix : ∀ v : Multiplicative Space, vectorAction g v * v⁻¹ ∈ E) : g = 1 := by
  obtain ⟨i, rfl⟩ := singular_four_eq_graph E hcard hs
  rw [lineResidual_eq_rotations_inter] at hg
  obtain ⟨k, rfl⟩ := hg.1
  have h₁ (x : Plane) : (planeRotation ^ k.toAdd.1.val) x = x := by
    have h := hfix (Multiplicative.ofAdd (x, 0))
    change (planeRotation ^ k.toAdd.2.val) 0 + -0 =
      planePermutation i ((planeRotation ^ k.toAdd.1.val) x + -x) at h
    rw [map_zero, neg_zero, add_zero] at h
    exact sub_eq_zero.mp ((planePermutation i).injective (by simpa [sub_eq_add_neg] using h.symm))
  have h₂ (x : Plane) : (planeRotation ^ k.toAdd.2.val) x = x := by
    have h := hfix (Multiplicative.ofAdd (0, x))
    change (planeRotation ^ k.toAdd.2.val) x + -x =
      planePermutation i ((planeRotation ^ k.toAdd.1.val) 0 + -0) at h
    simpa only [map_zero, neg_zero, add_zero, ← sub_eq_add_neg, sub_eq_zero] using h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Prod.ext (h₁ x.1) (h₂ x.2)

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- The actual original marked action supplies the kernel bound needed by replacement. -/
theorem lineY_inf_sectionKernel_le_lineQ (d : NaturalAction V M) (Y E : Subgroup G)
    [IsMulCommutative V]
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hY : lineNormalizer E ≤ normalizer (lineY Y E : Set G)) :
    lineY Y E ⊓ Descent.sectionKernel V E ≤ lineQ E := by
  have hcore : twoCoreAmbient (lineY Y E) ≤ lineQ E :=
    pCoreIn_mono_of_normalizes ((lineY_le Y E).trans inf_le_right) hY
  rw [Orthogonal.lineY_twoCore d Y E hYM hEV himage hYcore] at hcore
  rintro y ⟨hy, hk⟩
  apply hcore
  refine ⟨hy, ?_⟩
  let m : M := ⟨y, hYM ((lineY_le Y E).trans inf_le_left hy)⟩
  have hg : d.action m ∈ lineResidual (coordinateLine d E) := by
    rw [← actionImage_lineY d Y E hYM hEV himage]
    exact mem_map_of_mem _ hy
  have he := rotation_quotient_faithful (coordinateLine d E)
    ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs)
    (d.action m) hg (by
      intro w
      apply (mem_coordinateLine d E _).mpr
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      have hd := d.intertwines m (d.coordinates.symm w)
      rw [d.coordinates.apply_symm_apply] at hd
      change (d.coordinates.symm (vectorAction (d.action m) w) : G) =
        y * (d.coordinates.symm w : G) * y⁻¹ at hd
      rw [hd]
      have hc := ((Descent.mem_sectionKernel_iff V E
        (lineV_le_lineNormalizer V E hEV) y).mp hk).2
        (d.coordinates.symm w) (le_conjugateSpanBy V _ (d.coordinates.symm w).property)
      change ⁅y, (d.coordinates.symm w : G)⁆ ∈ E
      rw [← commutatorElement_inv]
      exact E.inv_mem hc)
  have hm : m ∈ d.action.ker := he
  rw [action_ker d] at hm
  exact hm

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
