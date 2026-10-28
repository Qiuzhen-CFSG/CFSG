module
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers

/-!
# Binary alpha-root classes from opposite-point fixation

A positive-unipotent element fixing an octonion vector whose last coordinate
is one lies in the derived group of the full G₂(2). Coordinates 6, 5 and 3
force the short-root parity C+D+F to vanish. This gives the class condition
needed when an alpha six-path root fixes its opposite endpoint. Normality
then preserves the class under the prescribed local-actor conjugation.

The vector need not be singular. In particular the conclusion applies to
any fixed point in the positive-unipotent orbit of the last basis vector.
No containment of the full second-ball kernel in the distinguished center
is used. Source: the root-coordinate model of DGS, Groups and Graphs (1985),
(14.2) and the binary branch of (14.17), printed pp.210 and 222--223.
The imported coordinates retain their ATLAS attribution (LICENSES/ATLAS.txt).
-/

public section
open Subgroup Atlas.G2.Explicit Atlas.SplitOctonion
namespace Atlas.G2.BinaryParabolicPair

private theorem parity_of_fixing (t : Fin 6 → ZMod 2) (v : Carrier (ZMod 2))
    (hv : v 7 = 1) (hfix : (unipotentProduct t).val v = v) :
    t 2 + t 3 + t 5 = 0 := by
  have h6 := congrFun hfix 6
  change v 6 + t 5 * v 7 = v 6 at h6
  have hf : t 5 = 0 := by simpa only [hv,mul_one,add_eq_left] using h6
  have h5 := congrFun hfix 5
  change v 5 + t 4 * (v 6 + t 5 * v 7) + t 3 * v 7 = v 5 at h5
  have hd : t 4 * v 6 + t 3 = 0 := by
    simpa only [hf,hv,zero_mul,add_zero,mul_one,add_assoc,add_eq_left] using h5
  have h3 := congrFun hfix 3
  change v 3 + t 5 * v 5 - t 3 * (v 6 + t 5 * v 7) - t 2 * v 7 = v 3 at h3
  have hc : t 3 * v 6 + t 2 = 0 := by
    simpa only [hf,hv,zero_mul,add_zero,mul_one,sub_sub,sub_eq_self] using h3
  have hp : ∀ e d c w : ZMod 2, e*w+d=0 → d*w+c=0 → c+d=0 := by decide +kernel
  simpa only [hf,add_zero] using hp (t 4) (t 3) (t 2) (v 6) hd hc

theorem alpha_fixer_mem_derived (g : Model (ZMod 2)) (hg : g ∈ unipotent)
    (v : Carrier (ZMod 2)) (hv : v 7 = 1) (hfix : g.val v = v) :
    g ∈ commutator (Model (ZMod 2)) := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩ := hg
  exact (EvenInvolutionGeometry.binary_unipotent_mem_derived t).mpr
    (parity_of_fixing t v hv hfix)

/-- Every point in the positive-unipotent orbit of the opposite coordinate
point supplies the same alpha-root class. -/
theorem alpha_fixer_mem_derived_of_opposite_orbit
    (g : Model (ZMod 2)) (hg : g ∈ unipotent)
    (u : Model (ZMod 2)) (hu : u ∈ unipotent)
    (hfix : g.val (u.val (basisVector 7)) = u.val (basisVector 7)) :
    g ∈ commutator (Model (ZMod 2)) := by
  apply alpha_fixer_mem_derived g hg (u.val (basisVector 7)) ?_ hfix
  rw [unipotent_eq_range] at hu
  obtain ⟨t,rfl⟩ := hu
  rfl

/-- The prescribed conjugation preserves the derived class of an alpha fixer. -/
theorem conjugate_alpha_fixer_mem_derived
    (g : Model (ZMod 2)) (hg : g ∈ unipotent)
    (v : Carrier (ZMod 2)) (hv : v 7 = 1) (hfix : g.val v = v)
    (a : Model (ZMod 2)) :
    a * g * a⁻¹ ∈ commutator (Model (ZMod 2)) := by
  exact (inferInstance : (commutator (Model (ZMod 2))).Normal).conj_mem
    g (alpha_fixer_mem_derived g hg v hv hfix) a

end Atlas.G2.BinaryParabolicPair
