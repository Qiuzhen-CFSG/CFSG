module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Conjugator
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Complement
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Symmetry.Preparation
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Symmetry.Transvection

/-!
# Assembly of the two marked transvections

The original reflection is constructed from `CentralizerGeometry`. For the
opposite reflection, its membership in Tᵍ fixes both r and u. Decomposing V
as Z(Tᵍ)⟨z⟩ gives the exact fixed plane and commutator center; intersection
with L′ and v ∉ L′ give the distinct marked lines. Weak closure transports
with the chosen conjugator.

This completes the equations conditional on `OppositeReflection`. The
opposite outer-PGL action and the construction of that geometric output
remain separate obligations; this module does not claim their existence
or the completed source symmetry theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1185. Conjugation is left conjugation throughout.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r v u s : G} {L R : Subgroup G}

/-- Complete the equations once the opposite geometric construction has been
proved. This conditional assembly does not assert the existence of u or s. -/
theorem symmetricTransvections_of_oppositeReflection
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hc : CentralizerGeometry T z L r v)
    (hw : WeaklyClosedInCenter (T : Subgroup G) z)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g)
    (hz : MulAut.conj g z = r) (ho : OppositeReflection T z r L g v u s) :
    ∃ t, SymmetricTransvections T z r L g v u s t := by
  obtain ⟨t, ht, htr, htz, htv, htaxis, htcenter⟩ :=
    hc.exists_marked_transvection h hr hr2
  have hzTg : z ∈ (T : Subgroup G).conjBy g :=
    htransport ⟨h.mem_sylow, h.z_normalizes_conjugate⟩
  have hrA : r ∈ embeddedCenter ((T : Subgroup G).conjBy g) := by
    rw [ho.center_eq]
    exact mem_sup_left (mem_zpowers r)
  have huA : u ∈ embeddedCenter ((T : Subgroup G).conjBy g) := by
    rw [ho.center_eq]
    exact mem_sup_right (mem_zpowers u)
  have hfix : embeddedCenter ((T : Subgroup G).conjBy g) ≤ involutionCentralizer s := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hx.2 s ho.s_mem.1).symm)
  have hfixed (x : G) (hx : x ∈ embeddedCenter ((T : Subgroup G).conjBy g)) :
      MulAut.conj s x = x := by
    change s * x * s⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_singleton_iff.mp (hfix hx)).symm
  have hV : markedEight z r v =
      embeddedCenter ((T : Subgroup G).conjBy g) ⊔ zpowers z := by
    rw [← ho.eight_eq, ho.center_eq, markedEight, sup_comm (zpowers r) (zpowers u)]
  have hzu : z ∈ centralizer (embeddedCenter ((T : Subgroup G).conjBy g) : Set G) :=
    le_centralizer_iff.mp (show embeddedCenter ((T : Subgroup G).conjBy g) ≤
      centralizer ((T : Subgroup G).conjBy g : Set G) from inf_le_right) hzTg
  have hAc : embeddedCenter ((T : Subgroup G).conjBy g) ≤ centralizer (zpowers u : Set G) :=
    inf_le_right.trans (centralizer_le (fun _ hx => (zpowers_le.mpr huA.1) hx))
  have hune : u ≠ 1 := by intro he; simpa [he] using ho.u_order
  obtain ⟨hsaxis, hscenter⟩ :=
    marked_reflection_axis_center h.involution hune huA hzu hAc hfix ho.s_z
  rw [← hV] at hsaxis hscenter
  have hlines : zpowers u ≠ zpowers v := by
    intro he
    apply ho.v_not_mem
    have hv : v ∈ zpowers u := he ▸ mem_zpowers v
    rw [← ho.intersection_eq] at hv
    exact hv.2
  exact ⟨t, {
    weak_z := hw
    weak_r := hz ▸ hw.conjBy g
    v_not_mem := ho.v_not_mem
    u_order := ho.u_order
    intersection_eq := ho.intersection_eq
    lines_ne := hlines
    opposite_center_eq := ho.center_eq
    t_mem := ht
    s_mem := ho.s_mem
    t_r := htr
    t_z := htz
    t_v := htv
    s_z := ho.s_z
    s_r := hfixed r hrA
    s_u := hfixed u huA
    t_axis := htaxis
    s_axis := hsaxis.trans ho.center_eq
    t_center := htcenter
    s_center := hscenter }⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
