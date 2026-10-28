module
public import Theory.Representation.PSL3Four.SmallDegree
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.ReeF4.BinaryDegree.TitsAbsolute.Degree26Restriction.CliffordBound
public import Theory.PGroupCore

/-!
# Small simple degrees above a normal PSL₃(4) two-core quotient

Normal two-subgroups act trivially on simple binary modules. The proved
PSL₃(4) classification therefore gives degree one or nine below degree
thirteen, retaining the full supplied quotient marking.

For an irreducible overgroup action nontrivial on a normal subgroup, a
one-dimensional constituent would give normal fixed vectors and hence
trivial action. A nine-dimensional constituent occupies more than half the
space, so Clifford's conjugate-span argument makes the restriction simple.
The original overgroup module consequently has degree nine as well.

Source: Isaacs, Character Theory, Theorem 6.5; the PSL₃(4) tensor-word
classification cited in Theory.Representation.PSL3Four.SmallDegree.
-/

public section
open Subgroup Representation
namespace Representation.PSL3Four
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Killing only the two-core gives the degree-one-or-nine alternatives. -/
theorem core_simple_degree (e : (G ⧸ pCore 2 G) ≃* Matrix.PSL3Four.PSL)
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 12) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 9 := by
  have hk : pCore 2 G ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let τ := quotientOfLEKer ρ (pCore 2 G) hk
  let σ := τ.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  exact MathieuSmall.M22Recognition.PointRestriction.SimpleDegrees.simple_degree σ hd

/-- A nontrivial normal component action forces degree nine in small dimension. -/
theorem normal_core_simple_degree (H : Subgroup G) [H.Normal]
    (e : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Four.PSL)
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W ≤ 12) (hnt : ¬ H ≤ ρ.ker) :
    Module.finrank (ZMod 2) W = 9 := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp H.subtype)
  let : J.toRepresentation.IsIrreducible := hJ
  have hjd : Module.finrank (ZMod 2) J.toSubmodule = 9 := by
    rcases core_simple_degree e J.toRepresentation (J.toSubmodule.finrank_le.trans hd) with h1 | h9
    · exfalso
      apply hnt
      apply le_ker_of_normal_invariants_ne_bot ρ H
      let : Nontrivial J.toSubmodule :=
        Subrepresentation.irreducible_module_nontrivial J.toRepresentation
      obtain ⟨v,hv⟩ := exists_ne (0 : J.toSubmodule)
      have ht (g : H) : J.toRepresentation g v = v := by
        have hv0 : v ≠ 0 := hv
        obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one h1 hv0 (J.toRepresentation g v)
        have ha0 : a ≠ 0 := by
          intro he
          have hh : J.toRepresentation g v = 0 := by simpa [he] using ha.symm
          apply hv
          simpa only [J.toRepresentation.inv_self_apply,map_zero] using
            congrArg (J.toRepresentation g⁻¹) hh
        have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
        simpa only [ha1,one_smul] using ha.symm
      intro hb
      have hm : (v : W) ∈ invariants (ρ.comp H.subtype) :=
        fun g => congrArg Subtype.val (ht g)
      rw [hb,Submodule.mem_bot] at hm
      exact hv (Subtype.ext hm)
    · exact h9
  let : Representation.IsIrreducible (ρ.comp H.subtype) :=
    irreducible_restrict_of_large_constituent ρ H inferInstance J hJ (by omega)
  rcases core_simple_degree e (ρ.comp H.subtype) hd with h1 | h9
  · have hh := J.toSubmodule.finrank_le
    omega
  · exact h9
end Representation.PSL3Four
