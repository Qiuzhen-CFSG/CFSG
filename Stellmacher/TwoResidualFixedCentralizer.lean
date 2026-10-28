module
public import Theory.GroupAction.CommutingFixedKernel
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# A residual centralizes an elementary module through its fixed subgroup

Let `E` and the two-group `Q` normalize an elementary abelian two-subgroup
`Z`. Suppose their commutator centralizes `Z`. If the two-residual of `E`
centralizes the Q-fixed subgroup `Z ∩ C_G(Q)`, it centralizes all of `Z`.

Use the actual conjugation homomorphism from the normalizer of `Z` into
its automorphism group. The Q-image is a two-group and commutes with the
residual image. The fixed-space kernel theorem makes the residual image
a two-group too. The two-residual is residual-perfect, so this image is
trivial, giving the required centralization in the ambient group.

This is the center-action transfer used in Stellmacher (9.1), relation
(3); see `refs/latex/stellmacher-n-group.tex`. It combines the standard
P × Q lemma with the residual functoriality established in Section 3.
-/

open BenderSuzuki.External
open Stellmacher
open scoped commutatorElement

namespace Stellmacher
public theorem twoResidual_centralizes_of_commuting_fixed
    {G : Type*} [Group G] [Finite G] (E Q Z : Subgroup G)
    [IsElementaryAbelian 2 Z] (hQ : IsPGroup 2 Q)
    (hEN : E ≤ Subgroup.normalizer (Z : Set G))
    (hQN : Q ≤ Subgroup.normalizer (Z : Set G))
    (hcomm : ⁅Q, E⁆ ≤ Subgroup.centralizer (Z : Set G))
    (hfix : ⁅Z ⊓ Subgroup.centralizer (Q : Set G), twoResidualAmbient E⁆ = ⊥) :
    ⁅Z, twoResidualAmbient E⁆ = ⊥ := by
  classical
  let R := twoResidualAmbient E
  have hRE : R ≤ E := Subgroup.map_subtype_le _
  have hRN := hRE.trans hEN
  let f : Q →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hQN)
  let g : R →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hRN)
  have hfP : IsPGroup 2 f.range := hQ.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfg : ⁅f.range, g.range⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rintro a ⟨q, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨r, rfl⟩
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    let qN : Subgroup.normalizer (Z : Set G) := ⟨q, hQN q.property⟩
    let rN : Subgroup.normalizer (Z : Set G) := ⟨r, hRN r.property⟩
    have hk : ⁅qN, rN⁆ ∈ Z.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hcomm (Subgroup.commutator_mem_commutator q.property (hRE r.property))
    change ⁅Z.normalizerMonoidHom qN, Z.normalizerMonoidHom rN⁆ = 1
    rw [← map_commutatorElement]
    exact hk
  have hgfix : g.range ≤ fixingSubgroup (MulAut Z)
      (FixedPoints.subgroup f.range Z : Set Z) := by
    rintro a ⟨r, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro z hz
    have hzC : (z : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hfz := hz (⟨f ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩⟩ : f.range)
      have hh := congrArg Subtype.val hfz
      change q * (z : G) * q⁻¹ = (z : G) at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh)
    have hzr : (r : G) * (z : G) = (z : G) * (r : G) :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hfix ⟨z.property, hzC⟩)
        r r.property
    apply Subtype.ext
    change (r : G) * (z : G) * (r : G)⁻¹ = (z : G)
    rw [hzr, mul_assoc, mul_inv_cancel, mul_one]
  have hgP : IsPGroup 2 g.range :=
    isPGroup_of_commuting_fixes_fixed f.range g.range hfP hfg hgfix
  have hquot : IsPGroup 2 (R ⧸ g.ker) :=
    hgP.of_equiv (QuotientGroup.quotientKerEquivRange g).symm
  have hker : hktPResidual 2 R ≤ g.ker := hktPResidual_le g.ker inferInstance hquot
  rw [show hktPResidual 2 R = ⊤ from twoResidualAmbient_has_top_twoResidual E] at hker
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hg : g ⟨r, hr⟩ = 1 := hker (Subgroup.mem_top _)
  have hh := congrArg (fun a : MulAut Z => (a ⟨z, hz⟩ : G)) hg
  change r * z * r⁻¹ = z at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
end Stellmacher
