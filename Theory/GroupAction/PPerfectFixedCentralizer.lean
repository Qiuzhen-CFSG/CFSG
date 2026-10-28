module

public import Theory.GroupAction.CommutingFixedKernel
public import Theory.GroupTheory.PPerfectHom

/-!
# Detecting a two-perfect action on fixed points

For commuting actions on a finite elementary abelian two-group, the kernel
of restriction to the fixed subgroup of a two-group is a two-group. A
two-perfect acting group therefore acts trivially if it fixes that subgroup.
This is the Thompson A × B consequence used in Aschbacher–Smith A.4.8(5).
The proof uses the actual conjugation images in the automorphism group.
-/

open scoped commutatorElement

public theorem IsPPerfect.centralizes_of_commuting_fixed
    {G : Type*} [Group G] [Finite G] (E Q Z : Subgroup G)
    [IsElementaryAbelian 2 Z] (hE : IsPPerfect 2 E) (hQ : IsPGroup 2 Q)
    (hEN : E ≤ Subgroup.normalizer (Z : Set G))
    (hQN : Q ≤ Subgroup.normalizer (Z : Set G))
    (hcomm : ⁅Q, E⁆ ≤ Subgroup.centralizer (Z : Set G))
    (hfix : ⁅Z ⊓ Subgroup.centralizer (Q : Set G), E⁆ = ⊥) :
    ⁅Z, E⁆ = ⊥ := by
  classical
  let f : Q →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hQN)
  let g : E →* MulAut Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hfP : IsPGroup 2 f.range := hQ.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfg : ⁅f.range, g.range⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    rintro a ⟨q, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨r, rfl⟩
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    let qN : Subgroup.normalizer (Z : Set G) := ⟨q, hQN q.property⟩
    let rN : Subgroup.normalizer (Z : Set G) := ⟨r, hEN r.property⟩
    have hk : ⁅qN, rN⁆ ∈ Z.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hcomm (Subgroup.commutator_mem_commutator q.property r.property)
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
  have hgtriv : g = 1 := hE.hom_eq_one_of_isPGroup hgP g.rangeRestrict |> fun h => by
    apply MonoidHom.ext
    intro e
    exact congrArg Subtype.val (DFunLike.congr_fun h e)
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hg : g ⟨r, hr⟩ = 1 := by rw [hgtriv]; rfl
  have hh := congrArg (fun a : MulAut Z => (a ⟨z, hz⟩ : G)) hg
  change r * z * r⁻¹ = z at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
