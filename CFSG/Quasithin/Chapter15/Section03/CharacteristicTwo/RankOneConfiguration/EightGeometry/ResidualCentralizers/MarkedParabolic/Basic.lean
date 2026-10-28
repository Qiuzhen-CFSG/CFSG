module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.LocalFamily
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.ActionKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Marking

/-!
# Compatible markings for the fixed-plane centralizer

Set K = C_L(Z_S). Relative normality of L in I makes S normalize K,
and S ∩ L lies in K because S centralizes its fixed plane. The given
natural eight-letter action has the same kernel as the original star map,
so it induces an actual compatible star equivalence. Relabelling preserves
compatibility, and every such equivalence takes the component to A₈ by
uniqueness of the index-two subgroup of S₈.

These are reductions toward the parabolic identification, not an assertion
that its four-block marking or Lie model already exists.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.3.32(4), printed pp.1132–1133.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic
variable {G : Type*} [Group G]

/-- The Sylow intersection lies in the actual component centralizer. -/
theorem sylow_intersection_le_centralizer (d : LocalData G) (L : Subgroup G) :
    d.S ⊓ L ≤ L ⊓ centralizer (d.ZS : Set G) :=
  le_inf inf_le_right (inf_le_left.trans (sylow_le_fixedPlane_centralizer d))

/-- Relative normality suffices for S to normalize C_L(Z_S). -/
theorem sylow_normalizes_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal) (hSI : d.S ≤ I) :
    d.S ≤ normalizer ((c.L ⊓ centralizer (d.ZS : Set G) : Subgroup G) : Set G) := by
  apply le_trans ?_ inf_normalizer_le_normalizer_inf
  apply le_inf
  · exact hSI.trans ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn)
  · exact (sylow_le_fixedPlane_centralizer d).trans (centralizer (d.ZS : Set G)).le_normalizer

/-- The original star quotient and the natural actor have identical kernels. -/
theorem star_actor_kernels (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2) :
    (d.starMap I).ker = a.actor.ker := by
  apply map_injective I.subtype_injective
  rw [star_kernel_eq_core_of_centralizer d c P hP hC, NaturalModule.naturalActor_ker,
    subgroupOf_map_subtype, inf_comm, hC]

/-- The first isomorphism theorem supplies a compatible marking with no relabelling. -/
noncomputable def naturalStarMarking (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2) :
    CompatibleStarMarking d I (d.componentModule I c.L) a where
  equiv := (QuotientGroup.quotientKerEquivOfSurjective (d.starMap I)
      (QuotientGroup.mk'_surjective _)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (star_actor_kernels d c a P hP hC)).trans
      (QuotientGroup.quotientKerEquivOfSurjective a.actor a.onto))
  relabel := 1
  compatible := by
    intro i
    have hs : (QuotientGroup.quotientKerEquivOfSurjective (d.starMap I)
        (QuotientGroup.mk'_surjective _)).symm (d.starMap I i) = QuotientGroup.mk i := by
      apply (QuotientGroup.quotientKerEquivOfSurjective (d.starMap I)
        (QuotientGroup.mk'_surjective _)).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    simp only [MulEquiv.trans_apply, one_mul, mul_one, inv_one]
    rw [hs]
    rfl

/-- Conjugate a marking while retaining the required actor identity. -/
def relabelMarking (d : LocalData G) {I U : Subgroup G} {a : NaturalEightAction I U}
    (b : CompatibleStarMarking d I U a) (r : Equiv.Perm (Fin 8)) :
    CompatibleStarMarking d I U a where
  equiv := b.equiv.trans (MulAut.conj r)
  relabel := r * b.relabel
  compatible := by
    intro i
    change r * b.equiv (d.starMap I i) * r⁻¹ =
      (r * b.relabel) * a.actor i * (r * b.relabel)⁻¹
    rw [b.compatible]
    group

/-- The component is A₈ under every star equivalence, including a relabelled one. -/
theorem component_image (d : LocalData G) {I L : Subgroup G}
    (m : Parabolics.MiddleNodePermutationMarking d I L)
    (e : d.Star I ≃* Equiv.Perm (Fin 8)) :
    (d.starImage I L).map e.toMonoidHom = alternatingGroup (Fin 8) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  calc
    _ = (d.starImage I L).index :=
      index_map_of_bijective (f := e.toMonoidHom) e.bijective _
    _ = ((d.starImage I L).map m.equiv.toMonoidHom).index :=
      (index_map_of_bijective (f := m.equiv.toMonoidHom) m.equiv.bijective _).symm
    _ = 2 := by rw [m.component]; exact alternatingGroup.index_eq_two

/-- The star kernel is a two-group under the supplied centralizer equality. -/
theorem star_kernel_isTwo (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hC : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2) :
    IsPGroup 2 (d.starMap I).ker := by
  have he : (d.starMap I).ker = pCore 2 I := by
    apply map_injective I.subtype_injective
    exact star_kernel_eq_core_of_centralizer d c P hP hC
  rw [he]
  exact pCore_isPGroup

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.MarkedParabolic

end
