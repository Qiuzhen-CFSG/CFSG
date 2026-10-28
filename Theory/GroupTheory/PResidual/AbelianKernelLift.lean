module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Lifting p-perfectness through a moved abelian kernel

If an abelian kernel K is contained in B and [K,B]=K, then B is p-perfect
whenever its image is p-perfect. The embedded p-residual R has B=RK;
commuting K with this product gives K≤R, and hence B=R.

Source application: the natural-block Borel in Aschbacher--Smith15.1.21(i),
printed pp.1097--1098. This argument retains the entire central cover.
-/

public section
open scoped IsMulCommutative
open Subgroup
namespace Subgroup

/-- A fully moved abelian kernel lifts p-perfectness of a subgroup image. -/
theorem isPPerfect_of_abelian_kernel_image {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} (f : G →* H) (K : Subgroup G) [IsMulCommutative f.ker]
    (hk : f.ker ≤ K) (hm : ⁅f.ker,K⁆ = f.ker)
    (hi : IsPPerfect p (K.map f)) : IsPPerfect p K := by
  let R := (pResidual p K).map K.subtype
  have he : R.map f = K.map f := by
    rw [show R = (pResidual p K).map K.subtype from rfl,
      map_embedded_pResidual, (pResidual_eq_top_iff p _).mpr hi,
      ← MonoidHom.range_eq_map, range_subtype]
  have hs : R ⊔ f.ker = K := by
    simpa only [comap_map_eq, sup_eq_left.mpr hk] using congrArg (comap f) he
  have hn : K ≤ normalizer (R : Set G) := by
    have hh := (pResidual p K).le_normalizer_map K.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hc : ⁅f.ker,K⁆ ≤ R := by
    rw [commutator_comm]
    have hpre : K ≤ commutatorPreimage K f.ker R := by
      apply hs.ge.trans
      apply sup_le
      · exact le_commutatorPreimage (map_subtype_le _)
          (le_normalizer_iff_commutator_le_left.mp (hk.trans hn))
      · apply le_commutatorPreimage hk
        rw [commutator_eq_bot_iff_le_centralizer.mpr f.ker.le_centralizer]
        exact bot_le
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le K f.ker R hn)
  have hR : R = K := le_antisymm (map_subtype_le _) (hs ▸ sup_le le_rfl (hm ▸ hc))
  apply (pResidual_eq_top_iff p K).mp
  apply map_injective (f := K.subtype) K.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact hR

end Subgroup
