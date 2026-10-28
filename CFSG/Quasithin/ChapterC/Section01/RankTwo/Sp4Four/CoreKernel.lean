module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary

/-!
# The whole two-core in a perfect symplectic extension

After factoring out the intrinsic commutator core [O₂(K),K], the remaining
two-core is central. The proved positive-root lifting and Sylow transfer
for Sp₄ in even characteristic exclude a nontrivial central two-kernel.
Thus the original two-core equals the entire intrinsic commutator core,
without assuming shortness or block recognition.

The original tensor plane quotient uses this equality to identify its exact
kernel with the ambient block intersection. Source: Aschbacher--Smith C.1.8,
I.1.3, and the final paragraph of 9.3 (printed pp.123,407,734--735).
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {K F : Type*} [Group K] [Finite K] [Group.IsPerfect K]
  [Field F] [Finite F] [CharP F 2]

theorem core_eq_blockU_of_symplectic_quotient (hF : 2 < Nat.card F)
    (e : (K ⧸ pCore 2 K) ≃* Sp F) : pCore 2 K = blockU K := by
  let q := QuotientGroup.mk' (blockU K)
  let f := QuotientGroup.lift (blockU K) (QuotientGroup.mk' (pCore 2 K))
    (by simpa only [QuotientGroup.ker_mk'] using (blockU_le_core (L := K)))
  have hk : f.ker = (pCore 2 K).map q := by
    dsimp [f]
    rw [QuotientGroup.ker_lift,QuotientGroup.ker_mk']
  let g := e.toMonoidHom.comp f
  have hg : Function.Surjective g := e.surjective.comp
    (QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _)
  have hgk : g.ker = (pCore 2 K).map q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,hk]
  have hgc : g.ker ≤ center (K ⧸ blockU K) := hgk ▸ blockU_core_image_le_center
  let cover : PerfectCentralCovering.Cover (K ⧸ blockU K) (Sp F) := {
    toMonoidHom := g
    surjective := hg
    isPerfect := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    ker_le_center := hgc }
  obtain ⟨lifts⟩ := CentralCovers.TwoPrimary.FieldFour.exists_positive_root_lifts hF g hg hgc
  have hodd := CentralCovers.TwoPrimary.not_two_dvd_kernel_of_positive_root_lifts cover lifts
  have hp : IsPGroup 2 g.ker := hgk ▸ pCore_isPGroup.map q
  have hbot : g.ker = ⊥ := by
    apply Subgroup.card_eq_one.mp
    exact hp.card_eq_or_dvd.resolve_right hodd
  apply le_antisymm _ blockU_le_core
  have hm : (pCore 2 K).map q = ⊥ := hgk.symm.trans hbot
  simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hm

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
