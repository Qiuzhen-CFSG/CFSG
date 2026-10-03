module

public import Stellmacher.SectionNine.DistanceOneAction

/-!
# A normalized subgroup escaping the starting core

For the actual length-one extraction, a subgroup normalized by the next
stabilizer cannot lie in the starting core if its intersection with the
extracted product is not contained in the intersection of the two vertex
centers. Indeed, the extracted element interchanges the two product factors.
The product and the given subgroup are invariant under it. Source (2)
would put their intersection in the first factor under core containment;
conjugating puts it in the second as well, giving the contradiction.
This is the noncontainment step for the admissible seed before relation (9).

Source: Stellmacher, N-group paper (1997), proof of (9.1), journal pp.46–47,
`refs/files/stellmacher-n-group.pdf`. No later core equality is used.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
universe u

/-- A next-stabilizer-invariant subgroup with a noncentral intersection
with the extracted product is not contained in the starting core. -/
public theorem distance_one_normalized_subgroup_not_le_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx)
    (U : Subgroup G)
    (hUnorm : stabilizer ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer U)
    (hnot :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      ¬ U ⊓ V ≤ z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next) :
    ¬ U ≤ q ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let f := (MulAut.conj data.x).toMonoidHom
  have hswap := distance_one_factor_transport ctx hb data
  have hVmap : V.map f = V := by
    change (C ⊔ D).map f = C ⊔ D
    rw [Subgroup.map_sup, hswap.1, hswap.2, sup_comm]
  have hUmap : U.map f = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUnorm data.x_mem)
  have hXmap : (U ⊓ V).map f = U ⊓ V := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj data.x).injective, hUmap, hVmap]
  intro hUQ
  have hXC : U ⊓ V ≤ C := by
    have hi := distance_one_extracted_core_intersection ctx hb data
    exact (le_inf inf_le_right (inf_le_left.trans hUQ)).trans hi.le
  have hXD : U ⊓ V ≤ D := by
    rw [← hXmap]
    exact (Subgroup.map_mono hXC).trans hswap.1.le
  exact hnot (le_inf (hXC.trans inf_le_left) (hXD.trans inf_le_left))

end Stellmacher.SectionNine
