module

public import Stellmacher.SectionNine.DistanceOneAction
public import Stellmacher.TwoResidualConjugator

/-!
# Residual motion of the extracted product modulo the center intersection

In the actual length-one extraction, the residual of the extracted group
acts nontrivially on the product of cross factors modulo the intersection
of the two vertex centers, assuming the source index bound (4).
A residual conjugator carries the first vertex center to the second and
preserves the product, hence carries its first cross factor to its second.
If the residual commutator lay in the center intersection, it would
normalize the first factor. Both factors would then coincide, contrary to
the index bound and the source (2) intersection with the starting core.
This supplies the nontrivial action used in the admissible-seed construction.

Source: Stellmacher, N-group paper (1997), proof of (9.1), journal pp.46–47,
`refs/files/stellmacher-n-group.pdf`. No later core equality is used.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

/-- The extracted residual does not centralize the cross-factor product
modulo the intersection of the two vertex centers. -/
public theorem distance_one_extracted_residual_commutator_not_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx)
    (hcoatom : data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a))
    (hfour :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      4 ≤ (V ⊓ q ctx.Γ ctx.criticalPath.a).relIndex V) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    ¬ ⁅V, twoResidualIn data.E⁆ ≤ z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let Zc := z Γ next
  let C := Za ⊓ stabilizer Γ next
  let D := Zc ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  have hgeom := distance_one_product_factors Γ cp.a next
  have hZc : Zc = Za.conjBy data.x := by
    dsimp only [Zc, Za, next]
    rw [z_act, inv_inv]
    rfl
  obtain ⟨r, hr, hrconj⟩ := Stellmacher.exists_twoResidual_conjugator Za data.E data.x
    data.x_mem_E (data.generated.trans (congrArg (Za ⊔ ·) hZc))
  have hRV : data.E ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans
        (distance_one_extracted_action ctx hb data hcoatom))
  have hVr : V.map (MulAut.conj r).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRV (twoResidualIn_le data.E hr))
  have hCr : C.conjBy r = D := by
    change C.map (MulAut.conj r).toMonoidHom = D
    have hVC : V ⊓ Za = C := hgeom.2.2.2.1
    rw [← hVC, Subgroup.map_inf _ _ _ (MulAut.conj r).injective, hVr]
    change V ⊓ Za.conjBy r = D
    rw [hrconj, ← hZc]
    simpa only [sup_comm] using (distance_one_product_factors Γ next cp.a).2.2.2.1
  change ¬ ⁅V, twoResidualIn data.E⁆ ≤ Za ⊓ Zc
  intro hcomm
  have hIC : Za ⊓ Zc ≤ C := by
    rw [← hgeom.2.2.2.2]
    exact inf_le_left
  have hRC : twoResidualIn data.E ≤ Subgroup.normalizer C :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono (le_sup_left : C ≤ V) le_rfl).trans (hcomm.trans hIC))
  have hDC : D = C := hCr.symm.trans
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRC hr))
  have hVC : V = C := by simp only [V, hDC, sup_idem]
  have hi := distance_one_extracted_core_intersection ctx hb data
  change 4 ≤ (V ⊓ q Γ cp.a).relIndex V at hfour
  rw [hi, hVC, Subgroup.relIndex_self] at hfour
  omega

end Stellmacher.SectionNine
