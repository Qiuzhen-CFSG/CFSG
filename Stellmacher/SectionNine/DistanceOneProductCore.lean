module

public import Stellmacher.SectionNine.DistanceOneExtraction
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The extracted distance-one product lies in the neighboring core

For the actual extraction witness in the length-one case, the final
intersection identity in (8) puts the first cross factor in the next core.
Conjugation by the extracted element carries it to the second cross factor:
its square lies in the next core and hence in the starting stabilizer.
As this element normalizes the next core, the join of both factors lies
there too. This containment is shared by the admissible-seed construction
and the maximal-subgroup argument leading to (9).

Source: Stellmacher, N-group paper (1997), proof of (9.1), journal pp.46–47,
`refs/files/stellmacher-n-group.pdf`. No later core equality is used.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix
universe u

private theorem cross_factor_conjugate
    {G : Type*} [Group G] (Z L : Subgroup G) (actor : G)
    (hsquare : actor ^ 2 ∈ L) :
    (Z ⊓ L.conjBy actor).conjBy actor = Z.conjBy actor ⊓ L := by
  have hdouble : (L.conjBy actor).conjBy actor = L := by
    rw [Subgroup.conjBy_conjBy, ← pow_two]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hsquare)
  change (Z ⊓ L.conjBy actor).map (MulAut.conj actor).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj actor).injective]
  change Z.conjBy actor ⊓ (L.conjBy actor).conjBy actor = _
  rw [hdouble]

/-- The two extracted cross factors lie in the next core under the final
intersection identity from source (8). -/
public theorem distance_one_product_le_next_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx)
    (hintersection : z ctx.Γ ctx.criticalPath.a ⊓
        stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a') :
    (z ctx.Γ ctx.criticalPath.a ⊓
        stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)) ⊔
      (z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) ⊓
        stabilizer ctx.Γ ctx.criticalPath.a) ≤ q ctx.Γ ctx.criticalPath.a' := by
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  have hlen : cp.length = 1 := hb
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have hQGa : q Gamma cp.a' ≤ stabilizer Gamma cp.a := by
    rw [← hfirst]
    exact (local_cores_le_edge_sylow ctx.sectionSeven Gamma cp).2.trans
      (edge_sylow_data ctx.sectionSeven Gamma cp).1.1
  have hconj : ((z Gamma cp.a ⊓ stabilizer Gamma (Gamma.act data.x⁻¹ cp.a)).map
      (MulAut.conj data.x).toMonoidHom) =
      z Gamma (Gamma.act data.x⁻¹ cp.a) ⊓ stabilizer Gamma cp.a := by
    simp only [stabilizer_act, z_act, inv_inv, conjugateBy]
    exact cross_factor_conjugate (z Gamma cp.a) (stabilizer Gamma cp.a)
      data.x (hQGa data.x_sq_mem)
  have hleft : z Gamma cp.a ⊓ stabilizer Gamma (Gamma.act data.x⁻¹ cp.a) ≤
      q Gamma cp.a' := hintersection.le.trans inf_le_right
  have hxnorm := stabilizer_le_normalizer_q Gamma cp.a' data.x_mem
  apply sup_le hleft
  rw [← hconj, ← Subgroup.mem_normalizer_iff_map_conj_eq.mp hxnorm]
  exact Subgroup.map_mono hleft





end Stellmacher.SectionNine
