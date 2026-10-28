module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.SourceEscape
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The original Sylow intersection in each C.5.3 block

Each constructed block lies in O²(H), hence in RK. Restrict subnormality
and the given Sylow subgroup of RK to that literal block, then map back
to G. The result is R∩Kᵢ, precisely the Sylow witness required by the
natural and alternating C.5.4 setup producers.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G}

theorem OriginalHypotheses.block_sylow (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i : Fin b.size) : ∃ P : Sylow 2 ((b.block i).map H.subtype),
      (P : Subgroup ((b.block i).map H.subtype)).map ((b.block i).map H.subtype).subtype =
        R ⊓ (b.block i).map H.subtype := by
  let J := R ⊔ K
  let A := b.block i
  let L := A.map H.subtype
  have hLK : L ≤ K := (map_mono ((le_iSup b.block i).trans b.generate.le)).trans_eq d.residual
  have hLJ : L ≤ J := hLK.trans le_sup_right
  let f : J →* H := inclusion (sup_le d.R_le_H d.K_le_H)
  have hsub : (L.subgroupOf J).IsSubnormal := by
    have he : L.subgroupOf J = A.comap f := by
      ext j
      constructor
      · rintro ⟨a,ha,he⟩
        have hh : a = f j := Subtype.ext he
        change f j ∈ A
        exact hh ▸ ha
      · intro hj
        exact mem_map_of_mem H.subtype hj
    rw [he]
    exact (b.type i).1.subnormal.comap f
  obtain ⟨P,hP⟩ := d.residual_sylow.exists_subgroupOf_eq_of_subnormal
    (L.subgroupOf J) hsub
  let e : L.subgroupOf J ≃* L := subgroupOfEquivOfLe hLJ
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup (L.subgroupOf J)).map e.toMonoidHom).map L.subtype = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨l,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨d.residual_sylow_image ▸ mem_map_of_mem J.subtype hz,z.property⟩
  · rintro ⟨hxR,hxL⟩
    obtain ⟨z,hz,he⟩ := d.residual_sylow_image.symm ▸ hxR
    refine ⟨⟨x,hxL⟩,?_,rfl⟩
    let w : L.subgroupOf J := ⟨⟨x,hLJ hxL⟩,hxL⟩
    refine ⟨w,?_,rfl⟩
    change (⟨x,hLJ hxL⟩ : J) ∈ (d.residual_sylow : Subgroup J)
    exact (Subtype.ext he : z = ⟨x,hLJ hxL⟩) ▸ hz

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
