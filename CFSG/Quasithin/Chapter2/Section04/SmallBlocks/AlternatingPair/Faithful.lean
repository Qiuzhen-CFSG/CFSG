module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Core

/-! The escaping conjugate removes the central core of the original A₅
block. Its whole intersection with O₂(G_I) is therefore trivial, not only
its module intersection. Source 2.4.25, printed p.542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.block_disjoint_phi_core
    (c : AlternatingPairSourceSetup d M₀) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    Disjoint L (twoCore (normalizer (Phi S L : Set G))) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let GI := normalizer (Phi S L : Set G)
  let Q := twoCore GI
  have hLG : L ≤ GI := (le_centralizer_iff.mp (Phi_le_centralizer S L)).trans
    (Subgroup.centralizer_le_normalizer _)
  have hN : L ≤ normalizer (L ⊓ Q : Set G) :=
    (le_inf L.le_normalizer (hLG.trans (le_normalizer_twoCore GI))).trans
      inf_normalizer_le_normalizer_inf
  have hW : L ⊓ Q ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 GI).to_le inf_le_right) inf_le_left hN
  have he : L.pCoreIn 2 = sourceModule L := congrArg (map L.subtype)
    (c.marked₁.block_core_eq_module c.x (c.original.R_normal c.x_mem) c.noncommuting)
  have hU : L ⊓ Q ≤ sourceModule L := he ▸ hW
  exact disjoint_iff.mpr (le_bot_iff.mp ((le_inf hU inf_le_right).trans
    (disjoint_iff.mp c.module_disjoint_phi_core).le))

end CFSG.Quasithin.Chapter2
