module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.LocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.NaturalBlockAlternative
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.LocalAmbient
/-!
# Natural component recovery from the original common Baumann group

The canonical original Baumann embedding transports the common intrinsic
commutator bound into the selected component's local class. Its block
alternative retains the natural type, since the alternating-three branch
contradicts the actual C-component's nonsolvability. The resulting block
and natural marking are on the same subgroup K inside H.
Source: Aschbacher--Smith C.1.18 and 10.2.3(4), printed pp.126--127,746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]
theorem source_intrinsic_component_natural_of_common_baumann_commutator
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hBK : baumann (T.subtype hTH : Subgroup H) ≤ normalizer (K : Set H))
    (hlocal : InLocalClass (inclusion (show baumann (T.subtype hTH : Subgroup H) ≤
      K ⊔ baumann (T.subtype hTH : Subgroup H) from le_sup_right)))
    (hcomm : commutator (baumann (T : Subgroup G)) ≤
      omegaCenter (baumann (T : Subgroup G))) : IsBlock K ∧ ∃ m, IsL2EvenBlock K m := by
  let S := T.subtype hTH
  let N := K ⊔ baumann (S : Subgroup H)
  obtain ⟨b,hb,_⟩ := original_baumann_embedding (T : Subgroup G) H hTH
    N le_sup_right hlocal
  have hblock : BlockAlternative N := hb.blockAlternative_of_commutator_le_omegaCenter
    (SelectedRankOne.baumann_fixed (T : Subgroup G)) hcomm
  let := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro Q hQ hQp
    let := hQ
    let : Group.IsNilpotent (K ⧸ Q) := hQp.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := K)]
    exact solvableResidual_le_of_solvable_quotient Q
  exact SelectedRankOne.selected_component_natural_of_blockAlternative S K hK hp hBK hblock
end CFSG.Quasithin.Chapter10
