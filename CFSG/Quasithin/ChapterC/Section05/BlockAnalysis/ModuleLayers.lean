module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.SourceBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import Theory.GroupTheory.Commutator.NormalGeneration
public import Theory.GroupTheory.PCoreRestriction

/-!
# The literal module bounds needed by C.5.5

The two-core commutator with a block lies in its original U-layer.
Commutators distribute over the generated block product, giving the
corresponding bound for K. The core commutator of K therefore lies in
the product of the U-layers; characteristic two makes its centralizer
a two-group. These are the C.1.11 inputs used in C.5.4–5, with the
ambient Fitting hypothesis retained throughout.

Source: Aschbacher–Smith C.1.11 and C.5.4–5, printed pp.124 and155.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {A B : Type*} [Group A] [Group B]

def moduleLayer (L : Subgroup A) : Subgroup A := (blockU L).map L.subtype

theorem moduleLayer_map (f : A →* B) (hf : Function.Injective f) (L : Subgroup A) :
    moduleLayer (L.map f) = (moduleLayer L).map f := by
  let e := equivMapOfInjective L f hf
  have he := RankOne.Solvable.blockU_map_equiv e
  rw [moduleLayer,←he,Subgroup.map_map,moduleLayer,Subgroup.map_map]
  rfl

theorem moduleLayer_le (L : Subgroup A) : moduleLayer L ≤ L := map_subtype_le _

theorem moduleLayer_ne_bot {L : Subgroup A} (hL : IsShort L) : moduleLayer L ≠ ⊥ :=
  fun he => hL.blockU_ne_bot ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp he)

variable [Finite A]

theorem moduleLayer_le_core {L : Subgroup A} (hL : IsBlock L) :
    moduleLayer L ≤ pCore 2 A :=
  (map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hL.subnormal)

theorem core_commutator_le_moduleJoin {ι : Sort*} (L : ι → Subgroup A)
    (hL : ∀ i, IsBlock (L i)) :
    ⁅pCore 2 A,⨆ i,L i⁆ ≤ ⨆ i,moduleLayer (L i) := by
  rw [commutator_iSup_of_normal_left]
  apply iSup_le
  intro i
  exact (commutator_le_core_commutator_of_isSubnormal (L i) (pCore 2 A)
    (hL i).subnormal (hL i).short.twoPerfect pCore_isPGroup le_normalizer_of_normal).trans
    (le_iSup (fun i => moduleLayer (L i)) i)

/-- The original residual module controls the centralizer of the whole
block-module product; there is no unguarded block-product assertion. -/
theorem centralizer_moduleJoin_le_core {ι : Sort*} (L : ι → Subgroup A)
    (hL : ∀ i, IsBlock (L i)) (hf : generalizedFitting A = pCore 2 A)
    (hgen : (⨆ i,L i) = pResidual 2 A) :
    centralizer ((⨆ i,moduleLayer (L i) : Subgroup A) : Set A) ≤ pCore 2 A := by
  let K := pResidual 2 A
  have hfK : generalizedFitting K = pCore 2 K :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore K hf le_normalizer_of_normal
  have hUK : moduleLayer K ≤ ⨆ i,moduleLayer (L i) := by
    change (⁅pCore 2 K,(⊤ : Subgroup K)⁆).map K.subtype ≤ _
    rw [map_commutator,←MonoidHom.range_eq_map,K.range_subtype]
    have hcK : (pCore 2 K).map K.subtype ≤ pCore 2 A :=
      pCoreIn_le_of_subnormal 2 (inferInstance : K.Normal).isSubnormal
    have hh := core_commutator_le_moduleJoin L hL
    rw [hgen] at hh
    exact (commutator_mono hcK le_rfl).trans hh
  exact (centralizer_le hUK).trans
    (centralizer_blockU_le_core_of_normal K hfK (isPGroup_quotient_pResidual 2))

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
