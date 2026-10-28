module
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic

/-!
# Local short moved modules in a characteristic-two core

The full-core displacement bound and short-layer dichotomy force the moved
module of a full-Sylow local short component into the ambient two-core.
The other alternative centralizes that self-centralizing core and would
make the local component solvable. This is the core-containment step in
the paired branch of Aschbacher--Smith14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Characteristic two forces the whole local short moved module into O₂(G). -/
theorem local_short_module_le_core_of_characteristicTwo
    (hf : generalizedFitting G = pCore 2 G) (S : Sylow 2 G)
    (B : Subgroup G) (hb : IsShort B)
    (hl : B ∈ ChapterA.Section03.localCComponents S) :
    (blockU B).map B.subtype ≤ pCore 2 G := by
  rcases RankOne.ChiProduct.normal_two_layer_short_dichotomy B (pCore 2 G) hb
    pCore_isPGroup (local_short_core_commutator_le_blockU S B hb hl) with hu | hc
  · exact hu
  · have hBcore : B ≤ pCore 2 G := hc.trans
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
    let : Group.IsNilpotent B := (pCore_isPGroup.to_le hBcore).isNilpotent
    exact (hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).injective)).elim

end CFSG.Quasithin.ChapterC
