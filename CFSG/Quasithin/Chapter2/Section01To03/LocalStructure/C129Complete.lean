module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Source
/-!
# The unconditional original C.1.29 input for Chapter 2

The complete known-simple outside-block theorem instantiates the universal
C.1.29 source adapter inside every actual local subgroup. This supplies the
literal block decomposition used by Chapter 2, preserving its original
subgroup maps and Sylow marking. No characteristic-pair, block, module,
classification, or decomposition premise remains.

Source: Aschbacher–Smith C.1.29 and 2.3.8–9.
-/
public section
namespace CFSG.Quasithin.Chapter2
universe u
variable {G : Type u} [Group G] [Finite G]

theorem localC129Input_knownSimple : LocalC129Input KnownSimple.IsKnownSimple G :=
  localC129Input_of_c128_outside
    (fun hG hf T M hM hn => ChapterC.RankOne.ChiProduct.SelectedRankOne.outside_moved_chi_knownSimple
      hG hf T M hM hn)
end CFSG.Quasithin.Chapter2
