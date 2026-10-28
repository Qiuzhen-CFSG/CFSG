module

public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# The literal two-core split in the alternating C.5 setup

Apply C.1.13(c) to the original subgroup K join Baum(R). Its two-core
contains the embedded U(K), is normalized by K, and has its K-commutators
in the original O₂(K); the source theorem proves these assertions itself.
Only normalization of the actual block by the Baumann subgroup is needed.
The stronger R-normalization version matches the normalized source setup.

No conjugator or identification of the entire block two-core with U(K)
is required. Source: Aschbacher–Smith C.5.4(3), printed p.155, using
C.1.13(c), printed pp.124–125.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
variable {G : Type*} [Group G] [Finite G]

theorem baumann_join_twoCore_split (K R : Subgroup G)
    (hK : IsAlternatingBlock K 5)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G)) :
    (K ⊔ ChapterB.baumann R).pCoreIn 2 = (blockU K).map K.subtype ⊔
      ((K ⊔ ChapterB.baumann R).pCoreIn 2 ⊓ centralizer (K : Set G)) :=
  hK.normalizer_twoCore_eq_module_sup_centralizer le_sup_left
    (sup_le K.le_normalizer hn)

theorem normalized_baumann_join_twoCore_split (K R : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hn : R ≤ normalizer (K : Set G)) :
    (K ⊔ ChapterB.baumann R).pCoreIn 2 = (blockU K).map K.subtype ⊔
      ((K ⊔ ChapterB.baumann R).pCoreIn 2 ⊓ centralizer (K : Set G)) :=
  baumann_join_twoCore_split K R hK (inf_le_left.trans hn)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
