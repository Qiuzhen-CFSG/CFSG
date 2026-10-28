module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.CubicLocal.InLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPair
public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC.GlaubermanNiles
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.CubicLocal
open ChapterB FixedPair
universe u
variable {G : Type u} [Group G] [Finite G]
/-!
# The fixed-pair cubic consumer

The local marking is consumed by the universal characteristic-pair alternative
on the same `D`.  The escaping subgroup is therefore classified as a literal
`BlockAlternative`; no block or characteristic-normalizer conclusion is used
as an input.  The later ambient C.1.27 lift still needs the actual subnormal
block supplied by the source factor route.
-/
theorem selected_blockAlternative
    (T : Sylow 2 G) (D : CharacteristicPair (baumann (T : Subgroup G)))
    (M N : Subgroup G) (hNM : N ≤ M) (hBN : baumann (T : Subgroup G) ≤ N)
    (hD : D.Universal.{u,u})
    (S : Sylow 2 N)
    (hS : (S : Subgroup N).map N.subtype = baumann (T : Subgroup G))
    (hSP : IsMinimalParabolicOver S ⊤)
    (hfit : generalizedFitting N = pCore 2 N)
    (hJ : ¬ elementaryAbelianMaxJ (S : Subgroup N) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N))
    (hsolv : Group.IsSolvable (N ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N)))
    (ha : IsMulCommutative ((S : Subgroup N).map
      (QuotientGroup.mk' (centralizer
        (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N)))))
    (hout : ¬ N ≤ (M ⊓ centralizer (firstSeed T D : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G))) :
    BlockAlternative N := by
  apply FixedPair.fixed_pair_block_of_escape T D hD M N hNM hBN
  · exact selected_inLocalClass T N S (baumann (T : Subgroup G)) hBN hS hSP hfit hJ hsolv ha
  · exact hout
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.CubicLocal
