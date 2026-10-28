module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Local
public import Theory.GroupTheory.Nonabelian27Normalizer

/-!
# The normal Sylow step in Bender's order-27 exclusion

Every ambient Sylow two-subgroup has exponent two by the actual involution
centralizer calculation. For any nonabelian subgroup D of order 27 whose
ambient centralizer is a three-group, the Frattini action therefore gives
a normal Sylow three-subgroup of the literal normalizer N_G(D).

This supplies the `normalizerSylow` argument of
`not_exceptionalOddNormalizer_of_local_steps`. The parent argument supplies
D = Z and proves the three input properties; they remain explicit here.
Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
printed p.225 (PDF page 3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G]

/-- The normalizer-Sylow producer, with exactly the order, nonabelianness,
and centralizer premises used by the exceptional-configuration assembly. -/
public theorem normalizerSylow_of_nonabelian_order27 (h : Janko1CentralizerData G)
    (D : Subgroup G) (hcard : Nat.card D = 27) (hnonabelian : ¬ IsMulCommutative D)
    (hcentralizer : IsPGroup 3 (centralizer (D : Set G))) :
    ∃ P : Sylow 3 (normalizer (D : Set G)),
      (P : Subgroup (normalizer (D : Set G))).Normal :=
  D.exists_normal_sylow_three_normalizer_of_nonabelian_card_27
    h.any_sylow_square hcard hnonabelian hcentralizer

end CFSG.Quasithin.Janko1CentralizerData
