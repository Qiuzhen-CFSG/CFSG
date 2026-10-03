module

public import Stellmacher.Recognition.FongWreathedCentralizerQuotients
public import Stellmacher.Recognition.FongWreathedOddCentralizers
public import Stellmacher.Recognition.FongWreathedFusion
public import Stellmacher.Recognition.FongWreathedFusionOrientation

/-!
# Fong's ambient centralizer data

The public entry point for Fong's local centralizer calculations in a
finite simple group with a wreathed Sylow subgroup of order 32. The
fusion and quotient results retain actual presentation elements, odd-core quotient
maps, and the prescribed cyclic denominators of the symmetric-four
quotients.

Choose a compatible presentation using the base-normalizer action, then
apply the presentation-independent centralizer theorems to that same
presentation. `exists_localCentralizerData` packages the six distinct
ambient classes together with the normal odd complements, concrete small
quotient models, order-96 quotients, and actual symmetric-four quotients.
The publicly imported component results also retain the projective maps
and their exact kernels for subsequent principal-block calculations.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), pp. 69–71, equations (4)–(5) and the
centralizer calculation preceding (6).
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

local notation "CF" => Subgroup.centralizer ({((F P : S) : G)} : Set G)
local notation "CF3" => Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G)
local notation "CF2" => Subgroup.centralizer ({((F P ^ 2 : S) : G)} : Set G)
local notation "CXF2" => Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)
local notation "CJ" => Subgroup.centralizer ({((J P : S) : G)} : Set G)

/-- Fong's ambient fusion and centralizer quotients for one compatible
presentation. The cyclic denominators in the last two fields are the images
of the actual square `F²`, with their proved normality. -/
public structure LocalCentralizerData : Prop extends SixClassFusion S P where
  F_normalComplement : HasNormalPComplement 2 CF
  F_cube_normalComplement : HasNormalPComplement 2 CF3
  XF_sq_normalComplement : HasNormalPComplement 2 CXF2
  F_quotient : Nonempty ((CF ⧸ pPrimeCore 2 CF) ≃* Multiplicative (ZMod 8))
  F_cube_quotient : Nonempty ((CF3 ⧸ pPrimeCore 2 CF3) ≃* Multiplicative (ZMod 8))
  XF_sq_quotient : Nonempty ((CXF2 ⧸ pPrimeCore 2 CXF2) ≃*
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
  F_sq_quotient_card : Nat.card (CF2 ⧸ pPrimeCore 2 CF2) = 96
  J_quotient_card : Nat.card (CJ ⧸ pPrimeCore 2 CJ) = 96
  F_sq_projective_quotient :
    let Z := Subgroup.zpowers
      (QuotientGroup.mk' (pPrimeCore 2 CF2) (squareInCentralizerF2 S P))
    let _ : Z.Normal := squareInCentralizerF2_quotient_zpowers_normal S P
    Nonempty (((CF2 ⧸ pPrimeCore 2 CF2) ⧸ Z) ≃* Equiv.Perm (Fin 4))
  J_projective_quotient :
    let Z := Subgroup.zpowers
      (QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P))
    let _ : Z.Normal := squareInCentralizerJ_quotient_zpowers_normal S P
    Nonempty (((CJ ⧸ pPrimeCore 2 CJ) ⧸ Z) ≃* Equiv.Perm (Fin 4))

/-- Fusion can be oriented without a solvability hypothesis. -/
public theorem exists_sixClassFusion (hS : IsWreathedOfHeight S 2) :
    ∃ P : Wreathed.Presentation S 2, SixClassFusion S P := by
  obtain ⟨P, ho⟩ := exists_baseOrientation S hS
  exact ⟨P, sixClassFusion_of_baseOrientation S P ho⟩

/-- For a compatible presentation, a single solvable involution centralizer
determines all the required odd-core quotient models. -/
public theorem localCentralizerData_of_baseOrientation (ho : BaseOrientation S P)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    LocalCentralizerData S P where
  toSixClassFusion := sixClassFusion_of_baseOrientation S P ho
  F_normalComplement := centralizerF_hasNormalPComplement S P x hx
  F_cube_normalComplement := centralizerF_cube_hasNormalPComplement S P x hx
  XF_sq_normalComplement := centralizerXF_sq_hasNormalPComplement S P x hx
  F_quotient := centralizerF_oddCore_quotient_equiv S P x hx
  F_cube_quotient := centralizerF_cube_oddCore_quotient_equiv S P x hx
  XF_sq_quotient := centralizerXF_sq_oddCore_quotient_equiv S P x hx
  F_sq_quotient_card := centralizerF2_oddCore_card S P x hx
  J_quotient_card := (centralizerJ_oddCore_projective S P x hx).1
  F_sq_projective_quotient := centralizerF2_oddCore_square_quotient_equiv S P x hx
  J_projective_quotient := centralizerJ_oddCore_square_quotient_equiv S P x hx

/-- Fong's complete fusion and centralizer data under the ambient hypotheses,
using one actual presentation chosen with the required orientation. -/
public theorem exists_localCentralizerData (hS : IsWreathedOfHeight S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ P : Wreathed.Presentation S 2, LocalCentralizerData S P := by
  obtain ⟨P, ho⟩ := exists_baseOrientation S hS
  exact ⟨P, localCentralizerData_of_baseOrientation S P ho x hx⟩

end Stellmacher.Recognition.FongWreathedIntrinsic
