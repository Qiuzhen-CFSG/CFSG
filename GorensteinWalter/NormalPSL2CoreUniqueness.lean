module

public import GorensteinWalter.NormalPSL2CoreUniquenessGeneral

/-!
# Compatibility for normal PSL2 core uniqueness

The original index-two interface for uniqueness of a normal odd PSL2 core
is preserved here. The stronger theorem in NormalPSL2CoreUniquenessGeneral
proves the same conclusion without the extra ambient index-two subgroup.
All earlier model and structural prerequisites are re-exported through it.

Source: Alperin--Brauer--Gorenstein, Chapter II, Section 3, Proposition 2
(article page 22). The proof retains field order three and exact field-order
equality, and delegates to the full general uniqueness argument.
-/

public section
noncomputable section
namespace GorensteinWalter
universe u

theorem unique_normal_psl2_core
    {H : Type u} [Group H] [Finite H]
    (hHd : HasDihedralSylowTwo H) (hO : pPrimeCore 2 H = ⊥)
    (K : Subgroup H) (hKnormal : K.Normal) (hKindex : K.index = 2)
    (F : Type u) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (L : Subgroup H) (hLnormal : L.Normal) (eL : L ≃* PSL2 F)
    (E : Type u) [Field E] [Finite E]
    (hE : IsOddPrimePower (Nat.card E))
    (M : Subgroup H) (hMnormal : M.Normal) (eM : M ≃* PSL2 E) :
    M = L ∧ Nat.card E = Nat.card F := by
  exact (fun (_ : K.Normal) (_ : K.index = 2) =>
    unique_normal_psl2_core_of_dihedral hHd hO F hF L hLnormal eL E hE M hMnormal eM)
      hKnormal hKindex

end GorensteinWalter
