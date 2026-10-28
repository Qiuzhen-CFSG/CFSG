module
public import Theory.Frattini.DihedralOmega
public import Theory.GroupTheory.DihedralGeneratedFactor

/-!
# The characteristic involution in an elementary-by-dihedral group

The Frattini omega of a direct product of an elementary two-group and a
dihedral group of order at least eight has order two. The elementary
factor contributes nothing; the dihedral factor contributes its center.

Source: Aschbacher–Smith C.6.4, printed pp.168–169. This invariant fixes
the original marked line throughout the maximal-dihedral argument.
-/

public section
open Subgroup
namespace Subgroup
theorem omegaFrattini_card_of_elementary_dihedral
    {A E : Type*} [Group A] [Group E] [Finite A] [Finite E]
    [IsElementaryAbelian 2 E] {n : ℕ} (hn : 2 ≤ n)
    (e : A ≃* E × DihedralGroup (2 ^ n)) :
    Nat.card ((⊤ : Subgroup A).omegaFrattini) = 2 := by
  rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,
    omegaFrattini_top_map_equiv, omegaFrattini_top_prod
      (IsElementaryAbelian.isPGroup 2 E) (DihedralFrattini.dihedral_isPGroup n)]
  have hE : (⊤ : Subgroup E).omegaFrattini = ⊥ := by
    let : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
    rw [omegaFrattini_top,frattini_eq_bot_of_isElementaryAbelian (p := 2)]
    exact bot_unique (omegaOneAmbient_le _)
  rw [hE,DihedralFrattini.omegaFrattini_top_of_equiv hn (MulEquiv.refl _),
    Nat.card_congr (prodEquiv (⊥ : Subgroup E) (center (DihedralGroup (2 ^ n)))).toEquiv,
    Nat.card_prod,card_bot,one_mul]
  exact DihedralGroup.center_card_of_equiv hn (MulEquiv.refl _)


end Subgroup
