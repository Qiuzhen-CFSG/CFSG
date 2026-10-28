module
public import Theory.GroupTheory.WreathTwoSylowCentralizer
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary two-subgroups of the concrete wreath product

Every elementary abelian two-subgroup of SL₂(2) wreath C₂ has order at most
four. Contain it in a Sylow two-subgroup, whose model is dihedral of order
eight. If the subgroup has at least four elements, the existing Sylow
centralizer bound gives order at most four; an abelian subgroup is contained
in that centralizer. The smaller case is immediate.

This source-neutral bound supplies the final fixed-core quotient estimate
in Stellmacher (8.6)(b), Journal of Algebra 190 (1997), printed p.44. The
statement uses the concrete regular wreath product and no campaign data.
-/

public theorem wreath_two_elementary_subgroup_card_le_four
    (V : Subgroup (RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))))
    (hV : IsElementaryAbelian 2 V) : Nat.card V ≤ 4 := by
  by_cases hcard : 4 ≤ Nat.card V
  · let _ := hV
    obtain ⟨P,hVP⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_le_sylow
    have hcent : V ≤ Subgroup.centralizer (V : Set _) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact (Subgroup.card_le_of_le (le_inf hVP hcent)).trans
      (wreath_two_sylow_centralizer_le_of_card_ge_four P V hVP hcard).2
  · omega
