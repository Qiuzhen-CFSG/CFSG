module

public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.ElementaryAbelian.Injective

/-!
# Two-cores of proper odd-index subgroups of SL₃(2)

A proper odd-index subgroup that is not a two-group contains a full Sylow
two-subgroup and hence is one of the parabolics. Its two-core is therefore
an elementary four-group. The conclusion uses the core embedded by the
actual subgroup inclusion.

Source: the binary parabolic lattice in Aschbacher–Smith I.5.4,
printed p.420; used in C.1.34(5), printed p.137.
-/

public section
open Subgroup
namespace Matrix.PSL3Two

/-- The embedded core of a proper odd-index non-two-group is an elementary
four-group; no maximality or parabolic marking is assumed. -/
theorem odd_index_core_data (H : Subgroup SL) (hH : H ≠ ⊤)
    (hodd : Odd H.index) (htwo : ¬ IsPGroup 2 H) :
    IsElementaryAbelian 2 (H.pCoreIn 2) ∧ Nat.card (H.pCoreIn 2) = 4 := by
  classical
  let S : Sylow 2 H := Classical.choice inferInstance
  have hindex : ¬ 2 ∣ ((S : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two S.not_dvd_index hodd.not_two_dvd_nat
  let T : Sylow 2 SL := (S.isPGroup'.map H.subtype).toSylow hindex
  obtain ⟨e,_,he⟩ := exists_sylow_line_marking equiv T H (map_subtype_le _)
    hH htwo
  let eH : H ≃* Equiv.Perm (Fin 4) :=
    ((e.subgroupMap H).trans (MulEquiv.subgroupCongr he)).trans
      MarkedAutomorphisms.lineEquivSymmetric
  have hc := ParabolicCoreModel.core_data eH
  let eC : pCore 2 H ≃* H.pCoreIn 2 :=
    (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let := hc.1
  exact ⟨IsElementaryAbelian.of_injective eC.symm.toMonoidHom eC.symm.injective,
    (Nat.card_congr eC.symm.toEquiv).trans hc.2⟩

end Matrix.PSL3Two
