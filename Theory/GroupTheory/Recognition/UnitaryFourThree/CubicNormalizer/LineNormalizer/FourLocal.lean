module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.CommonCentralizer
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.PlaneData
public import Theory.GroupTheory.NormalizingSubgroupCard
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
/-!
# The global four-group normalizer is its original local plane normalizer.
The common centralizer has order12 and the automorphism group has order6.
Source: Aschbacher, Sporadic Groups (1994),45.7(3),printed p.245.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_four_normalizer_eq_local (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) (htA:m.t∈A)
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
    normalizer (U:Set G)⊓normalizer ((zpowers z⊔zpowers m.t:Subgroup G):Set G)=
      normalizer (A:Set G)⊓normalizer (U:Set G) := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let S:=zpowers z⊔zpowers m.t
  let K:=normalizer (U:Set G)
  let J:=K⊓normalizer (S:Set G)
  let L:=normalizer (A:Set G)⊓K
  have hSp:A⊓Subgroup.centralizer (U:Set G)=S:=R.reflected_four_eq_plane_fixed h P m A hA htA
  have hLJ:L≤J:=by
    refine le_inf inf_le_right ?_
    rw[←hSp]
    exact (le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hf:=R.reflected_line_plane_position h P m A hA htA
  have hLc:Nat.card L=72:=(R.plane_cubic_ambient_data h A hA U m.common_fixed_card hf.2.1 hf.2.2).1
  have hc:Nat.card (J⊓Subgroup.centralizer (S:Set G):Subgroup G)=12:=by
    change Nat.card ((K⊓normalizer (S:Set G))⊓Subgroup.centralizer (S:Set G):Subgroup G)=12
    rw[inf_assoc,inf_eq_right.mpr (centralizer_le_normalizer _)]
    exact (R.reflected_four_common_centralizer h P m ht hs hlocal).2
  let : IsElementaryAbelian 2 S:=(h.reflected_four P m).1
  let : Nontrivial S:=Finite.one_lt_card_iff_nontrivial.mp (by rw[(h.reflected_four P m).2];decide)
  let : IsKleinFour S:=⟨(h.reflected_four P m).2,IsElementaryAbelian.exponent_eq_prime⟩
  have hd:=card_normalizing_subgroup_dvd J S inf_le_right
  rw[hc,IsKleinFour.card_mulAut] at hd
  exact (eq_of_le_of_card_ge hLJ (by rw[hLc];exact Nat.le_of_dvd (by decide) hd)).symm
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
