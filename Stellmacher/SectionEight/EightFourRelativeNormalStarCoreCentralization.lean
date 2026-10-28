module
public import Stellmacher.SectionEight.EightFourNormalStarCoreCentralization
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Normal-star residual-core centralization inside an ambient subgroup

Apply the normal-star core-centralization theorem inside the literal subgroup
P and transport its conclusion to the ambient group. The normal subgroups Z
and MZ are only normal inside P. Both two-group supplement equalities and
commutator hypotheses use the supplied ambient subgroups. Their containment
in P is either explicit for M and Z or follows from the supplement equalities.

The subtype embedding identifies the native two-residual with O²(P). Its
induced group equivalence carries the native two-core to the actual two-core
of O²(P), and the induced quotient equivalence transfers the odd-order
hypothesis. Subgroup maps preserve the two generation equalities and the
commutators; native core normalization follows pointwise. The proved native
theorem then maps back to the exact ambient commutator with O₂(O²(P)).

This is the endpoint-stabilizer application in source (8) of Stellmacher
(8.4), Journal of Algebra190 (1997), printed p39,
`refs/files/stellmacher-n-group.pdf`. It imposes no containment of M in a
smaller factor join and does not replace the actual core or quotient.
-/

namespace Stellmacher.SectionEight
open SectionsFiveToSeven
/-- Transport the normal-star core-centralization theorem through the actual ambient subgroup. -/
public theorem eight_four_relative_normal_star_core_centralization
    {G : Type*} [Group G] [Finite G]
    (P M Z A B T U : Subgroup G)
    (hMP : M ≤ P) (hZP : Z ≤ P)
    (hZn : (Z.subgroupOf P).Normal) (hMZn : ((M ⊔ Z).subgroupOf P).Normal)
    (hAT : A ⊔ T = P) (hBU : B ⊔ U = P)
    (hT : IsPGroup 2 T) (hU : IsPGroup 2 U)
    (hMA : ⁅M,A⁆ ≤ Z) (hMB : ⁅M,B⁆ = ⊥)
    (hQM : twoCoreIn (twoResidualIn P) ≤ Subgroup.normalizer M)
    (hZQ : ⁅Z,twoCoreIn (twoResidualIn P)⁆ = ⊥)
    (hodd : Odd (Nat.card (twoResidualIn P ⧸ pCore 2 (twoResidualIn P)))) :
    ⁅M,twoCoreIn (twoResidualIn P)⁆ = ⊥ := by
  let RP := twoResidualAmbient (⊤ : Subgroup P)
  let R := twoResidualIn P
  have hmapR : RP.map P.subtype = R :=
    map_twoResidualAmbient_of_subgroup_image ⊤ P.subtype P
      (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
  let eR : RP ≃* R := (RP.equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hmapR)
  have hcomp : R.subtype.comp eR.toMonoidHom = P.subtype.comp RP.subtype := by ext r; rfl
  have hcores : (pCore 2 RP).map eR.toMonoidHom = pCore 2 R := pCore_map_iso 2 eR
  have hmapQ : (twoCoreIn RP).map P.subtype = twoCoreIn R := by
    unfold twoCoreIn
    rw [← hcores,Subgroup.map_map,Subgroup.map_map,hcomp]
  have hoddP : Odd (Nat.card (RP ⧸ pCore 2 RP)) := by
    rw [Nat.card_congr (QuotientGroup.congr (pCore 2 RP) (pCore 2 R) eR hcores).toEquiv]
    exact hodd
  have hAP : A ≤ P := le_sup_left.trans_eq hAT
  have hTP : T ≤ P := le_sup_right.trans_eq hAT
  have hBP : B ≤ P := le_sup_left.trans_eq hBU
  have hUP : U ≤ P := le_sup_right.trans_eq hBU
  let _ : (Z.subgroupOf P).Normal := hZn
  let _ : (M.subgroupOf P ⊔ Z.subgroupOf P).Normal := by
    rw [← Subgroup.subgroupOf_sup hMP hZP]
    exact hMZn
  have hATP : A.subgroupOf P ⊔ T.subgroupOf P = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hAP,
      Subgroup.map_subgroupOf_eq_of_le hTP,← MonoidHom.range_eq_map,Subgroup.range_subtype,hAT]
  have hBUP : B.subgroupOf P ⊔ U.subgroupOf P = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hBP,
      Subgroup.map_subgroupOf_eq_of_le hUP,← MonoidHom.range_eq_map,Subgroup.range_subtype,hBU]
  have hMAP : ⁅M.subgroupOf P,A.subgroupOf P⁆ ≤ Z.subgroupOf P := by
    intro x hx
    have hm := Subgroup.mem_map_of_mem P.subtype hx
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hMP,
      Subgroup.map_subgroupOf_eq_of_le hAP] at hm
    exact hMA hm
  have hMBP : ⁅M.subgroupOf P,B.subgroupOf P⁆ = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hMP,
      Subgroup.map_subgroupOf_eq_of_le hBP,Subgroup.map_bot,hMB]
  have hQMP : twoCoreIn RP ≤ Subgroup.normalizer (M.subgroupOf P) := by
    intro q hq
    apply Subgroup.mem_normalizer_iff.mpr
    intro m
    have hqm : (q : G) ∈ Subgroup.normalizer M := hQM
      (hmapQ ▸ Subgroup.mem_map_of_mem P.subtype hq)
    exact Subgroup.mem_normalizer_iff.mp hqm m
  have hZQP : ⁅Z.subgroupOf P,twoCoreIn RP⁆ = ⊥ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hZP,
      hmapQ,Subgroup.map_bot]
    exact hZQ
  have hresult := eight_four_normal_star_core_centralization
    (M.subgroupOf P) (Z.subgroupOf P) (A.subgroupOf P) (B.subgroupOf P)
    (T.subgroupOf P) (U.subgroupOf P) hATP hBUP hT.comap_subtype hU.comap_subtype
    hMAP hMBP hQMP hZQP hoddP
  have hm := congrArg (Subgroup.map P.subtype) hresult
  rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hMP,Subgroup.map_bot] at hm
  change ⁅M,(twoCoreIn RP).map P.subtype⁆ = ⊥ at hm
  rwa [hmapQ] at hm
end Stellmacher.SectionEight
