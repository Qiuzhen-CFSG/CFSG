module
public import FeitThompson.BGsection1.theorem_1_17
public import Theory.GroupTheory.SylowNormalIntersection
public import BenderSuzuki.External.Suzuki.V.theorem_2_10
public import BenderSuzuki.External.Huppert.IV.ComplementTransfer

/-!
# A cyclic focal subgroup yields a normal two-complement

For a finite group G with Sylow two-subgroup P, cyclicity of the focal
subgroup of P implies that G has a normal two-complement. This is the
normal-complement step in Alperin–Brauer–Gorenstein, Chapter II, Section 1,
Proposition 1(iv), article pp.10–11 of
`refs/latex/alperin-brauer-gorenstein.tex`. In the quasi-dihedral application,
the two local automizer indices equal two and the focal subgroup becomes
the cyclic derived subgroup of P. Only focal cyclicity is needed here.

Use the existing focal transfer to P modulo its focal subgroup. Its actual
kernel K meets P in the focal subgroup. Restricting P to normal K therefore
produces a cyclic Sylow two-subgroup of K. If K has even order, Burnside's
cyclic-Sylow transfer theorem applies because two is its least prime divisor;
if K has odd order, K itself is its normal two-complement. The quotient G/K
embeds in the two-group transfer target. The proved normal-complement
extension theorem now lifts the normal two-complement from K to G.
The proof retains the actual subgroup inclusions and their equivalences,
and uses the existing Feit–Thompson focal definitions throughout.
-/

namespace ABG
open BenderSuzuki.External

/-- A finite group with cyclic Sylow-two focal subgroup has a normal two-complement. -/
public theorem hasNormalTwoComplement_of_cyclic_focalSubgroupOf
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcyclic : IsCyclic ((P : Subgroup G).focalSubgroupOf)) :
    HasNormalPComplement 2 G := by
  let f := (P : Subgroup G).transferFocal
  let K := f.ker
  have hKP : K ⊓ (P : Subgroup G) = (P : Subgroup G).focalSubgroup :=
    Subgroup.ker_transferFocal_inf_eq_focalSubgroup P
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal K
  have hmap : (R : Subgroup K).map K.subtype =
      ((P : Subgroup G).focalSubgroupOf).map (P : Subgroup G).subtype := by
    rw [hR, Subgroup.subgroupOf_map_subtype, inf_comm, hKP,
      Subgroup.map_focalSubgroupOf]
  let e : R ≃* (P : Subgroup G).focalSubgroupOf :=
    ((R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
      ((MulEquiv.subgroupCongr hmap).trans
        (((P : Subgroup G).focalSubgroupOf).equivMapOfInjective
          (P : Subgroup G).subtype (P : Subgroup G).subtype_injective).symm)
  let : IsCyclic ((P : Subgroup G).focalSubgroupOf) := hcyclic
  have hRcyclic : IsCyclic R := isCyclic_of_injective e.toMonoidHom e.injective
  have hKcomp : HasNormalPComplement 2 K := by
    by_cases htwo : 2 ∣ Nat.card K
    · exact Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1 R
        ((Nat.minFac_eq_two_iff (Nat.card K)).mpr htwo) hRcyclic
    · exact hkt_hasNormalPComplement_of_not_dvd_card htwo
  have htarget : IsPGroup 2 (P ⧸ (P : Subgroup G).focalSubgroupOf) :=
    P.isPGroup'.to_quotient _
  have hquot : IsPGroup 2 (G ⧸ K) :=
    (htarget.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient K hquot hKcomp
end ABG
