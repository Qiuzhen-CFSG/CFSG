module
public import Stellmacher.SectionFour.NormalSupplement

/-!
# Generation by the Baumann closure in Stellmacher (4.6)

For a critical pair `(P, Pstar)` with `P ≤ C`, assume the residual-core
product `E = O²(Pstar)O₂(C)` has `O₂(C)` as a Sylow 2-subgroup, and retain
the solvability and characteristic-2 hypotheses of the Baumann configuration.
The normal closure in `Pstar` of the literal subgroup
`B = C_{O₂(C)}(Ω₁(Z(J(O₂(C)))))`, together with the original Sylow `S`,
generates `Pstar`.

The normal-supplement data shows that `S` normalizes `B` and `E S = Pstar`.
The critical pair prevents `Pstar` from normalizing `B`, so the full
commutator theorem (3.4) gives `[O²(Pstar), B] = O²(Pstar)`. Normality of
the closure then puts the residual in that closure. The residual and `S`
generate `Pstar`, yielding the claim used for factor elimination in (4.6).

Source: `refs/latex/stellmacher-n-group.tex`, proof of (4.6), journal page 26,
from the definition of `L` through the assertion `LS = Pstar`.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour

/-- The actual Baumann closure and the fixed Sylow generate the partner. -/
public theorem baumann_closure_sup_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
    L.map Pstar.subtype ⊔ (S : Subgroup G) = Pstar := by
  let Q := twoCoreAmbient (cSubgroup S)
  let B := Q ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
  obtain ⟨_, _, _, _, SP, QE, hSP, hQmap, hgen, hQS, _, _⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hSPstar : (S : Subgroup G) ≤ Pstar := hSP ▸ Subgroup.map_subtype_le _
  have hQSambient := Subgroup.map_mono (f := Pstar.subtype) hQS
  rw [hQmap, hSP] at hQSambient
  have hSC : (S : Subgroup G) ≤ cSubgroup S := by
    obtain ⟨T, hT⟩ := hpair.1.1.2.1
    exact (hT ▸ Subgroup.map_subtype_le _).trans hPC
  have hQnormal : (Q.subgroupOf (cSubgroup S)).Normal := by
    rw [show Q = (pCore 2 (cSubgroup S)).map (cSubgroup S).subtype from rfl,
      subgroupOf_map_subtype_eq]
    infer_instance
  have hSNQ : (S : Subgroup G) ≤ Subgroup.normalizer Q := hSC.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hQnormal)
  have hSNB : (S : Subgroup G) ≤ Subgroup.normalizer B :=
    hSNQ.trans (normalizer_le_normalizer_baumann Q)
  have hBS : B ≤ (S : Subgroup G) := inf_le_left.trans hQSambient
  have hBN : (B.subgroupOf (S : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mpr hSNB
  have hES : E ⊔ (S : Subgroup G) = Pstar := by
    have hm := congrArg (Subgroup.map Pstar.subtype) hgen
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEP, hSP,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
    exact hm
  have hcomm : ⁅twoResidualAmbient Pstar, B⁆ = twoResidualAmbient Pstar :=
    baumann_partner_full_commutator (S : Subgroup G)
      ⟨heven, S.ne_bot_of_dvd_card heven.two_dvd, S.isPGroup'⟩
      Pstar Q E B hpair.2.1 hsolv hEP hES.ge hSyl rfl hBS hBN
      (baumann_not_normalized_by_partner S heven P Pstar hpair hPC)
  have hBPstar : B ≤ Pstar := hBS.trans hSPstar
  have hRL : twoResidualAmbient Pstar ≤ L.map Pstar.subtype := by
    rw [← hcomm]
    have hRP : twoResidualAmbient Pstar ≤ Pstar := Subgroup.map_subtype_le _
    rw [← Subgroup.map_subgroupOf_eq_of_le hRP,
      ← Subgroup.map_subgroupOf_eq_of_le hBPstar, ← Subgroup.map_commutator]
    exact Subgroup.map_mono ((Subgroup.commutator_mono le_rfl Subgroup.le_normalClosure).trans
      (Subgroup.commutator_le_right _ L))
  change L.map Pstar.subtype ⊔ (S : Subgroup G) = Pstar
  apply le_antisymm (sup_le (Subgroup.map_subtype_le _) hSPstar)
  have hRS : twoResidualAmbient Pstar ⊔ (S : Subgroup G) = Pstar :=
    SectionThree.twoResidual_sup_sylowImage hpair.2.1.1.2.1
  calc
    Pstar = twoResidualAmbient Pstar ⊔ (S : Subgroup G) := hRS.symm
    _ ≤ L.map Pstar.subtype ⊔ (S : Subgroup G) := sup_le_sup hRL le_rfl

end Stellmacher.SectionFour
