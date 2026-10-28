module

public import Stellmacher.SectionNine.NineResidualOddCoreEquality
public import Stellmacher.SectionOne.OneSevenOddCoreDerived
public import Stellmacher.UniqueMaximalContainingTransport
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# The geometric local residual is the canonical derived product

Consider a surjective action homomorphism from a genuine Section Nine
vertex stabilizer which kills its two-core. If its range satisfies the
exact Section One module hypotheses and contains a canonical factor,
the image of the geometric two-residual equals the derived subgroup of
the full action-defined canonical product.

The adjacent-edge P-set data give a native Sylow subgroup with a unique
maximal overgroup. Its image remains proper, because the canonical
factor of order six cannot lie in a two-group. Unique maximality descends
through the surjection. The native residual and Sylow generate the local
group, so their images generate the range. The residual-image odd-core
identification and the proved normal complement argument now apply.

This verifies the generation and normality inputs behind Stellmacher
(9.10)(3), printed p.57 of `refs/files/stellmacher-n-group.pdf`. No
identification with a canonical product is included among the hypotheses.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_local_residual_eq_canonical_derived
    {G X V : Type u} [Group G] [Finite G] [Group X] [Finite X]
    [Group V] [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (action : GAt ctx.Γ vertex →* X)
    (hsurj : Function.Surjective action) (hkernel : pCore 2 (GAt ctx.Γ vertex) ≤ action.ker)
    (hyp : SectionOne.Hypotheses X V)
    (factor : Subgroup X) (hfactor : SectionOne.IsOneSevenFactor (V := V) factor) :
    ((EAt ctx.Γ vertex).subgroupOf (GAt ctx.Γ vertex)).map action =
      (commutator (SectionOne.oneSevenGenerated (G := X) (V := V))).map
        (SectionOne.oneSevenGenerated (G := X) (V := V)).subtype := by
  classical
  let P := GAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let edgeSylow : Sylow 2 (P ⊓ GAt ctx.Γ neighbor : Subgroup G) := default
  let S := sylowTwoAmbient (P ⊓ GAt ctx.Γ neighbor) edgeSylow
  have hdata := edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) edgeSylow
  have hPset := hdata.2.1
  obtain ⟨nativeSylow, hnative⟩ := hPset.1.2.1
  have huniq : IsUniqueMaximalContaining (nativeSylow : Subgroup P) ⊤ :=
    native_uniqueMaximalContaining P (nativeSylow : Subgroup P)
      (by rw [hnative]; exact hPset.2)
  let imageSylow := nativeSylow.mapSurjective hsurj
  have hproper : (nativeSylow : Subgroup P).map action ≠ ⊤ := by
    intro htop
    have htwo : IsPGroup 2 X := by
      have h := nativeSylow.isPGroup'.map action
      rw [htop] at h
      exact h.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := (htwo.to_subgroup factor).exists_card_eq
    have hthree : 3 ∣ 2 ^ n := by
      rw [← hn, SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hfactor.1]
      decide
    have hdiv := Nat.prime_three.dvd_of_dvd_pow hthree
    norm_num at hdiv
  have himageUnique := uniqueMaximalContaining_map_of_ne_top action hsurj
    (nativeSylow : Subgroup P) huniq hproper
  have hEeq : E = twoResidualAmbient P := ctx.Γ.twoResidualAt_def vertex
  have hEP : E ≤ P := by
    rw [hEeq]
    exact Subgroup.map_subtype_le _
  have hnativeGen : E.subgroupOf P ⊔ (nativeSylow : Subgroup P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEP, hnative,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hEeq]
    exact SectionThree.twoResidual_sup_sylowImage
      (show IsSylowSubgroupIn S P from ⟨nativeSylow, hnative⟩)
  have himage := nine_local_residual_image_eq_oddCore ctx vertex neighbor hadj
    action hsurj hkernel
  have hgen : SectionOne.oddCore X ⊔ (imageSylow : Subgroup X) = ⊤ := by
    rw [← himage]
    change (E.subgroupOf P).map action ⊔ (nativeSylow : Subgroup P).map action = ⊤
    rw [← Subgroup.map_sup, hnativeGen, Subgroup.map_top_of_surjective action hsurj]
  rw [himage]
  exact SectionOne.oneSeven_oddCore_eq_derived_of_unique_maximal hyp imageSylow
    hgen himageUnique factor hfactor

end Stellmacher.SectionNine
