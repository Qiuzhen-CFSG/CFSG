module
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.SL2ProductSylowCoordinates

/-!
# The full one-seven group with a Sylow subgroup of order two

Under the Section 1 action hypotheses, if E(V,S) is the whole group and
S has order two, the group is SL₂(2). This is the rank-one step in the
faithful local quotient argument at the start of Stellmacher (8.2),
Journal of Algebra 190 (1997), p.37.

The proved global factor identification expresses E as a normal product of
one-seven factors. Its Sylow intersection has order 2 to the number of
factors. The given Sylow order forces one factor, and E=G identifies that
SL₂(2) factor with the whole group. The hypotheses E=G and |S|=2 are
explicit: the later dihedral-quotient bridge must supply them separately.
-/

namespace Stellmacher.SectionOne
universe u

public theorem isSL2Two_of_oneE_eq_top_of_sylow_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : Nat.card S = 2)
    (hE : oneE (V := V) (S : Subgroup G) = ⊤) : IsSL2Two G := by
  classical
  let F := oneSevenFactors (G := G) (V := V)
  let E := oneSevenGenerated (G := G) (V := V)
  obtain ⟨hEnormal, hprod, _⟩ := oneSeven_global_product h S
  change IsInternalDirectProduct E F at hprod
  have hEtop : E = ⊤ := (oneSeven_global_identification h S).2.symm.trans hE
  have hF : ∀ D ∈ F, IsSL2Two D :=
    fun D hD => ((mem_oneSevenFactors_iff D).mp hD).1
  have hcard := (sl2_product_sylow_coordinates S E hEnormal F hprod hF).2.2.1
  rw [hEtop, inf_top_eq, hS] at hcard
  have hFcard : F.card = 1 := by
    apply (Nat.pow_right_injective (by decide : 1 < 2))
    simpa using hcard.symm
  obtain ⟨D, hFD⟩ := Finset.card_eq_one.mp hFcard
  have hDin : D ∈ F := by rw [hFD]; simp
  have hDE : D = E := by
    apply le_antisymm
    · rw [hprod.1]
      exact le_iSup (fun K : {K : Subgroup G // K ∈ F} => K.val) ⟨D, hDin⟩
    · rw [hprod.1]
      apply iSup_le
      intro K
      have hKD : K.val = D := by simpa [hFD] using K.property
      rw [hKD]
  have hD := hF D hDin
  rw [hDE, hEtop] at hD
  obtain ⟨e⟩ := hD
  exact ⟨Subgroup.topEquiv.symm.trans e⟩

end Stellmacher.SectionOne
