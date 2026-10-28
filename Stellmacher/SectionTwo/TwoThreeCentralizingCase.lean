module
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian

/-!
# The centralizing case of Stellmacher (2.3)

Under the Section 2 hypotheses and O₂(G)=C_S(V), if V centralizes J(S),
the Baumann subgroup B is Sylow in its normal closure.

The maximal-elementary argument puts V in Ω₁(Z(J(S))), hence B in O₂(G).
Baumann heredity identifies B with the Baumann subgroup of O₂(G), whose
normalizer contains G. Thus B is normal, its normal closure equals B,
and its two-group structure supplies the Sylow witness.

This proves the first paragraph of (2.3), journal p.20 of
`refs/latex/stellmacher-n-group.tex`, independently of the noncentralizing
case and of (2.2).
-/

namespace Stellmacher.SectionTwo

public theorem lemma_two_three_of_v_centralizes_j
    {G : Type*} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G =
      (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (B L : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hL : L = Subgroup.normalClosure (B : Set G))
    (hcent : vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    ∃ P : Sylow 2 L, P.map L.subtype = B := by
  obtain ⟨hVcore,hVe⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let _ : IsElementaryAbelian 2 (vSubgroup S) := hVe
  have hcoreS : pCore 2 G ≤ (S : Subgroup G) := fitting_pCore_le_sylow S
  have hVZ := elementary_centralizer_maxJ_le_omegaCenter (S : Subgroup G)
    (vSubgroup S) (hVcore.trans hcoreS) hcent
  have hBcore : B ≤ pCore 2 G := by
    rw [hcore, hB]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hVZ)
  have hBcoreEq : B = pCore 2 G ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (pCore 2 G)) : Set G) := by
    rw [hB] at hBcore ⊢
    exact (baumann_eq_of_intermediate (S : Subgroup G) (pCore 2 G) hBcore hcoreS).symm
  have hBN : B.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [hBcoreEq]
    exact (show (⊤ : Subgroup G) ≤ Subgroup.normalizer (pCore 2 G : Set G) by
      rw [Subgroup.normalizer_eq_top]).trans (normalizer_le_normalizer_baumann _)
  let _ : B.Normal := hBN
  have hLB : L = B := by
    rw [hL]
    exact le_antisymm (Subgroup.normalClosure_le_normal le_rfl) Subgroup.le_normalClosure
  have hLp : IsPGroup 2 L := S.isPGroup'.to_le (hLB ▸ hBcore.trans hcoreS)
  have htopP : IsPGroup 2 (⊤ : Subgroup L) :=
    hLp.of_injective (⊤ : Subgroup L).subtype (⊤ : Subgroup L).subtype_injective
  obtain ⟨P,hP⟩ := htopP.exists_le_sylow
  refine ⟨P, ?_⟩
  have hPeq : (P : Subgroup L) = ⊤ := top_unique hP
  change (P : Subgroup L).map L.subtype = B
  rw [hPeq, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hLB]

end Stellmacher.SectionTwo

