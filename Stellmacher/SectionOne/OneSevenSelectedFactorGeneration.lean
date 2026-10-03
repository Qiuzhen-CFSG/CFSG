module
public import Stellmacher.SectionOne.OneSevenIdentification

/-!
# A canonical one-seven factor generating with the Sylow subgroup

Under the Section 1 module hypotheses, suppose the one-seven product together
with the Sylow subgroup generates the group, and that Sylow subgroup has a
unique maximal overgroup. Then one of the actual canonical one-seven factors
already generates the group together with the Sylow subgroup.

If every individual factor joined with the Sylow subgroup were proper, each
join would lie in the unique maximal overgroup. The global identification of
`oneE` with the join of all canonical factors would then place the whole group
in that proper maximal subgroup, a contradiction. The proof also rules out an
empty factor family; it does not require a separate nonemptiness assumption.

This is the unique-maximal selection from Stellmacher (1.7) used in the local
module argument of (9.3), Journal of Algebra 190 (1997), p.50. Its factor family
and module hypotheses are the production Section 1 definitions.
-/

namespace Stellmacher.SectionOne
universe u

private theorem le_unique_maximal_ambient
    {G : Type u} [Group G] [Finite G]
    {S K : Subgroup G} {M : Subgroup (⊤ : Subgroup G)}
    (huniq : ∀ M' : Subgroup (⊤ : Subgroup G), IsCoatom M' →
      S ≤ M'.map (⊤ : Subgroup G).subtype → M' = M)
    (hSK : S ≤ K) (hKne : K ≠ ⊤) :
    K ≤ M.map (⊤ : Subgroup G).subtype := by
  have hKsub_ne : K.subgroupOf (⊤ : Subgroup G) ≠ ⊤ := by
    intro htop
    apply hKne
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show K ≤ (⊤ : Subgroup G) from le_top), htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨M', hM'coat, hKM'⟩ :=
    (eq_top_or_exists_le_coatom (K.subgroupOf (⊤ : Subgroup G))).resolve_left hKsub_ne
  have hSM' : S ≤ M'.map (⊤ : Subgroup G).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show K ≤ (⊤ : Subgroup G) from le_top)] at hSK
    exact hSK.trans (Subgroup.map_mono hKM')
  rw [← huniq M' hM'coat hSM']
  rw [← Subgroup.map_subgroupOf_eq_of_le
    (show K ≤ (⊤ : Subgroup G) from le_top)]
  exact Subgroup.map_mono hKM'

public theorem oneSeven_exists_factor_sup_sylow_eq_top
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hgen : oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    ∃ D ∈ oneSevenFactors (G := G) (V := V), D ⊔ (S : Subgroup G) = ⊤ := by
  classical
  obtain ⟨M, hMcoat, hSM, huniq⟩ := hunique
  by_contra! hproper
  have hDM (D : Subgroup G) (hD : D ∈ oneSevenFactors (G := G) (V := V)) :
      D ≤ M.map (⊤ : Subgroup G).subtype :=
    le_sup_left.trans (le_unique_maximal_ambient huniq le_sup_right (hproper D hD))
  have hEM : oneSevenGenerated (G := G) (V := V) ≤
      M.map (⊤ : Subgroup G).subtype := by
    apply sSup_le
    intro D hD
    exact hDM D ((mem_oneSevenFactors_iff D).mpr hD)
  have htop : (⊤ : Subgroup G) ≤ M.map (⊤ : Subgroup G).subtype := by
    calc
      (⊤ : Subgroup G) = oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) := hgen.symm
      _ = oneSevenGenerated (V := V) ⊔ (S : Subgroup G) := by
        rw [(oneSeven_global_identification h S).2]
      _ ≤ M.map (⊤ : Subgroup G).subtype := sup_le hEM hSM
  have hMtop : M = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    apply le_antisymm
    · exact Subgroup.map_mono le_top
    · simpa [← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  exact hMcoat.1 hMtop

end Stellmacher.SectionOne
