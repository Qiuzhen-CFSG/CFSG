module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Residual supplements and centralization

The image of a Sylow p-subgroup is the whole p-group quotient by the
p-residual. This gives the residual/Sylow supplement and a centralization
criterion for normal subgroups. Conversely, adjoining a normalizing
two-group to a two-perfect group leaves its embedded two-residual unchanged.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, the S₃ branch of Theorem 15.3.1, printed p.1155 (PDF p.1172).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow subgroup supplements the prime residual in a finite group. -/
theorem pResidual_sup_sylow_eq_top {p : ℕ} [Fact p.Prime] (T : Sylow p G) :
    pResidual p G ⊔ (T : Subgroup G) = ⊤ := by
  let q := QuotientGroup.mk' (pResidual p G)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pResidual p G))
  have hp : IsPGroup p (⊤ : Subgroup (G ⧸ pResidual p G)) :=
    (isPGroup_quotient_pResidual p).to_subgroup ⊤
  have hmap : (T : Subgroup G).map q = ⊤ :=
    top_unique (hp.le_sylow_of_normal S)
  have h := congrArg (fun K : Subgroup (G ⧸ pResidual p G) => K.comap q) hmap
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using h

/-- Centralizing the residual and an ambient Sylow subgroup centralizes the normal group. -/
theorem centralizes_normal_of_centralizes_pResidual_and_sylow {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (X Z : Subgroup G) [X.Normal]
    (hZR : Z ≤ centralizer ((pResidual p X).map X.subtype : Set G))
    (hZT : Z ≤ centralizer (T : Set G)) : Z ≤ centralizer (X : Set G) := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal X
  have hs := congrArg (fun K : Subgroup X => K.map X.subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hS, subgroupOf_map_subtype] at hs
  apply le_centralizer_iff.mpr
  rw [← hs]
  exact sup_le (le_centralizer_iff.mp hZR)
    (inf_le_left.trans (le_centralizer_iff.mp hZT))
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

/-- Adjoining a normalizing two-group preserves the embedded two-residual. -/
theorem embedded_pResidual_join_pGroup (E T : Subgroup G)
    (hE : IsPPerfect 2 E) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (E : Set G)) :
    (pResidual 2 (E ⊔ T : Subgroup G)).map (E ⊔ T).subtype = E := by
  let L := E ⊔ T
  have hEL : E ≤ L := le_sup_left
  have hTL : T ≤ L := le_sup_right
  let _ : (E.subgroupOf L).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le E.le_normalizer hn)
  have hp : IsPPerfect 2 (E.subgroupOf L) :=
    hE.of_surjective (subgroupOfEquivOfLe hEL).symm.toMonoidHom
      (subgroupOfEquivOfLe hEL).symm.surjective
  have hgen : E.subgroupOf L ⊔ T.subgroupOf L = ⊤ := by
    apply (map_injective L.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hEL, map_subgroupOf_eq_of_le hTL,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [pResidual_eq_of_isPPerfect_sup (E.subgroupOf L) (T.subgroupOf L)
    hp hT.comap_subtype hgen, map_subgroupOf_eq_of_le hEL]

end Subgroup
