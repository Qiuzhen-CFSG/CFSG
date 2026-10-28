module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.Flag
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Residual generation along the marked flag

The original Sylow T lies in every ordered flag stabilizer and supplements
its two-residual. T normalizes each residual and each initial join H_i;
the joins are two-perfect. Hence H_i is exactly O²(H_i T), and ordinary
flag-stabilizer generation implies H_(n-1)=L when L is two-perfect and
normalized by T. This lifts the geometry through the actual kernels.

For n=2, P=LT gives H₁=L directly. The preceding 12.8.9(1) residual
identity then proves [L,Z(I₂)]=1 without further induction assumptions.

Source: Aschbacher–Smith, Lemma 12.8.10(5), printed p.854 (PDF p.871),
with the two-residual convention from Hypothesis 12.8.1(2).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem isPPerfect_iSup {ι : Sort*} (A : ι → Subgroup G)
    (hA : ∀ i, IsPPerfect 2 (A i)) : IsPPerfect 2 (⨆ i, A i : Subgroup G) := by
  let K := ⨆ i, A i
  apply (pResidual_eq_top_iff 2 K).mp
  apply map_injective K.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  apply le_antisymm (map_subtype_le _) (iSup_le fun i => ?_)
  have hi : A i ≤ K := le_iSup A i
  have hp : IsPPerfect 2 ((A i).subgroupOf K) := (hA i).of_surjective
    (subgroupOfEquivOfLe hi).symm.toMonoidHom (subgroupOfEquivOfLe hi).symm.surjective
  have hh := map_mono (f := K.subtype) (le_pResidual_of_isPPerfect ((A i).subgroupOf K) hp)
  rwa [map_subgroupOf_eq_of_le hi] at hh

public theorem sylow_le_orderedParabolic (F : InvariantFlag T V n) (L : Subgroup G) (j : ℕ) :
    (T : Subgroup G) ≤ F.orderedParabolic L j := by
  apply le_inf le_sup_right
  apply le_iInf; intro i; apply le_iInf; intro _
  exact F.invariant i

public theorem orderedResidual_sup_sylow (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (j : ℕ) :
    F.orderedResidual L j ⊔ (T : Subgroup G) = F.orderedParabolic L j := by
  have hh := congrArg (fun A : Subgroup (F.orderedParabolic L j) =>
    A.map (F.orderedParabolic L j).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype (F.sylow_le_orderedParabolic L j)))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le (F.sylow_le_orderedParabolic L j), ← MonoidHom.range_eq_map, range_subtype,
    orderedResidual] using hh

public theorem sylow_normalizes_initialResiduals (F : InvariantFlag T V n)
    (L : Subgroup G) (i : ℕ) :
    (T : Subgroup G) ≤ normalizer (F.initialResiduals L i : Set G) := by
  have hn (j : ℕ) : F.orderedParabolic L j ≤ normalizer (F.orderedResidual L j : Set G) := by
    have hh := (pResidual 2 (F.orderedParabolic L j)).le_normalizer_map
      (F.orderedParabolic L j).subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  simp only [initialResiduals, Subgroup.map_iSup]
  apply iSup_congr; intro j
  apply iSup_congr; intro _
  exact mem_normalizer_iff_map_conj_eq.mp (hn j (F.sylow_le_orderedParabolic L j ht))

public theorem initialResiduals_isPPerfect (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (i : ℕ) : IsPPerfect 2 (F.initialResiduals L i) := by
  exact isPPerfect_iSup _ (fun j => isPPerfect_iSup _
    (fun _ => F.orderedResidual_isPPerfect L j))

public theorem initialResiduals_eq_residual (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (i : ℕ) :
    (pResidual 2 (F.initialResiduals L i ⊔ (T : Subgroup G) : Subgroup G)).map
      (F.initialResiduals L i ⊔ (T : Subgroup G)).subtype = F.initialResiduals L i :=
  embedded_pResidual_join_pGroup _ _ (F.initialResiduals_isPPerfect L i)
    T.isPGroup' (F.sylow_normalizes_initialResiduals L i)

/-- The ordinary flag-stabilizer generation implies terminal residual equality;
there is no extra residual-generation hypothesis. -/
public theorem initialResiduals_terminal_of_parabolic_generation (F : InvariantFlag T V n)
    [Finite G] (hn : 2 ≤ n) (L : Subgroup G) (hL : IsPPerfect 2 L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hgen : (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.orderedParabolic L j) =
      L ⊔ (T : Subgroup G)) : F.initialResiduals L (n - 1) = L := by
  have he : F.initialResiduals L (n - 1) ⊔ (T : Subgroup G) = L ⊔ (T : Subgroup G) := by
    apply le_antisymm
    · apply sup_le _ le_sup_right
      apply iSup_le; intro j; apply iSup_le; intro _
      exact (F.orderedResidual_le L j).trans inf_le_left
    · rw [← hgen]
      apply iSup_le; intro j; apply iSup_le; intro hj
      rw [← F.orderedResidual_sup_sylow L j]
      apply sup_le _ le_sup_right
      apply le_sup_of_le_left
      exact le_iSup_of_le j (le_iSup_of_le (show 1 ≤ j ∧ j ≤ n - 1 by omega) le_rfl)
  calc
    F.initialResiduals L (n - 1) =
        (pResidual 2 (F.initialResiduals L (n - 1) ⊔ (T : Subgroup G) : Subgroup G)).map
          (F.initialResiduals L (n - 1) ⊔ (T : Subgroup G)).subtype :=
      (F.initialResiduals_eq_residual L (n - 1)).symm
    _ = (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype := by rw [he]
    _ = L := embedded_pResidual_join_pGroup _ _ hL T.isPGroup' hTL

/-- In rank two P=LT, and its two-residual is the original L. -/
public theorem initialResiduals_rankTwo (F : InvariantFlag T V 2) (L : Subgroup G)
    (hL : IsPPerfect 2 L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    F.initialResiduals L 1 = L := by
  rw [F.initialResiduals_one, orderedResidual, F.orderedParabolic_one, F.P_rankTwo]
  exact embedded_pResidual_join_pGroup _ _ hL T.isPGroup' hTL

/-- The n=2 source branch needs no induction and no containment of Z(U)^g.
The residual identity is precisely the residual clause of 12.8.9(1). -/
public theorem center_centralized_rankTwo (F : InvariantFlag T V 2) (L : Subgroup G)
    (hL : IsPPerfect 2 L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hresidual : (pResidual 2 (F.P L)).map (F.P L).subtype =
      (pResidual 2 (F.I₂ L)).map (F.I₂ L).subtype) :
    ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  have hLP : (pResidual 2 (F.P L)).map (F.P L).subtype = L := by
    rw [F.P_rankTwo]
    exact embedded_pResidual_join_pGroup _ _ hL T.isPGroup' hTL
  have hLI : L ≤ F.I₂ L := calc
    L = (pResidual 2 (F.P L)).map (F.P L).subtype := hLP.symm
    _ = (pResidual 2 (F.I₂ L)).map (F.I₂ L).subtype := hresidual
    _ ≤ F.I₂ L := map_subtype_le _
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply hLI.trans
  apply le_centralizer_iff.mpr
  rintro x ⟨z, hz, rfl⟩ a ha
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
