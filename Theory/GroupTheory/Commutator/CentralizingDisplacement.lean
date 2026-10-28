module

public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Normality of commutators from centralizing displacement

If T normalizes Z and its commutators with A centralize Z, T normalizes
[A,Z]. An abelian overgroup of A then gives normality in its join with T.
For a transitive family of seeds, each resulting commutator lies in every
seed and centralizes the conjugate span of any core centralized by a seed.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.1(i), printed p.133. The graph application is in
`DGS85.CommutingNontrivial.Neighborhood`.
-/

public section

open Subgroup
open scoped commutatorElement

namespace Subgroup

variable {G : Type*} [Group G]

theorem normalizes_commutator_of_centralizing_displacement
    (T A Z : Subgroup G) (hTZ : T ≤ normalizer (Z : Set G))
    (hAZ : A ≤ normalizer (Z : Set G))
    (hTA : ⁅T, A⁆ ≤ centralizer (Z : Set G)) :
    T ≤ normalizer ((⁅A, Z⁆ : Subgroup G) : Set G) := by
  have hHZ : ⁅A, Z⁆ ≤ Z := le_normalizer_iff_commutator_le_right.mp hAZ
  apply le_normalizer_iff.mpr
  intro t ht
  have hmap : (⁅A, Z⁆).map (MulAut.conj t).toMonoidHom ≤ ⁅A, Z⁆ := by
    rw [map_commutator]
    apply commutator_le.mpr
    rintro _ ⟨a, ha, rfl⟩ _ ⟨z, hz, rfl⟩
    have hz' : t * z * t⁻¹ ∈ Z := le_normalizer_iff.mp hTZ t ht z hz
    have hc : ⁅t, a⁆ ∈ centralizer (Z : Set G) :=
      hTA (commutator_mem_commutator ht ha)
    have hca : t * a * t⁻¹ = ⁅t, a⁆ * a := by
      simp [commutatorElement_def, mul_assoc]
    change ⁅t * a * t⁻¹, t * z * t⁻¹⁆ ∈ ⁅A, Z⁆
    rw [hca, commutatorElement_mul_left_eq_conj_mul]
    have hcz : ⁅⁅t, a⁆, t * z * t⁻¹⁆ = 1 :=
      (commutatorElement_eq_one_iff_mul_comm).mpr
        (mem_centralizer_iff.mp hc _ hz').symm
    have hch := mem_centralizer_iff.mp hc _
      (hHZ (commutator_mem_commutator ha hz'))
    rw [hcz, mul_one, ← hch, mul_assoc, mul_inv_cancel, mul_one]
    exact commutator_mem_commutator ha hz'
  intro h hh
  exact hmap (mem_map_of_mem (MulAut.conj t).toMonoidHom hh)

theorem commutator_normalized_of_abelian_join
    (V A Z T L : Subgroup G) [IsMulCommutative V]
    (hAV : A ≤ V) (hZV : Z ≤ normalizer (V : Set G))
    (hTZ : T ≤ normalizer (Z : Set G))
    (hAZ : A ≤ normalizer (Z : Set G))
    (hTA : ⁅T, A⁆ ≤ centralizer (Z : Set G)) (hgen : V ⊔ T = L) :
    L ≤ normalizer ((⁅A, Z⁆ : Subgroup G) : Set G) := by
  have hHV : ⁅A, Z⁆ ≤ V := (commutator_mono hAV le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hZV)
  rw [← hgen]
  exact sup_le (((le_centralizer V).trans (centralizer_le hHV)).trans
    (centralizer_le_normalizer _))
    (normalizes_commutator_of_centralizing_displacement T A Z hTZ hAZ hTA)

theorem commutator_iSup_eq_iSup_of_normalized_seeds {ι : Sort*}
    (L A : Subgroup G) (Z : ι → Subgroup G)
    (hZL : ∀ i, Z i ≤ L)
    (hn : ∀ i, L ≤ normalizer ((⁅A, Z i⁆ : Subgroup G) : Set G)) :
    ⁅A, ⨆ i, Z i⁆ = ⨆ i, ⁅A, Z i⁆ := by
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_iSup_le_of_relative_normal L A _ Z
      ((le_iInf hn).trans (iInf_normalizer_le_normalizer_iSup _)) hZL
    intro i
    rw [commutator_comm]
    exact le_iSup (fun j => ⁅A, Z j⁆) i
  · exact iSup_le fun i => commutator_mono le_rfl (le_iSup Z i)

theorem normal_subgroup_le_conjugate
    (L H Z : Subgroup G) (hn : L ≤ normalizer (H : Set G))
    (hHZ : H ≤ Z) {g : G} (hg : g ∈ L) :
    H ≤ Z.map (MulAut.conj g).toMonoidHom := by
  have hfix := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  exact hfix ▸ map_mono hHZ

theorem neighbor_commutator_normalized_and_le_iInf {ι : Sort*}
    (L V A : Subgroup G) (Z : ι → Subgroup G) [IsMulCommutative V]
    (hAV : A ≤ V) (hZL : ∀ i, Z i ≤ L)
    (hZV : ∀ i, Z i ≤ normalizer (V : Set G))
    (hAZ : ∀ i, A ≤ normalizer (Z i : Set G))
    (hlocal : ∀ i, ⁅A, Z i⁆ ≠ ⊥ → ∃ T : Subgroup G,
      V ⊔ T = L ∧ T ≤ normalizer (Z i : Set G) ∧
      ⁅T, A⁆ ≤ centralizer (Z i : Set G))
    (htrans : ∀ i j, ∃ g ∈ L, (Z i).map (MulAut.conj g).toMonoidHom = Z j) :
    L ≤ normalizer ((⁅A, ⨆ i, Z i⁆ : Subgroup G) : Set G) ∧
      ⁅A, ⨆ i, Z i⁆ ≤ ⨅ i, Z i := by
  have hn (i : ι) : L ≤ normalizer ((⁅A, Z i⁆ : Subgroup G) : Set G) := by
    by_cases h : ⁅A, Z i⁆ = ⊥
    · rw [h]
      exact le_normalizer_of_normal
    obtain ⟨T, hgen, hTZ, hTA⟩ := hlocal i h
    exact commutator_normalized_of_abelian_join V A (Z i) T L
      hAV (hZV i) hTZ (hAZ i) hTA hgen
  have hbound (i : ι) : ⁅A, Z i⁆ ≤ ⨅ j, Z j := by
    apply le_iInf
    intro j
    obtain ⟨g, hg, he⟩ := htrans i j
    rw [← he]
    exact normal_subgroup_le_conjugate L _ _ (hn i)
      (le_normalizer_iff_commutator_le_right.mp (hAZ i)) hg
  rw [commutator_iSup_eq_iSup_of_normalized_seeds L A Z hZL hn]
  exact ⟨(le_iInf hn).trans (iInf_normalizer_le_normalizer_iSup _), iSup_le hbound⟩

/-- Adjoining a centralizing seed does not enlarge a relatively normal
commutator. This keeps the center vertex in the radius-one span. -/
theorem commutator_sup_eq_of_centralizing_seed
    (L A Z₀ V : Subgroup G)
    (hZ₀L : Z₀ ≤ L) (hVL : V ≤ L)
    (hZ₀A : Z₀ ≤ centralizer (A : Set G))
    (hn : L ≤ normalizer ((⁅A, V⁆ : Subgroup G) : Set G)) :
    ⁅A, Z₀ ⊔ V⁆ = ⁅A, V⁆ := by
  apply le_antisymm
  · rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal L Z₀ V A ⁅A, V⁆ hn hZ₀L hVL
    · rw [commutator_eq_bot_iff_le_centralizer.mpr hZ₀A]
      exact bot_le
    · exact (commutator_comm V A).le
  · exact commutator_mono le_rfl le_sup_right

/-- Algebraic normality and central-span step of DGS85 8.1(i), printed p.133.
The intended substitution is L = L_(α′), A = V_β ∩ Q_(α′), V = V_β,
Z₀ = Z_(α′), and Z i the centers at neighbors of α′. The conclusion is
relative normality in L_(α′), not in L_λ. The center-vertex seed is retained.
The graph application supplies local-generation, displacement and conjugacy
hypotheses using the actual radius-one span, including its center vertex. -/
theorem radius_one_commutator_normalized_and_central_in_core_spans {ι : Sort*}
    (L V A Z₀ : Subgroup G) (Z Q : ι → Subgroup G) [IsMulCommutative V]
    (hAV : A ≤ V) (hZL : ∀ i, Z i ≤ L)
    (hZV : ∀ i, Z i ≤ normalizer (V : Set G))
    (hAZ : ∀ i, A ≤ normalizer (Z i : Set G))
    (hlocal : ∀ i, ⁅A, Z i⁆ ≠ ⊥ → ∃ T : Subgroup G,
      V ⊔ T = L ∧ T ≤ normalizer (Z i : Set G) ∧
      ⁅T, A⁆ ≤ centralizer (Z i : Set G))
    (htrans : ∀ i j, ∃ g ∈ L, (Z i).map (MulAut.conj g).toMonoidHom = Z j)
    (hZ₀L : Z₀ ≤ L) (hZ₀A : Z₀ ≤ centralizer (A : Set G))
    (hZQ : ∀ i, Z i ≤ Q i) (hZCQ : ∀ i, Z i ≤ centralizer (Q i : Set G)) :
    L ≤ normalizer ((⁅A, Z₀ ⊔ ⨆ i, Z i⁆ : Subgroup G) : Set G) ∧
      ⁅A, Z₀ ⊔ ⨆ i, Z i⁆ ≤ ⨅ i, Z i ∧
      ∀ i, ⁅A, Z₀ ⊔ ⨆ j, Z j⁆ ≤ conjugateSpanBy (Q i) L ⊓
        centralizer (conjugateSpanBy (Q i) L : Set G) := by
  obtain ⟨hn, hbound⟩ := neighbor_commutator_normalized_and_le_iInf L V A Z
    hAV hZL hZV hAZ hlocal htrans
  rw [commutator_sup_eq_of_centralizing_seed L A Z₀ (⨆ i, Z i)
    hZ₀L (iSup_le hZL) hZ₀A hn]
  refine ⟨hn, hbound, fun i => ?_⟩
  have hseed : ⁅A, ⨆ j, Z j⁆ ≤ Z i := hbound.trans (iInf_le Z i)
  exact le_inf (hseed.trans ((hZQ i).trans (le_conjugateSpanBy (Q i) L)))
    (le_centralizer_conjugateSpanBy_of_normalizes _ (Q i) L hn
      (hseed.trans (hZCQ i)))

end Subgroup
