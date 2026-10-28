module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugate subgroups through a distinguished subgroup

If `N_G(V)` controls fusion of `U` into `V`, then `N_G(U)` is transitive
on the conjugates of `V` containing `U`. If in addition `N_G(U) ≤ N_G(V)`,
there is just one such conjugate. This uniqueness propagates to subgroups
of `V` whose normalizer orbit contains a subgroup containing `U`.

The proof corrects a conjugator on the right by an element of `N_G(V)`.
This is the subgroup version of the element transporter argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, A.1.7(1), applied in 6.2.5(4),(6), printed p. 681.
The local fusion and module-orbit calculations in 6.2.5 remain separate inputs.
We use left conjugation, the inverse of the source's right-conjugation convention.
-/

namespace Subgroup

variable {G : Type*} [Group G]

private theorem map_conj_mul (V : Subgroup G) (g n : G) :
    V.map (MulAut.conj (g * n)).toMonoidHom =
      (V.map (MulAut.conj n).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev, mul_assoc]

private theorem map_conj_inverse (V : Subgroup G) (g : G) :
    (V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = V := by
  rw [← map_conj_mul]
  rw [mul_inv_cancel, map_one]
  exact map_id V

/-- Fusion of `U` into `V` can be turned around to control conjugates of `V`
containing `U`. -/
public theorem exists_normalizer_conjugator_of_subgroup_fusion
    (U V : Subgroup G)
    (hfusion : ∀ g : G, U.map (MulAut.conj g).toMonoidHom ≤ V →
      ∃ n ∈ normalizer (V : Set G),
        U.map (MulAut.conj n).toMonoidHom = U.map (MulAut.conj g).toMonoidHom)
    (g : G) (hg : U ≤ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ normalizer (U : Set G),
      V.map (MulAut.conj c).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  have hpre : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ V := by
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    have hi : (V.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = V := by
      simpa only [inv_inv] using map_conj_inverse V g⁻¹
    rwa [hi] at h
  obtain ⟨n, hn, he⟩ := hfusion g⁻¹ hpre
  refine ⟨g * n, mem_normalizer_iff_map_conj_eq.mpr ?_, ?_⟩
  · change U.map (MulAut.conj (g * n)).toMonoidHom = U
    rw [map_conj_mul, he, map_conj_inverse]
  · have hnV : V.map (MulAut.conj n).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hn
    rw [map_conj_mul, hnV]

/-- Normalizer control plus fusion gives the unique conjugate through `U`. -/
public theorem conjugate_eq_of_subgroup_fusion
    (U V : Subgroup G)
    (hfusion : ∀ g : G, U.map (MulAut.conj g).toMonoidHom ≤ V →
      ∃ n ∈ normalizer (V : Set G),
        U.map (MulAut.conj n).toMonoidHom = U.map (MulAut.conj g).toMonoidHom)
    (hN : normalizer (U : Set G) ≤ normalizer (V : Set G))
    (g : G) (hg : U ≤ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  obtain ⟨c, hc, he⟩ := exists_normalizer_conjugator_of_subgroup_fusion U V hfusion g hg
  rw [← he]
  exact mem_normalizer_iff_map_conj_eq.mp (hN hc)

/-- Uniqueness through `U` propagates to any subgroup having a normalizer
conjugate containing `U`, for example a hyperplane in a transitive orbit. -/
public theorem conjugate_eq_of_unique_incidence
    (U V W : Subgroup G)
    (hunique : ∀ g : G, U ≤ V.map (MulAut.conj g).toMonoidHom →
      V.map (MulAut.conj g).toMonoidHom = V)
    (horbit : ∃ n ∈ normalizer (V : Set G), U ≤ W.map (MulAut.conj n).toMonoidHom)
    (g : G) (hg : W ≤ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  obtain ⟨n, hn, hUW⟩ := horbit
  have h := hunique (n * g) (by
    rw [map_conj_mul]
    exact hUW.trans (map_mono hg))
  apply map_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective
  rw [← map_conj_mul, h]
  exact (mem_normalizer_iff_map_conj_eq.mp hn).symm

/-- A subgroup with a unique containing conjugate controls its normalizer. -/
public theorem normalizer_le_of_unique_incidence
    (V W : Subgroup G) (hWV : W ≤ V)
    (hunique : ∀ g : G, W ≤ V.map (MulAut.conj g).toMonoidHom →
      V.map (MulAut.conj g).toMonoidHom = V) :
    normalizer (W : Set G) ≤ normalizer (V : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hunique
  have hfix : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rw [← hfix]
  exact map_mono hWV

end Subgroup
