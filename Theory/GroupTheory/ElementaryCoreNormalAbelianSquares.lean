module

public import FeitThompson.PCore.Nilpotent
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Elementary two-core actors on normal abelian subgroups

The two-part of a normal nilpotent subgroup lies in the Sylow, and its
odd part centralizes the two-core. The resulting normalization puts each
commutator with an elementary actor in that actor, forcing it to fix all
squares in every normal abelian subgroup.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup
namespace Theory.GroupTheory
 theorem normal_nilpotent_le_normalizer_of_core_and_sylow_normal
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (V R : Subgroup G) [R.Normal] [Group.IsNilpotent R]
    (hV : V ≤ pCore 2 G) (hVN : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    R ≤ normalizer (V : Set G) := by
  let P := (pCore 2 R).map R.subtype
  let U := (pPrimeCore 2 R).map R.subtype
  have hP : P ≤ (T : Subgroup G) :=
    ((pCore_isPGroup (p := 2) (G := R)).map R.subtype).le_sylow_of_normal T
  have hUc : Nat.Coprime 2 (Nat.card U) := by
    rw [card_map_of_injective R.subtype_injective]
    exact pPrimeCore_coprime_card
  have hdisj : Disjoint (pCore 2 G) U := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hUc.pow_left n
  have hU : U ≤ centralizer (V : Set G) := by
    intro u hu v hv
    exact (commute_of_normal_of_disjoint (pCore 2 G) U inferInstance inferInstance
      hdisj v u (hV hv) hu).eq
  have hs : R ≤ P ⊔ U := by
    have hh := map_mono (f := R.subtype)
      (nilpotent_top_le_pCore_sup_pPrimeCore (p := 2) (inferInstance : Group.IsNilpotent R))
    simpa only [← MonoidHom.range_eq_map, range_subtype, Subgroup.map_sup] using hh
  exact hs.trans (sup_le (hP.trans hVN) (hU.trans (centralizer_le_normalizer (V : Set G))))

/-- An elementary normal Sylow subgroup in the two-core fixes squares in every normal abelian subgroup. -/
theorem elementary_core_commute_normal_abelian_squares
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (V R : Subgroup G) [R.Normal] [IsMulCommutative R]
    (hV : V ≤ pCore 2 G) (hVN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hpow : ∀ v ∈ V, v ^ 2 = 1) :
    ∀ v ∈ V, ∀ r ∈ R, Commute v (r ^ 2) := by
  let : CommGroup R := IsMulCommutative.instCommGroup
  have hn := normal_nilpotent_le_normalizer_of_core_and_sylow_normal T V R hV hVN
  intro v hv r hr
  have hcV : v * r * v⁻¹ * r⁻¹ ∈ V := by
    have hh := (hn hr v⁻¹).mp (V.inv_mem hv)
    simpa only [mul_assoc] using V.mul_mem hv hh
  have hc := hpow _ hcV
  have hr' : v * r * v⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem r hr v
  have hcomm : Commute (v * r * v⁻¹) r := by
    exact congrArg R.subtype ((IsMulCommutative.is_comm (M := R)).comm (⟨_, hr'⟩ : R) ⟨r, hr⟩)
  rw [hcomm.inv_right.mul_pow, inv_pow, mul_inv_eq_one] at hc
  apply (mul_inv_eq_iff_eq_mul).mp
  calc
    v * r ^ 2 * v⁻¹ = (v * r * v⁻¹) ^ 2 := (map_pow (MulAut.conj v) r 2)
    _ = r ^ 2 := hc
end Theory.GroupTheory
