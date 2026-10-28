module
public import Theory.GroupTheory.SylowNormalCoprimeSupplement

/-!
# Normal prime subgroups inside a coprime normal supplement

If a normal subgroup N of a finite group has order prime to p and
N ⊔ H is the whole group, every normal p-subgroup P lies in H. No
solvability or group-action hypothesis is needed.

Choose a Sylow p-subgroup S of H. The normal coprime supplement theorem
makes its ambient image Sylow in N ⊔ H, and the full-join hypothesis
transports this to a Sylow subgroup of G. Normality places P in that
Sylow subgroup, which is already contained in H.

This standard Sylow consequence is used in the q′-core normalizer
supplements of Kurzweil–Stellmacher, *The Theory of Finite Groups*, §11.2.
It is kept in Theory because all inputs are general finite-group results.
-/

/-- A normal p-subgroup lies in any subgroup supplemented by a normal p′-subgroup. -/
public theorem normal_pSubgroup_le_of_coprime_normal_supplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N H P : Subgroup G) [N.Normal] [P.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hsup : N ⊔ H = ⊤) (hP : IsPGroup p P) : P ≤ H := by
  classical
  let S : Sylow p H := Classical.choice inferInstance
  have hNnot : ¬ p ∣ Nat.card N := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hN
  obtain ⟨T, hT⟩ := S.exists_map_eq_map_of_normal_coprime_sup N H hNnot
  have hsurj : Function.Surjective (N ⊔ H : Subgroup G).subtype := by
    intro x
    exact ⟨⟨x, by rw [hsup]; trivial⟩, rfl⟩
  let T₀ : Sylow p G := T.mapSurjective (f := (N ⊔ H : Subgroup G).subtype) hsurj
  have hT₀ : (T₀ : Subgroup G) = (S : Subgroup H).map H.subtype := hT
  have hPT := hP.le_sylow_of_normal T₀
  rw [hT₀] at hPT
  exact hPT.trans (Subgroup.map_subtype_le _)
