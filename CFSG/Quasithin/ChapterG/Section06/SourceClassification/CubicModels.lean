module

public import Theory.SpecificGroups.BinaryLinear.SylowCubic
public import Theory.SpecificGroups.SymmetricCubicSylow
public import CFSG.Quasithin.ChapterG.Section06.Source

/-!
# The normalized-cubic sieve on actual transvection models

Transport the original Sylow subgroup and cubic generator through the given
actor coordinates. In a natural binary linear model, transport of the
original displacement operator forces dimension two. In a symmetric model
of degree five through eight, the actual cubic normalizer forces degree
seven and a single three-cycle. These are model calculations, not a proof
that an arbitrary source action has such a model.

Source: Aschbacher–Smith, C.5.12, printed p.163, using G.6.4, pp.345–346.
The earlier B.5.6 classification dependency is retained in FFExtraction.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section06
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

theorem binary_model_degree_of_normalized_cubic
    (ρ : Representation (ZMod 2) G V) (S : Sylow 2 G) (c a : G)
    (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    (ha : a ^ 2 = 1) (hi : a * c = c ^ 2 * a)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    {n : ℕ} (e : G ≃* BinaryLinear.GL (Fin n → ZMod 2))
    (E : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (hE : ∀ g v, E (ρ g v) = e g (E v)) : n = 2 := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn' : (P : Subgroup (BinaryLinear.GL (Fin n → ZMod 2))) ≤
      normalizer (zpowers (e c) : Set (BinaryLinear.GL (Fin n → ZMod 2))) := by
    change (S : Subgroup G).map e.toMonoidHom ≤ _
    have heq : (zpowers c).map e.toMonoidHom = zpowers (e c) := by
      simpa only [MulEquiv.coe_toMonoidHom] using MonoidHom.map_zpowers e.toMonoidHom c
    rw [← heq, ← map_equiv_normalizer_eq]
    exact map_mono hn
  have hrange : (LinearMap.range (ρ a - LinearMap.id)).map E.toLinearMap =
      LinearMap.range ((e a).toLinearMap - LinearMap.id) := by
    ext w
    constructor
    · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
      refine ⟨E u, ?_⟩
      change e a (E u) - E u = E (ρ a u - u)
      rw [map_sub, hE]
    · rintro ⟨u, rfl⟩
      obtain ⟨v, rfl⟩ := E.surjective u
      refine ⟨ρ a v - v, ⟨v, rfl⟩, ?_⟩
      change E (ρ a v - v) = e a (E v) - E v
      rw [map_sub, hE]
  have ht' : Module.finrank (ZMod 2)
      (LinearMap.range ((e a).toLinearMap - LinearMap.id)) = 1 := by
    rw [← hrange, E.finrank_map_eq]
    exact ht
  have hdim := BinaryLinear.finrank_eq_two_of_normalized_cubic_inverted_transvection
    P (e c) (e a) (by rw [← map_pow, hc, map_one])
    (fun h => hcne (e.injective (h.trans e.map_one.symm))) hn'
    (by rw [← map_pow, ha, map_one])
    (by simpa only [map_mul, map_pow] using congrArg e hi) ht'
  simpa using hdim

theorem symmetric_model_degree_of_normalized_cubic
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    {n : ℕ} (hnlo : 5 ≤ n) (hnhi : n ≤ 8) (e : G ≃* Equiv.Perm (Fin n)) :
    n = 7 ∧ (e c).cycleType = {3} := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn' : (P : Subgroup (Equiv.Perm (Fin n))) ≤
      normalizer (zpowers (e c) : Set (Equiv.Perm (Fin n))) := by
    change (S : Subgroup G).map e.toMonoidHom ≤ _
    have heq : (zpowers c).map e.toMonoidHom = zpowers (e c) := by
      simpa only [MulEquiv.coe_toMonoidHom] using MonoidHom.map_zpowers e.toMonoidHom c
    rw [← heq, ← map_equiv_normalizer_eq]
    exact map_mono hn
  exact Equiv.Perm.degree_seven_of_sylow_normalizes_cubic hnlo hnhi P (e c)
    (by rw [← map_pow, hc, map_one])
    (fun h => hcne (e.injective (h.trans e.map_one.symm))) hn'
end CFSG.Quasithin.ChapterG.Section06
