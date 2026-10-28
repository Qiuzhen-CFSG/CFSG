module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.ComponentAction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.SylowAction

/-!
# Equivariant markings on the original component Sylow

Restrict the literal central quotient to the actual component Sylow, then
use the root-coordinate action obtained from that same projective Sylow.
The resulting marking has exactly the original central kernel and retains
pointwise conjugation compatibility. A cubic actor centralizing this Sylow
would lie in the three-prime action kernel, which is impossible.

Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/
public section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G]

theorem exists_equivariant_sylow_mark
    (K N : Subgroup G) (e : K ⧸ center K ≃* PSL) (P : Sylow 2 K)
    (hNK : N ≤ normalizer (K : Set G))
    (α : N →* MulAut PSL)
    (hcompat : ∀ n k, α n (e (QuotientGroup.mk' (center K) k)) =
      e (QuotientGroup.mk' (center K) (K.normalizerMonoidHom ⟨n, hNK n.property⟩ k)))
    (hP : ∀ n, ((P.mapSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))) : Subgroup PSL).map
        (α n).toMonoidHom = P.mapSurjective
          (f := e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
          (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    (hker : Nat.Coprime 3 (Nat.card α.ker)) :
    ∃ f : P →* Root, Function.Surjective f ∧ f.ker = (center K).subgroupOf P ∧
      ∃ β : N →* MulAut Root, Nat.Coprime 3 (Nat.card β.ker) ∧
        ∀ (n : N) (a b : P), ((b : K) : G) = n * ((a : K) : G) * (n : G)⁻¹ →
          β n (f a) = f b := by
  let q : K →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P₀ := P.mapSurjective (f := q) hq
  obtain ⟨eR, β, hβ, hβker⟩ := exists_root_action α P₀ hP hker
  let qP : P →* P₀ := {
    toFun a := ⟨q a, mem_map_of_mem q a.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' a b := Subtype.ext (map_mul q (a : K) (b : K)) }
  have hqP : Function.Surjective qP := by
    rintro ⟨u, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  let f := eR.symm.toMonoidHom.comp qP
  refine ⟨f, eR.symm.surjective.comp hqP, ?_, β, hβker, ?_⟩
  · ext a
    change eR.symm (qP a) = 1 ↔ (a : K) ∈ center K
    rw [← map_one eR.symm, eR.symm.injective.eq_iff]
    rw [Subtype.ext_iff]
    change q a = 1 ↔ (a : K) ∈ center K
    change e (QuotientGroup.mk' (center K) a) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  · intro n a b hab
    apply eR.injective
    apply Subtype.ext
    rw [hβ]
    change α n (eR (eR.symm (qP a))) = eR (eR.symm (qP b))
    simp only [eR.apply_symm_apply]
    change α n (e (QuotientGroup.mk' (center K) a)) =
      e (QuotientGroup.mk' (center K) b)
    rw [hcompat]
    congr 2
    exact Subtype.ext hab.symm

end Matrix.PSL3Four.RootNormalizerModel

namespace Subgroup
open Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem cubic_not_centralize_equivariant_sylow
    (K N : Subgroup G) (P : Sylow 2 K)
    (f : P →* Root) (hf : Function.Surjective f)
    (β : N →* MulAut Root) (hker : Nat.Coprime 3 (Nat.card β.ker))
    (hact : ∀ (n : N) (a b : P), ((b : K) : G) = n * ((a : K) : G) * (n : G)⁻¹ →
      β n (f a) = f b)
    (W : Subgroup G) (hW : Nat.card W = 3) (hWN : W ≤ N) :
    ¬ W ≤ centralizer ((P : Subgroup K).map K.subtype : Set G) := by
  intro hWC
  have hle : W.subgroupOf N ≤ β.ker := by
    intro n hn
    change β n = 1
    apply MulEquiv.ext
    intro u
    obtain ⟨a, rfl⟩ := hf u
    change β n (f a) = f a
    apply hact n a a
    have hc : ((a : K) : G) * n = n * ((a : K) : G) :=
      mem_centralizer_iff.mp (hWC hn) _ (mem_map_of_mem K.subtype a.property)
    calc
      ((a : K) : G) = ((a : K) : G) * n * (n : G)⁻¹ := by group
      _ = n * ((a : K) : G) * (n : G)⁻¹ := by rw [hc]
  have hdiv := card_dvd_of_le hle
  have hWcard : Nat.card (W.subgroupOf N) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv).trans hW
  rw [hWcard] at hdiv
  exact Nat.prime_three.coprime_iff_not_dvd.mp hker hdiv

end Subgroup
