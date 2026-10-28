module

public import CFSG.Quasithin.Chapter12.Section08.Setup

/-!
# Sylow placement in the final hyperplane argument

The source 12.9.9(2) applies to hyperplanes of conjugates of V contained
in T. The final proof conjugates one of them by an element of H, which
need not normalize T. If the resulting hyperplane normalizes V, Sylow
conjugacy inside N_G(V) returns it to T. This conjugation preserves both
V and M=N_G(L), so the original relative intersection and its centralizer
are transported together. V is not assumed normal in all of M.

Source: Aschbacher--Smith, 12.9.9(2) and the final paragraph of the proof
of 12.9.1, printed pp.862--864.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

private theorem exists_sylow_conjugator (T : Sylow 2 G) (N D : Subgroup G)
    (hTN : (T : Subgroup G) ≤ N) (hDN : D ≤ N) (htwo : IsPGroup 2 D) :
    ∃ k : N, D.map (MulAut.conj (k : G)).toMonoidHom ≤ (T : Subgroup G) := by
  have ht : IsPGroup 2 (D.subgroupOf N) :=
    htwo.comap_of_injective N.subtype N.subtype_injective
  obtain ⟨S, hDS⟩ := ht.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq N S (T.subtype hTN)
  refine ⟨k, ?_⟩
  rintro x ⟨d, hd, rfl⟩
  have hdS : (⟨d, hDN hd⟩ : N) ∈ (S : Subgroup N) := hDS hd
  have hm : k * (⟨d, hDN hd⟩ : N) * k⁻¹ ∈ (T.subtype hTN : Subgroup N) := by
    rw [← hk]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom hdS
  exact hm

/-- The original 12.9.9(2) statement only requires hyperplanes inside T. -/
def SylowHyperplaneControl (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  ∀ g : G, (conjugate V g ⊓ normalizer (L : Set G)) ≤ (T : Subgroup G) →
    (conjugate V g ⊓ normalizer (L : Set G)).relIndex (conjugate V g) = 2 →
    (conjugate V g ⊓ normalizer (L : Set G)) ⊓ centralizer (V : Set G) = ⊥

/-- Move the literal hyperplane into T inside N_G(V). This justifies the
last use of 12.9.9(2) after the source conjugation by h ∈ H; h need not
normalize T. No normality of V in all of M is assumed. -/
theorem hyperplane_control_of_normalizes
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (hyperplanes : SylowHyperplaneControl T L V) (g : G)
    (hDN : conjugate V g ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G))
    (hindex : (conjugate V g ⊓ normalizer (L : Set G)).relIndex (conjugate V g) = 2) :
    (conjugate V g ⊓ normalizer (L : Set G)) ⊓ centralizer (V : Set G) = ⊥ := by
  let := h.chosen.elementary
  let A := conjugate V g
  let M := normalizer (L : Set G)
  let D := A ⊓ M
  have ht : IsPGroup 2 D :=
    ((IsElementaryAbelian.isPGroup 2 V).map (MulAut.conj g⁻¹).toMonoidHom).to_le inf_le_left
  obtain ⟨k, hk⟩ := exists_sylow_conjugator T (normalizer (V : Set G)) D
    (h.sylow_normalizes_seed earlier.structural) hDN ht
  let f := MulAut.conj (k : G)
  have hv : V.map f.toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp k.property
  have hm : M.map f.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp
    (M.le_normalizer (h.seed_normalizer_le earlier.structural earlier.uniqueness k.property))
  have ha : A.map f.toMonoidHom = conjugate V (g * (k : G)⁻¹) := by
    unfold A conjugate
    rw [map_map]
    congr 1
    ext x
    simp [f, mul_assoc]
  have hd : D.map f.toMonoidHom = conjugate V (g * (k : G)⁻¹) ⊓ M := by
    change (A ⊓ M).map f.toMonoidHom = _
    rw [map_inf _ _ _ f.injective, ha, hm]
  have ht' : conjugate V (g * (k : G)⁻¹) ⊓ M ≤ (T : Subgroup G) := by
    rw [← hd]
    exact hk
  have hi' : (conjugate V (g * (k : G)⁻¹) ⊓ M).relIndex
      (conjugate V (g * (k : G)⁻¹)) = 2 := by
    rw [← hd, ← ha, relIndex_map_map_of_injective _ _ f.injective]
    exact hindex
  have he := hyperplanes (g * (k : G)⁻¹) ht' hi'
  have hcent : (centralizer (V : Set G)).map f.toMonoidHom ≤ centralizer (V : Set G) := by
    have hc := map_centralizer_le_centralizer_image (V : Set G) f.toMonoidHom
    change _ ≤ centralizer ((V.map f.toMonoidHom : Subgroup G) : Set G) at hc
    rwa [hv] at hc
  apply le_bot_iff.mp
  intro x hx
  have hdx : f x ∈ conjugate V (g * (k : G)⁻¹) ⊓ M :=
    hd ▸ mem_map_of_mem f.toMonoidHom hx.1
  have hcx : f x ∈ centralizer (V : Set G) :=
    hcent (mem_map_of_mem f.toMonoidHom hx.2)
  have hx1 : f x = 1 := mem_bot.mp (he ▸ show f x ∈
      (conjugate V (g * (k : G)⁻¹) ⊓ M) ⊓ centralizer (V : Set G) from ⟨hdx, hcx⟩)
  exact mem_bot.mpr (f.injective (hx1.trans f.map_one.symm))

end CFSG.Quasithin.Chapter12.Section09
