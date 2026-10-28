module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# The involution-contained branch of Suzuki quotient fusion

The direct product T = PU has precisely the square-one elements in
M°U. If S has no additional involutions, conjugates of U whose images
lie in S/M° already lie in M°U, giving weak closure in the literal
quotient of M. The argument lifts conjugates of actual elements of U;
it requires no general involution-lifting assertion for a two-quotient.

Source: GLS4, Chapter 2, the first sentence of Lemma 14.9, using the
geometry of Lemmas 14.2–14.3; `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory
open scoped Pointwise

private theorem weaklyClosed_map_of_involutions {G : Type*} [Group G] [Finite G]
    (A S U : Subgroup G) [A.Normal] (hAS : A ≤ S) (hUS : U ≤ S)
    (hU : ∀ u ∈ U, u ^ 2 = 1)
    (hsquare : ∀ x ∈ S, x ^ 2 = 1 → x ∈ A ⊔ U) :
    External.WeaklyClosedIn (S.map (QuotientGroup.mk' A))
      (U.map (QuotientGroup.mk' A)) := by
  let pi := QuotientGroup.mk' A
  refine ⟨map_mono hUS, ?_⟩
  intro q hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective A q
  apply eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    have hmem : pi (a⁻¹ * v * a) ∈ S.map pi := by
      apply hq
      exact ⟨pi v, ⟨v, hv, rfl⟩, by simp [pi]⟩
    have hS : a⁻¹ * v * a ∈ S := by
      have he : (S.map pi).comap pi = S := comap_map_eq_self (by
        simpa only [pi, QuotientGroup.ker_mk'] using hAS)
      exact he ▸ hmem
    have hsq : (a⁻¹ * v * a) ^ 2 = 1 := by
      have hh : (MulAut.conj a⁻¹ v) ^ 2 = 1 := by
        rw [← map_pow, hU v hv, map_one]
      simpa only [MulAut.conj_apply, inv_inv] using hh
    have hm := mem_map_of_mem pi (hsquare _ hS hsq)
    have he : (A ⊔ U).map pi = U.map pi := by
      rw [Subgroup.map_sup, show A.map pi = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (by
        rw [QuotientGroup.ker_mk']), bot_sup_eq]
    rw [he] at hm
    simpa [pi, MulAut.conj_apply] using hm
  · exact le_of_eq (card_map_of_injective (MulAut.conj (pi a)⁻¹).injective).symm

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Every involution of T lies in the actual product M°U. -/
public theorem LocalGeometry.square_one_mem_closure_sup_U
    (g : LocalGeometry Z M z t m) {x : G} (hx : x ∈ g.T) (hsq : x ^ 2 = 1) :
    x ∈ closure (Z ∩ (M : Set G)) ⊔ g.U := by
  have hxprod : x ∈ (borelTwoCore M z t : Set G) * (g.U : Set G) := g.T_product ▸ hx
  obtain ⟨p, hp, u, hu, rfl⟩ := hxprod
  have hpL : p ∈ residualGenerated M z t := (g.P_eq ▸ hp).2
  have hc : Commute p u := mem_centralizer_iff.mp (g.U_le_centralizer hu) p hpL
  let := g.U_elementary
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  have hp2 : p ^ 2 = 1 := by
    rwa [hc.mul_pow, hu2, mul_one] at hsq
  have hpA : p ∈ closure (Z ∩ (M : Set G)) := by
    change p ∈ (closure (Z ∩ (M : Set G)) : Set G)
    rw [← g.P_involutions]
    exact ⟨hp, hp2⟩
  exact mul_mem_sup hpA hu

/-- The source identity Ω₁(T) = M°U, as ambient subgroups. -/
public theorem LocalGeometry.omega_T_eq (g : LocalGeometry Z M z t m) :
    omegaOneAmbient g.T = closure (Z ∩ (M : Set G)) ⊔ g.U := by
  apply le_antisymm
  · exact (omegaOneAmbient_le_iff _ _).mpr fun _ hx hs =>
      g.square_one_mem_closure_sup_U hx hs
  · apply sup_le
    · intro x hx
      have hp : x ∈ borelTwoCore M z t ∧ x ^ 2 = 1 := by
        change x ∈ {x : G | x ∈ borelTwoCore M z t ∧ x ^ 2 = 1}
        rw [g.P_involutions]
        exact hx
      apply (omegaOneAmbient_le_iff g.T _).mp le_rfl x
      · exact (g.P_eq ▸ hp.1).1
      · exact hp.2
    · let := g.U_elementary
      intro x hx
      exact (omegaOneAmbient_le_iff g.T _).mp le_rfl x (g.U_le_T hx)
        (elemPow_eq_one_of_isElementaryAbelian x hx)

/-- The first branch of Lemma 14.9, retaining M's actual quotient map. -/
public theorem quotientFusion_of_omega_le (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (hOmega : omegaOneAmbient g.S ≤ closure (Z ∩ (M : Set G)) ⊔ g.U) :
    QuotientFusion d g := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  have hUM : g.U ≤ M := g.U_le_S.trans g.S_le_M
  apply weaklyClosed_map_of_involutions (A.subgroupOf M) (g.S.subgroupOf M)
    (g.U.subgroupOf M) (subgroupOf_mono M g.closure_le_S) (subgroupOf_mono M g.U_le_S)
  · let := g.U_elementary
    intro u hu
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : G) hu)
  · intro x hx hsq
    have hmem := (omegaOneAmbient_le_iff _ _).mp hOmega (x : G) hx
      (congrArg Subtype.val hsq)
    change x ∈ (A.subgroupOf M) ⊔ (g.U.subgroupOf M)
    rw [← subgroupOf_sup distinguishedClosure_le hUM]
    exact hmem

/-- Failure of quotient weak closure forces the involution required in 14.7(b). -/
public theorem exists_involution_outside_T_of_not_quotientFusion
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hf : ¬ QuotientFusion d g) :
    ∃ a ∈ g.S, a ^ 2 = 1 ∧ a ∉ g.T := by
  by_contra hn
  apply hf
  apply quotientFusion_of_omega_le d g
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hs
  have hxT : x ∈ g.T := by
    by_contra hxT
    exact hn ⟨x, hx, hs, hxT⟩
  exact g.square_one_mem_closure_sup_U hxT hs

end BenderSuzuki.ZD.SuzukiExclusion
