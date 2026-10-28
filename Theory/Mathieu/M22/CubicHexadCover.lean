module
public import Theory.Mathieu.M22.CubicHexad
public import Theory.Mathieu.M22.CubicHexadCover.Rank
public import Theory.Mathieu.M22.CubicHexadCover.LocalLift
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The invariant cubic rank obstruction for M₂₂ covers

The invariant cubic pair in M₂₂ lifts through an odd central kernel of order
dividing three. Its join maps onto the perfect hexad group. Taking a perfect
section upstairs gives three-rank at least two, inside every subgroup that
contains all Sylow-invariant cubic overgroups. This is the model input to
original Aschbacher--Smith 14.3.6(6), printed p.994.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.CubicHexadCover
variable {E : Type} [Group E] [Finite E]

theorem invariant_cubic_rank
    (f : E →* M22) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker ∣ 3)
    (hcompat : ∀ a : MulAut E, ∃ b : MulAut M22, ∀ x, b (f x) = f (a x))
    (P : Sylow 2 E) (N : Subgroup E)
    (hN : ∀ L : Subgroup E, (P : Subgroup E) ≤ L → (P : Subgroup E).relIndex L = 3 →
      (∀ a : MulAut E, (P : Subgroup E).map a.toMonoidHom = P → L.map a.toMonoidHom = L) → L ≤ N) :
    ∃ D : Subgroup E, D ≤ N ∧ Group.IsPerfect D ∧ 2 ≤ primeRank 3 D := by
  let Pq := P.mapSurjective hf
  obtain ⟨J₁,J₂,hP₁,hP₂,hi₁,hi₂,hinv,⟨e₁⟩,⟨e₂⟩,hperfect,j,hj⟩ :=
    M22CubicHexad.exists_invariant_cubic_hexad_pair Pq
  have ho : Odd (Nat.card f.ker) := (by decide : Odd 3).of_dvd_nat hk
  obtain ⟨L₁,hPL₁,hm₁,hil₁,hinv₁⟩ := exists_invariant_cubic_lift f hf hc ho P J₁ hP₁ hi₁ e₁
  obtain ⟨L₂,hPL₂,hm₂,hil₂,hinv₂⟩ := exists_invariant_cubic_lift f hf hc ho P J₂ hP₂ hi₂ e₂
  have hLP (a : MulAut E) (ha : (P : Subgroup E).map a.toMonoidHom = P) :
      L₁.map a.toMonoidHom = L₁ ∧ L₂.map a.toMonoidHom = L₂ := by
    obtain ⟨b,he⟩ := hcompat a
    have hbP : (Pq : Subgroup M22).map b.toMonoidHom = Pq := by
      change ((P : Subgroup E).map f).map b.toMonoidHom = (P : Subgroup E).map f
      rw [map_map,show b.toMonoidHom.comp f = f.comp a.toMonoidHom from MonoidHom.ext he,
        ←map_map,ha]
    obtain ⟨hb₁,hb₂⟩ := hinv b hbP
    exact ⟨hinv₁ a b he hb₁,hinv₂ a b he hb₂⟩
  have hLN : L₁ ⊔ L₂ ≤ N := sup_le (hN L₁ hPL₁ hil₁ (fun a ha => (hLP a ha).1))
    (hN L₂ hPL₂ hil₂ (fun a ha => (hLP a ha).2))
  let := hperfect
  obtain ⟨D,hD,hperf,hrank⟩ := perfect_rank_two_in_preimage f hc hk (L₁ ⊔ L₂) (J₁ ⊔ J₂)
    (by rw [Subgroup.map_sup,hm₁,hm₂]) j hj
  exact ⟨D,hD.trans hLN,hperf,hrank⟩

theorem central_quotient_invariant_cubic_rank
    (e : (E ⧸ center E) ≃* M22) (hk : Nat.card (center E) ∣ 3)
    (P : Sylow 2 E) (N : Subgroup E)
    (hN : ∀ L : Subgroup E, (P : Subgroup E) ≤ L → (P : Subgroup E).relIndex L = 3 →
      (∀ a : MulAut E, (P : Subgroup E).map a.toMonoidHom = P → L.map a.toMonoidHom = L) → L ≤ N) :
    ∃ D : Subgroup E, D ≤ N ∧ Group.IsPerfect D ∧ 2 ≤ primeRank 3 D := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center E := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ center E
    rw [e.map_eq_one_iff,QuotientGroup.eq_one_iff]
  apply invariant_cubic_rank f hf (hker ▸ le_rfl) (hker.symm ▸ hk) ?_ P N hN
  intro a
  let b := (MulAut.congr e) ((center E).quotientAut a)
  refine ⟨b,?_⟩
  intro x
  dsimp only [b,f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
  simp only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,quotientAut_apply_mk]

end Sporadic.Mathieu.CubicHexadCover
