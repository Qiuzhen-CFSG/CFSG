module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import BenderSuzuki.SE.InvolutionsInTwoSubgroups
/-!
# The unitriangular obstruction to strong embedding

The two simple-root involutions in UT₃(F) do not commute. Its elementary root
plane supplies a four-group. The involution-commutation consequence of the
proved Bender–Suzuki theorem therefore excludes strongly embedded subgroups
in every finite group containing this literal unitriangular subgroup.

This is the strong-embedding generation route for the linear row of
Aschbacher–Smith F.4.45–49 and §5.3, using Bender–Suzuki Theorem SE.
It asserts no recognition or ambient generation by itself.
-/

public noncomputable section
open Subgroup Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearAmbientGeometry
variable {G : Type*} [Group G] [Finite G]
  (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- Noncommuting root involutions exclude strong embedding in the actual ambient group. -/
theorem not_stronglyEmbedded_of_unipotent
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2 ^ m)
    (S : Subgroup G) (e : U F ≃* S) (M : Subgroup G) :
    ¬ BenderSuzuki.IsStronglyEmbedded M := by
  intro hM
  let f := markedHom F S e
  have hf : Function.Injective f := markedHom_injective F S e
  obtain ⟨E,hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := V₁ F) 2
    (n := 2) (by rw [card_V₁,hF,← pow_mul]; exact Nat.pow_dvd_pow 2 (by omega))
  let j := f.comp (V₁ F).subtype
  have hj : Function.Injective j := hf.comp (V₁ F).subtype_injective
  have hr : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo G := by
    refine ⟨E.map j,?_,?_⟩
    · rw [card_map_of_injective hj,hE]
      rfl
    · rintro ⟨x,y,hy,rfl⟩
      apply Subtype.ext
      change j y ^ 2 = 1
      rw [← map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (V₁ F)) y,map_one]
  have hS : IsPGroup 2 S := (IsPGroup.of_card (G := U F) (n := m * 3)
    (by rw [card_U,hF,pow_mul])).of_equiv e
  let a : U F := ⟨1,0,0⟩
  let b : U F := ⟨0,1,0⟩
  have ha : a ^ 2 = 1 := (square_eq_one_iff F a).mpr (Or.inr rfl)
  have hb : b ^ 2 = 1 := (square_eq_one_iff F b).mpr (Or.inl rfl)
  have hc := hM.squares_commute_in_twoSubgroup hr S hS (f a) (f b)
    (e a).property (e b).property (by rw [← map_pow,ha,map_one]) (by rw [← map_pow,hb,map_one])
  have heq : a * b = b * a := hf (by simpa only [map_mul] using hc.eq)
  have h01 := congrArg U.c heq
  change (0 + 0 + (1:F) * 1) = 0 + 0 + 0 * 0 at h01
  simp at h01
end Matrix.PSL3.LinearAmbientGeometry
