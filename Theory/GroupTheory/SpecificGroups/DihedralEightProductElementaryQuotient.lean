module

public import Theory.GroupTheory.SpecificGroups.DihedralEightProductElementary

/-!
# The quotient by an elementary sixteen in D₈ × D₈

The two projections of an elementary sixteen each have order four and
index two. The subgroup is their full product, so it contains every
square. Consequently every homomorphic image killing that sixteen is
elementary abelian. This supplies the actual four-subgroup of the
normalizer quotient in Aschbacher--Smith F.5.4(4), printed p.301.
-/

public noncomputable section
open Subgroup
namespace DihedralGroup
local notation "D8" => DihedralGroup 4

theorem square_mem_elementary_sixteen (E : Subgroup (D8 × D8))
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 16) (x : D8 × D8) : x^2 ∈ E := by
  let A := E.map (MonoidHom.fst D8 D8)
  let B := E.map (MonoidHom.snd D8 D8)
  have hA := elementary_card_le_four A (hE.map _)
  have hB := elementary_card_le_four B (hE.map _)
  have hEAB : E ≤ A.prod B := fun a ha => ⟨⟨a,ha,rfl⟩,⟨a,ha,rfl⟩⟩
  have hprod : Nat.card (A.prod B) = Nat.card A * Nat.card B := by
    rw [Nat.card_congr (prodEquiv A B).toEquiv,Nat.card_prod]
  have hcard := card_le_of_le hEAB
  rw [hc,hprod] at hcard
  have hcA : Nat.card A = 4 := by nlinarith
  have hcB : Nat.card B = 4 := by nlinarith
  have hAi : A.index = 2 := by
    have hh := A.card_mul_index
    rw [hcA,nat_card] at hh
    omega
  have hBi : B.index = 2 := by
    have hh := B.card_mul_index
    rw [hcB,nat_card] at hh
    omega
  have heq : E = A.prod B := eq_of_le_of_card_ge hEAB (by rw [hprod,hcA,hcB,hc])
  rw [heq]
  exact ⟨A.sq_mem_of_index_two hAi x.1,B.sq_mem_of_index_two hBi x.2⟩

theorem elementary_image_of_sixteen_kernel {K : Type*} [Group K]
    (f : D8 × D8 →* K) (E : Subgroup (D8 × D8))
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 16) (hker : E ≤ f.ker) :
    IsElementaryAbelian 2 f.range := by
  have hp : ∀ a : f.range, a^2 = 1 := by
    rintro ⟨a,x,rfl⟩
    apply Subtype.ext
    change f x ^ 2 = 1
    rw [← map_pow]
    exact hker (square_mem_elementary_sixteen E hE hc x)
  exact { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

end DihedralGroup
