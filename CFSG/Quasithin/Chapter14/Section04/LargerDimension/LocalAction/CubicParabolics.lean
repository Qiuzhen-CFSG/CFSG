module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.SourceFlags

/-!
# Maximality of the actual cubic parabolics

For a source cubic residual X normalized by the ambient Sylow subgroup T,
[XT:T] = 3. Passing to a vertex's actual two-core quotient preserves the
Sylow index. That index is 21 for PSL₃(2) and 9 for S₃ × S₃, so XT has
prime index 7 or 3 in the vertex. This proves maximality of the marked
subgroups without assuming their images are standard model parabolics.
The existing quotient correspondence then gives the complete rank-two
parabolic records, including the exhaustive clause and intersection T.

Source: Aschbacher--Smith, 14.4.8(2) and 14.4.13, printed pp.1009,1012.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction

variable {G D : Type*} [Group G] [Group D] [Finite G]

private theorem core_sylow_index (e : (G ⧸ pCore 2 G) ≃* D)
    (S : Sylow 2 G) {n : ℕ} (hD : ∀ P : Sylow 2 D, (P : Subgroup D).index = n) :
    (S : Subgroup G).index = n := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ (S : Subgroup G) := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  exact ((S : Subgroup G).index_map_eq hf hk).symm.trans (hD (S.mapSurjective hf))

private theorem linear_sylow_index (e : (G ⧸ pCore 2 G) ≃* Matrix.PSL3Two.PSL)
    (S : Sylow 2 G) : (S : Subgroup G).index = 21 := by
  apply core_sylow_index e S
  intro P
  have h := (P : Subgroup Matrix.PSL3Two.PSL).card_mul_index
  rw [Matrix.PSL3Two.card_sylow_two P, Matrix.PSL3Two.card_PSL] at h
  omega

private theorem product_sylow_index
    (e : (G ⧸ pCore 2 G) ≃* SymmetricThreeProduct.G)
    (S : Sylow 2 G) : (S : Subgroup G).index = 9 := by
  apply core_sylow_index e S
  intro P
  have hc : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, SymmetricThreeProduct.card_group]
    decide +kernel
  have h := (P : Subgroup SymmetricThreeProduct.G).card_mul_index
  rw [hc, SymmetricThreeProduct.card_group] at h
  omega

omit [Finite G] in
private theorem coatom_of_prime_index (P : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hi : P.index = p) : IsCoatom P := by
  constructor
  · intro he
    have : p = 1 := by simpa only [he, index_top] using hi.symm
    exact hp.ne_one this
  · intro Q hQ
    have hd : Q.index ∣ p := hi ▸ index_dvd_of_le hQ.le
    rcases (Nat.dvd_prime hp).mp hd with hh | hh
    · exact index_eq_one.mp hh
    · have hm := relIndex_mul_index hQ.le
      rw [hi, hh] at hm
      have he : P.relIndex Q = 1 := by nlinarith [hp.pos]
      exact False.elim (hQ.not_ge (relIndex_eq_one.mp he))

private theorem marked_index {H X J : Subgroup G} (T : Sylow 2 G)
    (hX : ThreeExtension H T X) (hXJ : X ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    {n : ℕ} (hi : ((T : Subgroup G).subgroupOf J).index = 3 * n) :
    ((X ⊔ (T : Subgroup G)).subgroupOf J).index = n := by
  have hm := relIndex_mul_relIndex (T : Subgroup G) (X ⊔ (T : Subgroup G)) J
    le_sup_right (sup_le hXJ hTJ)
  change ((T : Subgroup G).subgroupOf (X ⊔ (T : Subgroup G))).index *
    ((X ⊔ (T : Subgroup G)).subgroupOf J).index =
    ((T : Subgroup G).subgroupOf J).index at hm
  rw [source_index_three T X hX, hi] at hm
  omega

/-- Every source cubic residual marks a maximal parabolic in a linear vertex. -/
theorem linear_marked_coatom {H X J : Subgroup G} (T : Sylow 2 G)
    (hX : ThreeExtension H T X) (hXJ : X ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (e : coreQuotient J ≃* Matrix.PSL3Two.PSL) :
    IsCoatom ((X ⊔ (T : Subgroup G)).subgroupOf J) := by
  apply coatom_of_prime_index _ (by decide : Nat.Prime 7)
  exact marked_index T hX hXJ hTJ (linear_sylow_index e (T.subtype hTJ))


/-- Every source cubic residual marks a maximal parabolic in a product vertex. -/
theorem product_marked_coatom {H X J : Subgroup G} (T : Sylow 2 G)
    (hX : ThreeExtension H T X) (hXJ : X ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (e : coreQuotient J ≃* SymmetricThreeProduct.G) :
    IsCoatom ((X ⊔ (T : Subgroup G)).subgroupOf J) := by
  apply coatom_of_prime_index _ (by decide : Nat.Prime 3)
  exact marked_index T hX hXJ hTJ (product_sylow_index e (T.subtype hTJ))

/-- The two literal parabolics of a linear vertex, with all maximality,
intersection and exhaustiveness clauses. The residuals generate the vertex
after adjoining T. -/
theorem linear_cubic_parabolics {H K A B J : Subgroup G} (T : Sylow 2 G)
    (hA : ThreeExtension H T A) (hB : ThreeExtension K T B)
    (hAJ : A ≤ J) (hBJ : B ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (hgen : (A ⊔ (T : Subgroup G)) ⊔ (B ⊔ (T : Subgroup G)) = J)
    (e : coreQuotient J ≃* Matrix.PSL3Two.PSL) :
    Quasithin.I5.RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      ((A ⊔ (T : Subgroup G)).subgroupOf J)
      ((B ⊔ (T : Subgroup G)).subgroupOf J) := by
  exact linear_vertex_parabolics T J _ _ (sup_le hAJ hTJ) (sup_le hBJ hTJ)
    le_sup_right le_sup_right hgen e
    (linear_marked_coatom T hA hAJ hTJ e) (linear_marked_coatom T hB hBJ hTJ e)

/-- The corresponding complete pair in the S₃ × S₃ vertex. -/
theorem product_cubic_parabolics {H K A B J : Subgroup G} (T : Sylow 2 G)
    (hA : ThreeExtension H T A) (hB : ThreeExtension K T B)
    (hAJ : A ≤ J) (hBJ : B ≤ J) (hTJ : (T : Subgroup G) ≤ J)
    (hgen : (A ⊔ (T : Subgroup G)) ⊔ (B ⊔ (T : Subgroup G)) = J)
    (e : coreQuotient J ≃* SymmetricThreeProduct.G) :
    Quasithin.I5.RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      ((A ⊔ (T : Subgroup G)).subgroupOf J)
      ((B ⊔ (T : Subgroup G)).subgroupOf J) := by
  exact product_vertex_parabolics T J _ _ (sup_le hAJ hTJ) (sup_le hBJ hTJ)
    le_sup_right le_sup_right hgen e
    (product_marked_coatom T hA hAJ hTJ e) (product_marked_coatom T hB hBJ hTJ e)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
