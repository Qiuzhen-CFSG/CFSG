module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Geometry
public import GorensteinWalter.PGammaL2OuterAbelian
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Restriction to the normal linear layers

The outer quotient of PSL₂ in the quadratic semilinear group has order four.
Thus every ambient Sylow two-subgroup supplements the inner layer. A proper
overgroup of that Sylow has proper intersection with each linear layer;
normality makes the literal Sylow intersection Sylow in the layer.

These maps are used by both torus branches. The actor is pulled back through
an injective homomorphism, so its four-group structure is preserved.
Source: Aschbacher–Smith A.2.3(2), E.1.2 and E.1.14(6), pp.33, 209–210, 214.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry

variable {K G : Type*} [Group K] [Group G]

/-- An actor contained in an injective image pulls back to the same four-group. -/
theorem kleinFour_comap (f : K →* G) (hf : Function.Injective f)
    (A : Subgroup G) (hA : IsKleinFour A) (hAf : A ≤ f.range) :
    IsKleinFour (A.comap f) := by
  let e := ((A.comap f).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hAf))
  exact ⟨(Nat.card_congr e.toEquiv).trans hA.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans hA.exponent_two⟩

/-- A Sylow subgroup pulls back to a Sylow subgroup of a normal embedded layer. -/
theorem sylow_comap_normal [Finite G] (f : K →* G) (hf : Function.Injective f)
    [f.range.Normal] (T : Sylow 2 G) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K) = (T : Subgroup G).comap f := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal f.range
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  let Q := S.comapOfInjective e.toMonoidHom e.injective
    (fun x _ => ⟨e.symm x, e.apply_symm_apply x⟩)
  refine ⟨Q, ?_⟩
  ext x
  change e x ∈ (S : Subgroup f.range) ↔ f x ∈ (T : Subgroup G)
  rw [hS]
  rfl

/-- A proper Sylow overgroup has proper intersection with a supplemented layer. -/
theorem comap_ne_top_of_supplement (f : K →* G) (T M : Subgroup G)
    (hsupp : T ⊔ f.range = ⊤) (hTM : T ≤ M) (hM : M ≠ ⊤) :
    M.comap f ≠ ⊤ := by
  intro h
  apply hM
  apply top_unique
  rw [← hsupp]
  apply sup_le hTM
  rintro _ ⟨x, rfl⟩
  exact (show x ∈ M.comap f from h ▸ mem_top x)

variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- Every Sylow two-subgroup supplements the actual PSL₂ layer in square degree. -/
theorem sylow_sup_psl {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (T : Sylow 2 (PGammaL2 F)) :
    (T : Subgroup _) ⊔ pGammaL2PSLRange F = ⊤ := by
  let : Fact (IsOddPrimePower (Nat.card F)) := ⟨⟨p, 2, hp, ho, by decide, hF⟩⟩
  let f := pGammaL2OuterProduct F
  have hc : Nat.card (PGammaL2 F ⧸ f.ker) = 4 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (pGammaL2OuterProduct_surjective F)).toEquiv, Nat.card_prod]
    rw [FiniteField.card_ringAut_of_card_prime_pow hp hF]
    have hlinear : Nat.card (PGL2 F ⧸
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) = 2 :=
      pgl2_psl2Range_index_eq_two F Fact.out
    rw [hlinear]
  have htwo : IsPGroup 2 (PGammaL2 F ⧸ f.ker) :=
    IsPGroup.of_card (n := 2) (by simpa using hc)
  simpa only [f, pGammaL2OuterProduct_ker] using T.sup_eq_top_of_quotient_isPGroup f.ker htwo

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry
