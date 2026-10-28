module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Exchange
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.FieldPower

/-!
# The local paired Hall/Cartan contradiction in the original source

Use the genuine 11.0.4 clauses to place Ω₁(Oₚ(A)) in L. The same original
Sylow element t moves its nontrivial factor in A ∩ K and fixes a nonidentity
diagonal. In compatible Cartan coordinates, its invertible triangular
semilinear operator induces one field power on all those p-points.
Faithfulness through the literal quotient L/O₂(L) gives the contradiction.

This completes the local calculation and its source application, not the
construction of the source configuration. The original Hall factors,
the square action of the chosen exchange element, and the compatible
SL₃/Sp₄ Cartan coordinates remain explicit inputs. The parameter-component
owner must construct them and recognize the actual seed at n(H) before
claiming 11.3.5 or producing RankOneReduction. The earlier residual and
cubic clauses retain their natural local-geometry producer; final source
assembly remains with the linear-geometry owner.

Source: Aschbacher--Smith, 11.0.4 and 11.3.5(2), printed pp.760,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G] [Finite G]

/-- The paired Hall/Cartan contradiction on the original chosen component.
The factor is literally A ∩ K, the quotient is L/O₂(L), and the same t in
the original Sylow supplies the exchange, fixed diagonal and field action.
The Hall factor construction and the marked semilinear operator remain
explicit geometric premises of this local step. -/
theorem source_paired_cartan_contradiction
    {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (A : Subgroup G) [IsMulCommutative A]
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hpB : p ∣ Nat.card (A ⊓ K : Subgroup G))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G))
    (hdisjoint : Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom))
    (hsq : (t : G) ^ 2 ∈ centralizer (primeTorsion (A ⊓ K) p : Set G))
    {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι S.field.Carrier) (hρ : Function.Injective ρ)
    (σ : S.field.Carrier ≃+* S.field.Carrier) (g : Matrix ι ι S.field.Carrier)
    (hg : g.IsUpperTriangular) (hdet : g.det ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d : ι → S.field.Carrier, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ primeTorsion A p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t (D.sylow_normalizes_component t.property)
          (QuotientGroup.mk' (pCore 2 L) x)) * g) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have hpow : 1 ≤ 2 ^ S.field.degree := Nat.one_le_pow _ _ (by decide)
    have h2 : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 (by have := S.field.degree_pos; omega)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega
  have hL := source_primeTorsion_le S A hA p hp hd halt hres hcubic
  obtain ⟨j,hj⟩ := primeTorsion_quotient_field_power_of_triangular A L p hL t htA
    (D.sylow_normalizes_component t.property) ρ hρ σ g hg hdet hdiag hint
  exact no_exchanged_primeTorsion_of_quotient_power A (A ⊓ K) L inf_le_left
    p (2 ^ j) hp2 hpB hL t htA hdisjoint hsq hj

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
