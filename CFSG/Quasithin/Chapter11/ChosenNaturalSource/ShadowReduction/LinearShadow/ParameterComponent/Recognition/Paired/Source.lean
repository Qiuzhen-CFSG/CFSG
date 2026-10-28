module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Hall
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Paired

/-!
# Apply the Cartan contradiction to the constructed source component

The source seed and oddness now discharge the disjoint-factor premise of
the paired torsion calculation. The original Sylow element and the literal
quotient L/O₂(L) are retained in the semilinear intertwining identity.
The remaining Hall-order, square-action and coordinate premises are explicit;
this is not yet the unconditional normality conclusion of 11.3.5(2).
Source: Aschbacher--Smith, printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

namespace Paired
open Matrix
/-- Apply the original Cartan calculation to the actual seed. Disjointness
of the two odd factors is proved from the source component geometry. -/
theorem source_paired_cartan_contradiction_of_seed
    {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (seed : ComponentSeed T H K)
    (A : Subgroup G) [IsMulCommutative A]
    (hA : A ≤ H ⊓ normalizer (L : Set G)) (hodd : Odd (Nat.card A))
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
    (htK : (t : G) ∉ normalizer (K : Set G))
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
  exact source_paired_cartan_contradiction S A hA p hp hd hpB halt hres hcubic t htA
    (seed.paired_odd_factors_disjoint h pr hc hs A hodd t
      (h.outside.1.1.2 t.property) htK) hsq ρ hρ σ g hg hdet hdiag hint
end Paired

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
