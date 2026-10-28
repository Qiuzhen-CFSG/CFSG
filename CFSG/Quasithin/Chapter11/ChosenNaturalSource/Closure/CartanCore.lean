module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.LocalClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Selection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.ResidualSelection

/-!
# Checked local closure applications in the chosen-natural endgame

The original chosen module and its actual flag give the point-normalizer
closure used in 11.5.7. The selection application also constructs a member
of H(L₁T,M) inside G₁, deriving its outside condition from 11.5.3(3) and
the preceding source geometry. The residual-compatible minimal H is also
constructed. The natural module sum, remaining Cartan action arguments and
exceptional elementary corank bound remain separate obligations.
Source: Aschbacher--Smith 11.5.4--5 and the opening of 11.5.7, pp.780--781.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The actual closure U=⟨V₃^G₁⟩ used at the start of 11.5.7. -/
theorem globalClosure_core_and_frattini (hp : E.point ≠ ⊥)
    (h13 : E.V₁ ≤ E.V₃) (hne : E.V₁ ≠ E.V₃)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃) :
    E.U ≤ E.G₁.pCoreIn 2 ∧
      E.tilde E.U ≤ (center ((E.tilde E.G₁).pCoreIn 2)).map
        ((E.tilde E.G₁).pCoreIn 2).subtype ∧
      (frattini E.U).map E.U.subtype ≤ E.V₁ ∧
      ⁅E.U, E.G₁.pCoreIn 2⁆ ≤ E.V₁ := by
  have hLH := sup_le E.L₁_le_G₁ hT1
  have h := E.localClosure_core_and_frattini hp h13 hne hT1 hlocal hirr E.G₁ le_rfl hLH
  exact ⟨h.1, E.localClosure_central_quotient hp h13 hne hT1 hlocal hirr E.G₁ le_rfl hLH,
    h.2.2.1, h.2.2.2.2⟩

/-- A selected H₁ with its core, central quotient and Frattini conclusions.
No local closure assertion is part of the input. -/
theorem exists_selected_localClosure (hp : E.point ≠ ⊥)
    (h13 : E.V₁ ≤ E.V₃) (hne : E.V₁ ≠ E.V₃)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hlocal : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hcontrol : centralizer (E.V₁ : Set G) ≤ E.M → E.G₁ ≤ E.M)
    (hKC : E.K ≤ centralizer (E.V₁ : Set G))
    (hescape : E.L₁ < E.K → ¬ E.K ≤ E.M)
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
        (E.M : Set G) ∧ H₁ ≤ E.G₁ ∧
      E.localClosure H₁ ≤ H₁.pCoreIn 2 ∧
      E.tilde (E.localClosure H₁) ≤ (center ((E.tilde H₁).pCoreIn 2)).map
        ((E.tilde H₁).pCoreIn 2).subtype ∧
      (frattini (E.localClosure H₁)).map (E.localClosure H₁).subtype ≤ E.V₁ := by
  obtain ⟨H₁, hH₁, hHG⟩ := E.exists_local_overgroup hp hT1
    (E.point_centralizer_not_le_M hp hTI hcontrol hKC hescape hnonabelian)
  have hLH : E.L₁ ⊔ (T : Subgroup G) ≤ H₁ := hH₁.1.2
  have h := E.localClosure_core_and_frattini hp h13 hne hT1 hlocal hirr H₁ hHG hLH
  exact ⟨H₁, hH₁, hHG, h.1,
    E.localClosure_central_quotient hp h13 hne hT1 hlocal hirr H₁ hHG hLH, h.2.2.1⟩

/-- The numeric and core consequences of 11.5.6 on the literal Cartan.
The rank and local quotient inputs are preceding marked flag geometry;
the strict-core input is precisely 11.4.1(3). -/
theorem cartan_numeric_and_core (hp : E.point ≠ ⊥)
    (hcart : LocalGeometry.IsCartan T L E.X) (hX : E.X ≤ E.G₁)
    (hr : ∀ p : ℕ, p.Prime → p ∣ 2 ^ E.input.field.degree - 1 → 2 ≤ primeRank p E.X)
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    (hstrict : E.L₁ < E.K → ⁅E.R₁, E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1) ∧
      primeRank 3 E.Y ≤ 1 ∧
      (Even E.input.field.degree → ¬ 3 ∣ Nat.card E.Y) ∧
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2, E.X⁆ ≤
        (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd hr hCX hz
  have hXL : E.X ≤ L := hcart.1.trans inf_le_left
  exact ⟨hc, E.three_rank_Y_le_one hp hc hexception hz hthree,
    E.three_not_dvd_Y_of_even hc,
    E.core_commutator_le ((hXL.trans le_sup_left).trans (L ⊔ (T : Subgroup G)).le_normalizer)
      hstrict⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
