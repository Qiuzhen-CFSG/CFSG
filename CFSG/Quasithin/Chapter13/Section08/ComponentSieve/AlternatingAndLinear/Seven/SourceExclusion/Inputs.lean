module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.CriticalReciprocity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsExclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry

/-!
# Earlier inputs to the conditional A₇ exclusion

All groups, sections and actions are literal. The component is normal only
inside H; the action is conjugation on U_H/V₁ through H/O₂(H). The critical
pair retains its endpoint conjugator. The first alternative allows a
nonidentity transvection in Vβ* or Vγ*: this includes the corrected actors
Uβ, Vβ and Uγ by subgroup containment, without identifying their vertices.

`Earlier` records only preceding source facts. Its local fields are the
13.7.3 theta/seed facts, 13.7.5 residual calculations and 13.8.13,16,21
component conclusions. Its geometric fields are F.9.13 and 13.8.4,5,8,18.
The reciprocal inputs are conditional on the strict case of 13.8.8 and
contain no rank-one or transvection conclusion. The final field is exactly
the used strict pointwise-centralizer implication of 13.8.23(4), universally
over the actual maximal subrepresentations.

The explicit universal appendix inputs retain all 4,6,4+dual models with
compatible actions, strong-FF exclusion and transvection recognition; their
Clifford/extension consequences are part of those earlier inputs. The
13.7.6(3) implication retains both alternating degrees and actual quotients.
The conditional exclusion does not certify those earlier book theorems.

No partition placement, S₇ surjectivity, natural quotient, nontrivial action
on W, rank-one actor, reciprocal transvection or partition contradiction is
a field. `SourceExclusion` derives all of them where they are used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959/PDF pp.975–976, with the preceding clauses
cited above (combined manuscript, 1 March 2004).
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
open CriticalGeometry PairsBranch PairsBranch.ModuleSelection
open FourThreeBranch.NaturalSelection
universe u
variable {G : Type u} [Group G] [Finite G]
  {L T H V : Subgroup G} (c : CriticalPair L T H V)
  (K L₁ L₀ X G₁ M V₃ V₁ : Subgroup G)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [IsElementaryAbelian 2 (Source.VH H V)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))

/-- The precise preceding local, geometric and appendix facts consumed by
13.8.24. All consequences specific to the A₇ exclusion are proved later. -/
structure Earlier : Prop where
  -- Local group setup and 13.8.13,16,21.
  member : H ∈ Source.Hz L₁ T G₁ M
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  component_normal : (K.subgroupOf H).Normal
  supplement : K ⊔ T = H
  local_le_component : L₁ ≤ K
  base_solvable : Group.IsSolvable (L₁ ⊔ T : Subgroup G)
  sylow : ∃ S : Sylow 2 H, (S : Subgroup H) = T.subgroupOf H
  two_group : IsPGroup 2 T
  theta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  solvable_overgroups : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
    Group.IsSolvable J → J ≤ M
  -- Source flag, 13.8.5 and the actual endpoint geometry.
  flag : V₃ ≤ V
  line_le : V₁ ≤ Source.UH H V₃
  source_action : CentralAction.IsSourceAction H V₃ V₁ ρ
  transvection_models : ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim ρ (zpowers a) = 1 →
    LocalGeometry.TransvectionModels ρ L
  covered_nine : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
    Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* Multiplicative (Fin 2 → ZMod 3))
  edge : (L ⊔ T) ⊓ H = L₁ ⊔ T
  terminal_core : Source.VH H V ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2
  Vgamma_le : c.Vgamma ≤ H
  Vgamma_placement : ∃ y : H,
    c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2
  alternatives :
    (∃ a ∈ Source.starImage H (CriticalReciprocity.Vbeta c),
      a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∨
    (∃ a ∈ Source.starImage H c.Vgamma, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∨
    LocalGeometry.SecondCase H L₁ T (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma
      (c.Aone V₁) V₁ ρ
  reciprocal_inputs :
    LocalGeometry.SecondCase H L₁ T (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma
      (c.Aone V₁) V₁ ρ → CriticalReciprocity.Earlier c L₁ K V₃ V₁
  Vgamma_quadratic : IsQuadratic ρ (Source.starImage H c.Vgamma)
  -- Earlier A₆/covered-A₆ local calculations, retaining O² residuals.
  local_models : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
  six_local_card : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
    Nat.card (L₁ ⧸ pCore 2 L₁) = 3
  covered_local_rank : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    primeRank 3 L₁ = 2
  covered_residuals : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    Nonempty (LocalResidualData L₁ L₀ X T)
  -- 13.8.21 and the generating seed recalled before 13.8.22.
  generated : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆
  monolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
    Source.starImage H K ≤ N
  seed_nontrivial : V₃ ≠ ⊥
  seed_commutator : ⁅V₃, L₁⁆ = V₃
  seed_normalized : L₁ ⊔ T ≤ normalizer (V₃ : Set G)
  seed_irreducible : IsIrreducible
    (sourceSeed H V₃ V₁ ρ source_action L₁ (le_sup_left.trans seed_normalized)).toRepresentation
  seed_rank : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2
  seed_centralized : L₀ ≤ centralizer (V₃ : Set G)
  -- Universal appendix/13.7.6 implications and the used clause of 13.8.23.
  small_modules : ∀ (φ : Source.Hstar H →* S7) (hi : Function.Injective φ)
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7)),
    SmallQuadraticInput.{u, u} φ (componentInclusion φ hi (Source.starImage H K) hK)
  alternating_natural : CentralAction.AlternatingNaturalImplication L L₁ T G₁ M ρ
  no_strong : SevenPointNoStrongInput.{u}
  recognition : SevenPointRecognitionInput.{u}
  strict_centralizer : ∀ W : Subrepresentation ρ, IsCoatom W →
    rank (Source.starImage H (c.Ugamma V₃)) = 1 →
    (∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w) →
    Source.starImage H (c.Ugamma V₃) < subspaceKernel W.toRepresentation
      (fixedSpace W.toRepresentation (Source.starImage H (c.Ugamma V₃))) ⊤ ∨
    Source.starImage H (c.Ugamma V₃) < subspaceKernel W.quotientRepresentation
      (fixedSpace W.quotientRepresentation (Source.starImage H (c.Ugamma V₃))) ⊤

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.SourceExclusion
