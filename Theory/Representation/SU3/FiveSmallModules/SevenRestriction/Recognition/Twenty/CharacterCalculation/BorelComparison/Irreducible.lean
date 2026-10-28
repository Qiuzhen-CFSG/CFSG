module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.RootGeometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity.SplitMultiplicity

/-!
# Irreducibility of root-center-free degree-twenty Borel restrictions

For an extraspecial root of order 125 with its central generator fused to
its square, every nonzero module without root-center invariants has dimension
at least twenty. Every submodule inherits the vanishing of those invariants,
so a module of dimension exactly twenty is irreducible.

The final theorem applies this argument to the literal Borel, using its
actual torus conjugator and the canonical root inclusion. It requires neither
whole-group irreducibility nor a splitting field, and discharges the Schur
lemma hypotheses in `BorelComparison`.

Source: the extraspecial degree calculation underlying Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3; Aschbacher–Smith K.2,
printed p.453. The Borel comparison is a local proof route, not a quoted
character-table identity.
-/

public section

open Subgroup
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Degrees.RootEigenline.NonlinearMultiplicity

private theorem subrepresentation_invariants_eq_bot
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (Z : Subgroup G)
    (hfix : invariants (ρ.comp Z.subtype) = ⊥) (S : Subrepresentation ρ) :
    invariants (S.toRepresentation.comp Z.subtype) = ⊥ := by
  apply bot_unique
  intro v hv
  apply Subtype.ext
  have hmem : (v : V) ∈ invariants (ρ.comp Z.subtype) := by
    intro z
    exact congrArg Subtype.val (hv z)
  rw [hfix] at hmem
  exact hmem

/-- Fusion of a nontrivial extraspecial five-center makes twenty the least
possible positive dimension of a root-center-free module. -/
theorem finrank_ge_twenty_of_root_center_free
    {K G V : Type*} [Field K] [CharP K 2] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K G V) (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3) (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (g : G) (hg : g * (z : G) * g⁻¹ = (z : G) ^ 2)
    (hfix : invariants (ρ.comp ((center P).map P.subtype).subtype) = ⊥) :
    20 ≤ Module.finrank K V := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hne : ρ (z : G) ≠ 1 := by
    intro he
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvfix : v ∈ invariants (ρ.comp ((center P).map P.subtype).subtype) := by
      rintro ⟨x, hx⟩
      obtain ⟨w, hw, rfl⟩ := hx
      have hall := (Representation.mem_invariants_iff_of_forall_mem_zpowers
        ((ρ.comp P.subtype).comp (center P).subtype)
        (⟨z, hz⟩ : center P)
        (fun _ => mem_zpowers_of_prime_card (IsExtraspecial.center_order_p 5 P)
          (by exact fun h => hz1 (congrArg Subtype.val h))) v).mpr
        (show ρ (z : G) v = v by rw [he]; rfl)
      exact hall ⟨w, hw⟩
    rw [hfix] at hvfix
    exact hv hvfix
  obtain ⟨a, ha, hd⟩ := multiplicity ρ P hc z hz hz1 hne g hg
  rw [hfix, finrank_bot] at hd
  omega

/-- Minimal dimension forces irreducibility on the group containing the
specified fusion actor, without any ambient irreducibility assumption. -/
theorem irreducible_of_root_center_free_twenty
    {K G V : Type*} [Field K] [CharP K 2] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3) (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (g : G) (hg : g * (z : G) * g⁻¹ = (z : G) ^ 2)
    (hdim : Module.finrank K V = 20)
    (hfix : invariants (ρ.comp ((center P).map P.subtype).subtype) = ⊥) :
    IsIrreducible ρ := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro S
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hSne : S.toSubmodule ≠ ⊥ := by
    intro h
    exact hS (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hSne
  have hge := finrank_ge_twenty_of_root_center_free S.toRepresentation P hc z hz hz1 g hg
    (subrepresentation_invariants_eq_bot ρ _ hfix S)
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.eq_top_of_finrank_eq
  have hle := Submodule.finrank_le S.toSubmodule
  omega

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Subgroup BenderSuzuki.MatrixGroups
open Degrees Degrees.RootEigenline
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- Every root-center-free degree-twenty representation is already
irreducible upon restriction to the actual Borel. -/
theorem borel_restriction_isIrreducible [Finite F]
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K V : Type*} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (standardGroup J) V)
    (hdim : Module.finrank K V = 20)
    (hfix : invariants (ρ.comp (standardRootCenter J).subtype) = ⊥) :
    IsIrreducible (ρ.comp (standardBorel J).subtype) := by
  obtain ⟨hp, hcard⟩ := borelRoot_structure J hc hconj
  let : IsExtraspecial 5 (borelRoot J) := hp
  obtain ⟨z, hz, hz1, hfusion⟩ := borelRoot_central_fusion J hc hconj
  obtain ⟨k, hk⟩ := hfusion 2 (by decide) (by decide)
  exact irreducible_of_root_center_free_twenty (ρ.comp (standardBorel J).subtype)
    (borelRoot J) hcard z hz hz1 (Degrees.principalTorusIn J k) hk hdim
    (borelRootCenter_invariants_eq_bot J ρ hfix)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
