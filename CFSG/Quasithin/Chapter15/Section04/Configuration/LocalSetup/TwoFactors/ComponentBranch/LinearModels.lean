module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.PrimeFields
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Nine

/-!
# Concrete PSL₂ actions in the component branch of 15.4.18

For the actual PSL₂ carrier, a faithful elementary four-group fixing a Sylow
two-subgroup pointwise, with characteristic-two fixed subgroups for each
nonidentity actor, forces the field size to be nine among the source parameters.
It gives actual A₆ and S₆ identifications, preserving the embedded component
and every automorphism's action.

The exact numeric restrictions in `Setup` reduce to prime and square fields.
`PrimeFields` excludes the prime cases using the projective automorphism
centralizer and involution fixed groups. `SquareFields` finds a coefficient
involution and identifies its fixed subgroup with PGL₂ over the prime field;
the two-core condition forces that prime to be three. Finally `Nine` supplies
the compatible exceptional isomorphism and symmetric extension.

This is the intrinsic model calculation. Application of every full F.6.18
alternative, including the actual field extension in case (8), and transport
through I/O_{3'}(I) belong to the parent component branch. `SourceFieldSize`
records only the numerical restrictions, not an extension identification.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.18,
printed pp.309–310, and 15.4.18, printed pp.1162–1163.
-/

public section

open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels

/-- The intrinsic fixed-action hypotheses eliminate every source PSL₂ field
size except nine. The fixed-group premise refers to the self-centralizing
two-core of each actual automorphism fixed subgroup. -/
theorem card_eq_nine_of_sourceFieldSize
    {F A : Type*} [Field F] [Finite F] [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hsize : SourceFieldSize (Nat.card F)) (P : Sylow 2 PSL(2,F))
    (ρ : A →* MulAut PSL(2,F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup PSL(2,F)) → ρ a x = x)
    (hc : CharacteristicTwoFixed ρ) : Nat.card F = 9 := by
  rcases sourceFieldSize_prime_or_square hsize with ⟨hp, hm⟩ | ⟨p, hp, hF, hm⟩
  · exact (primeField_fixed_action_false F hp rfl hm P hA ρ hρ hfix hc).elim
  · have hp3 := prime_eq_three_of_square_field hp hF (by rwa [← hF]) P ρ hρ hA hfix hc
    simpa [hp3] using hF

/-- The source parameter restrictions and intrinsic fixed-action hypotheses
give compatible identifications of the component with A₆ and its generated
inner extension with S₆, without assuming field size nine or a fixed-group
descent identification. -/
theorem exists_symmetric_extension_of_sourceFieldSize
    {F A : Type*} [Field F] [Finite F] [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (hsize : SourceFieldSize (Nat.card F)) (P : Sylow 2 PSL(2,F))
    (ρ : A →* MulAut PSL(2,F)) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 4)
    (hfix : ∀ a x, x ∈ (P : Subgroup PSL(2,F)) → ρ a x = x)
    (hc : CharacteristicTwoFixed ρ) :
    ∃ (e : PSL(2,F) ≃* alternatingGroup (Fin 6))
      (Φ : MulAut.innerExtension ρ ≃* Equiv.Perm (Fin 6)),
      (∀ x : PSL(2,F), Φ ⟨MulAut.conj x, MulAut.conj_mem_innerExtension ρ x⟩ =
        (e x : Equiv.Perm (Fin 6))) ∧
      ∀ (g : MulAut.innerExtension ρ) (x : PSL(2,F)),
        (e (g.val x) : Equiv.Perm (Fin 6)) =
          Φ g * (e x : Equiv.Perm (Fin 6)) * (Φ g)⁻¹ :=
  exists_symmetric_extension_of_card_nine
    (card_eq_nine_of_sourceFieldSize hsize P ρ hρ hA hfix hc) P ρ hρ hA hfix

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels
