module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairModule
/-!
# A common natural model for the original exchanged pair

The original Sylow supplies an element exchanging the two actual factors.
Transport the first quotient summand's natural coordinates through precisely
that element. The second factor consequently has the same chosen field and
natural model. Combining the complementary quotient summands gives the literal
product action, with both original factor inclusions explicitly identified.
No common-field, cross-action, exchange, or original-module splitting premise
is added to the source consumer.

Source: Aschbacher–Smith B.6.9 and E.2.3, pp.115–116 and216–217.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V D M : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Group D] [AddCommGroup M] [Module (ZMod 2) M]

structure SourceInduction.SourceTwoFactorCase.MarkedProduct
    {K : Type*} [Group K] {σ : Representation (ZMod 2) K V}
    (d : SourceTwoFactorCase σ) (τ : Representation (ZMod 2) D M) where
  action : ActionEquiv (fixed σ).quotientRepresentation
    (Representation.prod (τ.comp (MonoidHom.fst D D)) (τ.comp (MonoidHom.snd D D)))
  first_eq : ((⊤ : Subgroup D).prod (⊥ : Subgroup D)).map
    action.groupEquiv.symm.toMonoidHom = d.first
  second_eq : ((⊥ : Subgroup D).prod (⊤ : Subgroup D)).map
    action.groupEquiv.symm.toMonoidHom = d.second

noncomputable def sourceTwoFactorSharedModel
    (ρ : Representation (ZMod 2) G V) (Y : Subgroup G) [Y.Normal]
    (d : SourceTwoFactorCase (ρ.comp Y.subtype))
    (h₁ : d.firstSpace.toSubmodule = moved (ρ.comp Y.subtype) d.first)
    (h₂ : d.secondSpace.toSubmodule = moved (ρ.comp Y.subtype) d.second)
    (g : G) (hg : d.first.map (MulAut.conjNormal g).toMonoidHom = d.second)
    (τ : Representation (ZMod 2) D M)
    (e : ActionEquiv (((fixed (ρ.comp Y.subtype)).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) τ) :
    d.MarkedProduct τ := by
  let e₂ := sourceFactorConjugateModelEquiv ρ Y d.first d.second d.firstSpace d.secondSpace
    h₁ h₂ g hg τ e
  exact ⟨d.quotientModelEquiv τ τ e e₂,d.quotientModelEquiv_first τ τ e e₂,
    d.quotientModelEquiv_second τ τ e e₂⟩

variable [Finite G] [FiniteDimensional (ZMod 2) V]
theorem source_offender_two_factor_shared_natural
    (ρ : Representation (ZMod 2) G V)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hff : IsFFModule ρ) (hcore : pCore 2 G = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    letI := offenderSubgroup_normal ρ
    ∃ t : T,
      d.first.map (MulAut.conjNormal (t : G)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (t : G)).toMonoidHom = d.first ∧
      ((∃ F : BinaryField, Nonempty (d.MarkedProduct (linearNatural F 2))) ∨
        Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
  let := offenderSubgroup_normal ρ
  obtain ⟨h₁,h₂⟩ := source_offender_two_factor_rank_one ρ T hP hff hcore d
  obtain ⟨t,ht₁,ht₂⟩ := source_offender_two_factor_exists_sylow_exchange ρ T hP hff hcore d
  refine ⟨t,ht₁,ht₂,?_⟩
  rcases h₁.2 with hlin | hsym
  · obtain ⟨F,⟨e⟩⟩ := hlin
    exact Or.inl ⟨F,⟨sourceTwoFactorSharedModel ρ _ d h₁.1 h₂.1 t ht₁ _ e⟩⟩
  · obtain ⟨e⟩ := hsym
    exact Or.inr ⟨sourceTwoFactorSharedModel ρ _ d h₁.1 h₂.1 t ht₁ _ e⟩
end CFSG.Quasithin.ChapterB
