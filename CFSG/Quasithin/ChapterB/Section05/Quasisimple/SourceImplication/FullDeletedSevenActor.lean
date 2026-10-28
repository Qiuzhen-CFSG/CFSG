module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension

/-!
# The full actor of a marked deleted seven-space

A faithful normal extension of the actual A7 deleted action embeds in S7
with its component marking and module coordinates preserved. If the actor
already has at least the order of S7, this embedding is an isomorphism.
The marked offender subgroup in the B.5.1 seven-letter row supplies precisely
that order bound. Source: Aschbacher–Smith 10.2.9 and C.1.24(a), printed
pp.751–753 and 130–131.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
open BinaryPermutation
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]

theorem full_deleted_seven_actor
    (ρ : Representation (ZMod 2) Q V) (hρ : Function.Injective ρ)
    (A : Subgroup Q) [A.Normal]
    (a : ActionEquiv (ρ.comp A.subtype) (alternatingNaturalRepresentation (Fin 7)))
    (hcard : Nat.card (Equiv.Perm (Fin 7)) ≤ Nat.card Q) :
    ∃ b : ActionEquiv ρ (naturalRepresentation (Fin 7)),
      ∀ x : A, b.groupEquiv x = (a.groupEquiv x).val := by
  let c := coreEquivNatural (Fin 7) (by decide)
  let eV := a.linearEquiv.trans c.symm
  have he : ∀ x : A, ∀ v, eV (ρ x v) =
      alternatingCoreRepresentation (Fin 7) (a.groupEquiv x) (eV v) := by
    intro x v
    apply c.injective
    change c (c.symm (a.linearEquiv (ρ x v))) =
      c (coreRepresentation (Fin 7) (a.groupEquiv x).val (eV v))
    rw [c.apply_symm_apply, coreEquivNatural_equivariant]
    change a.linearEquiv (ρ x v) =
      naturalRepresentation (Fin 7) (a.groupEquiv x).val (c (c.symm (a.linearEquiv v)))
    rw [c.apply_symm_apply]
    exact a.intertwines x v
  obtain ⟨f,hf,hfA,hact⟩ := SevenParabolic.faithful_extension A ρ hρ a.groupEquiv eV he
  let e := MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hcard)
  refine ⟨⟨e,a.linearEquiv,?_⟩,hfA⟩
  intro g v
  have h := congrArg c (hact g v)
  change c (c.symm (a.linearEquiv (ρ g v))) =
    c (coreRepresentation (Fin 7) (f g) (c.symm (a.linearEquiv v))) at h
  rwa [c.apply_symm_apply, coreEquivNatural_equivariant,c.apply_symm_apply] at h
end CFSG.Quasithin.ChapterB.QuasisimpleSource
