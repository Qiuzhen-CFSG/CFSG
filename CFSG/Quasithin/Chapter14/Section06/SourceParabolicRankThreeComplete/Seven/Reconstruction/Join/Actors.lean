module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Extension
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer

/-!
# Exhaustion of the faithful seven-letter actor

The natural six-space normalizer embeds in S7; a prescribed full S7 actor
therefore exhausts it. On a binary four-space the actual normal A7 image
is self-normalizing. Both statements retain the faithful ambient action.
Source: Aschbacher–Smith, C.1.23 and original14.6.10(5), pp.130 and1029.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
variable {A V : Type*} [Group A] [Finite A] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- The full natural S7 actor fills any faithful extension in which A7 is normal. -/
theorem natural_actor_surjective (ρ : Representation (ZMod 2) A V)
    (hρ : Function.Injective ρ) (f : Equiv.Perm (Fin 7) →* A)
    (hf : Function.Injective f) [(alternatingGroup (Fin 7) |>.map f).Normal]
    (E : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7))
    (he : ∀ s v, E (ρ (f s) v) = BinaryPermutation.naturalRepresentation (Fin 7) s (E v)) :
    Function.Surjective f := by
  let N := (alternatingGroup (Fin 7)).map f
  let eN : N ≃* alternatingGroup (Fin 7) :=
    ((alternatingGroup (Fin 7)).equivMapOfInjective f hf).symm
  let c := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let E' := E.trans c.symm
  have hc (s : Equiv.Perm (Fin 7)) (v : BinaryPermutation.natural (Fin 7)) :
      c.symm (BinaryPermutation.naturalRepresentation (Fin 7) s v) =
        BinaryPermutation.coreRepresentation (Fin 7) s (c.symm v) := by
    apply c.injective
    rw [c.apply_symm_apply, BinaryPermutation.coreEquivNatural_equivariant, c.apply_symm_apply]
  obtain ⟨g,hg,_,_⟩ := BinaryPermutation.SevenParabolic.faithful_extension N ρ hρ eN E' (by
    intro n v
    obtain ⟨k,rfl⟩ := eN.symm.surjective n
    rw [eN.apply_symm_apply]
    change c.symm (E (ρ (f k.val) v)) =
      BinaryPermutation.coreRepresentation (Fin 7) k.val (c.symm (E v))
    rw [he,hc])
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_le_card
  calc
    Nat.card A ≤ Nat.card (Equiv.Perm (Fin 7)) := Nat.card_le_card_of_injective g hg
    _ = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv

/-- A faithful four-space admits no proper normal extension of its A7 actor. -/
theorem exceptional_actor_surjective (ρ : Representation (ZMod 2) A V)
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (f : alternatingGroup (Fin 7) →* A) (hf : Function.Injective f) [f.range.Normal] :
    Function.Surjective f := by
  apply MonoidHom.range_eq_top.mp
  exact BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top
    ρ hρ hd f.range (MonoidHom.ofInjective hf).symm

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
