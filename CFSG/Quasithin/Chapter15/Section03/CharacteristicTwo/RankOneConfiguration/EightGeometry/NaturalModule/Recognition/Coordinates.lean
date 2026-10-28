module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FaithfulAction
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Realizing recognized coordinates on the ambient subgroup

An equivariant linear equivalence for the already constructed star action
induces the required multiplicative equivalence on the original subgroup U_L.
The actor is exactly the supplied marking composed with the original star map.
This conversion is only the final representation-to-subgroup step; constructing
the linear equivalence from the FF alternatives remains a separate obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(1), printed p.1132.
-/

@[expose] public section


open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition
variable {G : Type*} [Group G] [Finite G]
variable (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (hchar : HasCharacteristicTwo I)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  [IsElementaryAbelian 2 ((d.componentModule I c.L).subgroupOf I)]

noncomputable def actionOfCoordinates
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (f : Additive ((d.componentModule I c.L).subgroupOf I) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8))
    (hf : ∀ g v, f (componentAction d c hn hI hchar P hP g v) =
      BinaryPermutation.naturalRepresentation (Fin 8) (e g) (f v)) :
    NaturalEightAction I (d.componentModule I c.L) := by
  have hWI : d.componentModule I c.L ≤ I :=
    (componentModule_le_span d c).trans (span_le d (hP ▸ map_subtype_le _))
  let k := (subgroupOfEquivOfLe hWI).symm
  refine {
    normalizes := componentModule_normalizes d c hn
    coordinates := k.trans (AddEquiv.toMultiplicativeRight f.toAddEquiv)
    actor := e.toMonoidHom.comp (d.starMap I)
    onto := e.surjective.comp (QuotientGroup.mk'_surjective _)
    compatible := ?_ }
  intro i u
  change Multiplicative.ofAdd (f (Additive.ofMul (k
      ((d.componentModule I c.L).normalizerMonoidHom
        ⟨i, componentModule_normalizes d c hn i.property⟩ u)))) = _
  have heq : Additive.ofMul (k
      ((d.componentModule I c.L).normalizerMonoidHom
        ⟨i, componentModule_normalizes d c hn i.property⟩ u)) =
      componentAction d c hn hI hchar P hP (d.starMap I i) (Additive.ofMul (k u)) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (componentAction_apply d c hn hI hchar P hP i (Additive.ofMul (k u))).symm
  rw [heq, hf]
  rfl

theorem actionOfCoordinates_actor
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (f : Additive ((d.componentModule I c.L).subgroupOf I) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8))
    (hf : ∀ g v, f (componentAction d c hn hI hchar P hP g v) =
      BinaryPermutation.naturalRepresentation (Fin 8) (e g) (f v)) :
    (actionOfCoordinates d c hn hI hchar P hP e f hf).actor =
      e.toMonoidHom.comp (d.starMap I) := rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition

end
