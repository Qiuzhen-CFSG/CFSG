module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorFour
public import Theory.GroupTheory.ComponentCardNormal

/-!
# Normality of the actual four-dimensional A₅ component

The original faithful symplectic action embeds the terminal group in
Sp₄(2) = S₆, of order 720. Two distinct conjugates of an A₅ component
would generate a direct product of order 3600. Thus that same component
is normal, and the existing local-lift theorem identifies the original
K with its T-conjugate span. No containment of T in K is inferred.

Source: Aschbacher–Smith G.11.2(2) and 14.3.14–15, pp.364 and 994.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- Normality concerns the same dotted A₅ component in the original
four-dimensional action, without a catalogue or orbit-marking premise. -/
theorem terminal_a5_component_normal_of_four
    (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (D : Subgroup F.TerminalHdot) (hD : IsComponent F.TerminalHdot D)
    (e5 : D ≃* alternatingGroup (Fin 5)) : D.Normal := by
  obtain ⟨_,j,hj,_⟩ := Representation.exists_binarySymplecticFour_embedding
    F.terminalRepresentation hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  let a := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  have hbound := Nat.card_le_card_of_injective (a.toMonoidHom.comp j)
    (a.injective.comp hj)
  have hS : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hDcard : Nat.card D = 60 := by
    rw [Nat.card_congr e5.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hz : center D = ⊥ := by
    apply le_bot_iff.mp
    intro d hd
    have he : e5 d = 1 :=
      (alternatingGroup.center_eq_bot (by simp)).le ((centerCongr e5) ⟨d,hd⟩).property
    exact e5.map_eq_one_iff.mp he
  apply hD.normal_of_card_lt_sq hz
  rw [hDcard]
  rw [hS] at hbound
  omega

/-- The actual local lift in degree four is its literal T-conjugate span. -/
theorem ComponentLift.eq_conjugateSpanBy_of_a5_of_four
    {F : InvariantFlag T V 2}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5)) :
    K = conjugateSpanBy K (T : Subgroup G) :=
  hK.eq_conjugateSpanBy_of_image_normal
    (terminal_a5_component_normal_of_four F hyp hd _ hK.image_component e5)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
