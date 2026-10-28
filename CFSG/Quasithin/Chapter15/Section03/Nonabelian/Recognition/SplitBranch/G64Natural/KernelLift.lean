module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural.Images
public import Theory.GroupTheory.SemisimpleCentralizerImage

/-!
# Kernel transport for the split constituent images

The normal subgroup K retains its given nonabelian simple-power isomorphism
inside the literal extension K⟨v⟩. The semisimple centralizer image theorem
therefore lifts centralizing elements through each actual constituent action,
even when that action has a nontrivial kernel on K.

The subgroup equivalence for restriction to K⟨v⟩ preserves the order of the
original K-centralizer. Thus its prime-to-three order passes to the centralizer
in the constituent image of K. The original order bound remains an explicit
input, supplied by the source displacement-plane stabilizer in the parent
argument. No recognized model or faithfulness premise is used here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, first split-constituent paragraph in the proof of
15.3.58, printed p.1149.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
universe u w
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {S : Type w} [Group S] [IsSimpleGroup S] {n : ℕ}
  {ρ : Representation (ZMod 2) A E} {K : Subgroup A} [K.Normal] {v : A}

/-- Centralizing elements in the literal constituent image lift to centralizing
original elements of K, without assuming faithfulness on K. -/
theorem constituent_centralizer_image
    (hna : ¬ IsMulCommutative S) (e : K ≃* (Fin n → S))
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule) :
    ((K ⊓ centralizer ({v} : Set A)).subgroupOf (extensionActor K v)).map
        (actionHom (constituentAction J hv)) =
      (K.subgroupOf (extensionActor K v)).map (actionHom (constituentAction J hv)) ⊓
        centralizer ({actionHom (constituentAction J hv) (extensionMark K v)} :
          Set (actionImage (constituentAction J hv))) := by
  have hcent : (K ⊓ centralizer ({v} : Set A)).subgroupOf (extensionActor K v) =
      K.subgroupOf (extensionActor K v) ⊓
        centralizer ({extensionMark K v} : Set (extensionActor K v)) := by
    ext x
    simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff,
      Subtype.ext_iff, Subgroup.coe_mul]
    rfl
  rw [hcent]
  exact Theory.GroupTheory.SemisimpleCentralizer.map_inf_centralizer hna _
    ((subgroupOfEquivOfLe (le_sup_left : K ≤ extensionActor K v)).trans e)
    (actionHom (constituentAction J hv)) (extensionMark K v)

/-- The original prime-to-three centralizer bound passes to the K-image of
each literal constituent action. -/
theorem constituent_centralizer_image_primeToThree
    (hna : ¬ IsMulCommutative S) (e : K ≃* (Fin n → S))
    (J : Subrepresentation (ρ.comp K.subtype))
    (hv : J.toSubmodule.map (ρ v) = J.toSubmodule)
    (hc : Nat.Coprime 3 (Nat.card ↥(K ⊓ centralizer ({v} : Set A)))) :
    Nat.Coprime 3 (Nat.card ↥(
      (K.subgroupOf (extensionActor K v)).map (actionHom (constituentAction J hv)) ⊓
        centralizer ({actionHom (constituentAction J hv) (extensionMark K v)} :
          Set (actionImage (constituentAction J hv))))) := by
  rw [← constituent_centralizer_image hna e J hv]
  have hcard : Nat.card ↥((K ⊓ centralizer ({v} : Set A)).subgroupOf
      (extensionActor K v)) = Nat.card ↥(K ⊓ centralizer ({v} : Set A)) :=
    Nat.card_congr (subgroupOfEquivOfLe
      ((inf_le_left : K ⊓ centralizer ({v} : Set A) ≤ K).trans le_sup_left)).toEquiv
  exact (hcard.symm ▸ hc).of_dvd_right
    (((K ⊓ centralizer ({v} : Set A)).subgroupOf (extensionActor K v)).card_map_dvd
      (actionHom (constituentAction J hv)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
