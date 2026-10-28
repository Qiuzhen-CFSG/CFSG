module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.RankTwo.Splitting

/-!
# Largest elementary subgroups in the rank-two branch

The Sylow action has kernel S_C of order four. Its elementary images
have order at most eight, so every elementary subgroup of S has order
at most 32. Equality forces one of the two elementary eight-group images;
comparison of orders then gives the entire relative centralizer upstairs.
The elementary splittings attain the bound, establishing the source
family A(S) with no assumed classification or transitivity.

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

private theorem card_image_bound (E : Subgroup G) (hE : E ≤ d.S)
    (hel : IsElementaryAbelian 2 E) : Nat.card (image d E) ≤ 8 := by
  let := hel
  let : IsElementaryAbelian 2 (E.subgroupOf d.S) := IsElementaryAbelian.subgroupOf hE
  let : IsElementaryAbelian 2 (image d E) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 ((image d E).map (d.imageSylow : Subgroup AutA6).subtype) :=
    IsElementaryAbelian.map _
  have h := AlternatingSix.ShadowLocal.elementary_card_le_eight
    ((image d E).map (d.imageSylow : Subgroup AutA6).subtype)
  rwa [card_map_of_injective (d.imageSylow : Subgroup AutA6).subtype_injective] at h

private theorem card_le_kernel_mul_image (E : Subgroup G) (hE : E ≤ d.S) :
    Nat.card E ≤ Nat.card d.SC * Nat.card (image d E) := by
  let A := E.subgroupOf d.S
  let N := d.toImageSylow.ker.subgroupOf A
  let f : N → d.SC := fun a => ⟨a.val.val, by
    have ha : (a.val : d.S) ∈ d.toImageSylow.ker := a.property
    rw [d.toImageSylow_kernel] at ha
    exact ha⟩
  have hf : Function.Injective f := by
    intro a b he
    have hv : (a.val.val : G) = (b.val.val : G) :=
      congrArg (fun x : d.SC => (x : G)) he
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  have hn := Nat.card_le_card_of_injective f hf
  have hc := N.card_mul_index
  change Nat.card N * d.toImageSylow.ker.relIndex A = Nat.card A at hc
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv] at hc
  change Nat.card N * Nat.card (image d E) = Nat.card E at hc
  rw [← hc]
  exact Nat.mul_le_mul_right _ hn

theorem elementary_card_le_thirtyTwo (hcard : Nat.card d.SC = 4)
    (E : Subgroup G) (hE : E ≤ d.S) (hel : IsElementaryAbelian 2 E) : Nat.card E ≤ 32 := by
  have hc := card_le_kernel_mul_image d E hE
  rw [hcard] at hc
  exact hc.trans (Nat.mul_le_mul_left 4 (card_image_bound d E hE hel))

theorem elementary_thirtyTwo_cases (hcard : Nat.card d.SC = 4)
    (E : Subgroup G) (hE : E ≤ d.S) (hel : IsElementaryAbelian 2 E)
    (hc : 32 ≤ Nat.card E) :
    E = d.S ⊓ centralizer (fourZero d : Set G) ∨
      E = d.S ⊓ centralizer (fourOne d : Set G) := by
  have him := card_image_bound d E hE hel
  have hb := card_le_kernel_mul_image d E hE
  rw [hcard] at hb
  have hie : Nat.card (image d E) = 8 := by omega
  let := hel
  let : IsElementaryAbelian 2 (E.subgroupOf d.S) := IsElementaryAbelian.subgroupOf hE
  let : IsElementaryAbelian 2 (image d E) := IsElementaryAbelian.map _
  have hle : E ≤ preimage d (image d E) := by rw [preimage_image d E hE]; exact le_sup_left
  rcases ElementaryPair.elementary_eight_cases d.imageSylow (image d E) hie with h | h
  · rw [h, ← centralizer_fourZero] at hle
    exact Or.inl (eq_of_le_of_card_ge hle (by rw [card_centralizer_fourZero d hcard]; exact hc))
  · rw [h, ← centralizer_fourOne] at hle
    exact Or.inr (eq_of_le_of_card_ge hle (by rw [card_centralizer_fourOne d hcard]; exact hc))

theorem largest_elementary_family (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    largestElementary d.S =
      {d.S ⊓ centralizer (fourZero d : Set G), d.S ⊓ centralizer (fourOne d : Set G)} := by
  have hzero : d.S ⊓ centralizer (fourZero d : Set G) ∈ largestElementary d.S := by
    refine ⟨inf_le_left, centralizer_fourZero_elementary d hEA hcard, ?_⟩
    intro E hE hel
    rw [card_centralizer_fourZero d hcard]
    exact elementary_card_le_thirtyTwo d hcard E hE hel
  have hone : d.S ⊓ centralizer (fourOne d : Set G) ∈ largestElementary d.S := by
    refine ⟨inf_le_left, centralizer_fourOne_elementary d hEA hcard, ?_⟩
    intro E hE hel
    rw [card_centralizer_fourOne d hcard]
    exact elementary_card_le_thirtyTwo d hcard E hE hel
  ext E
  constructor
  · intro hE
    have hb := hE.2.2 _ inf_le_left hzero.2.1
    rw [card_centralizer_fourZero d hcard] at hb
    rcases elementary_thirtyTwo_cases d hcard E hE.1 hE.2.1 hb with h | h <;> simp [h]
  · intro hE
    rcases (show E = d.S ⊓ centralizer (fourZero d : Set G) ∨
        E = d.S ⊓ centralizer (fourOne d : Set G) from by simpa using hE) with rfl | rfl
    · exact hzero
    · exact hone

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
