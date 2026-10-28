module

public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Shapes
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.SylowCenters
public import Theory.SpecificGroups.Suzuki.SubgroupParameters

/-!
# The Sylow centralizer-index bound in the Suzuki case

An actual E₄ × Sz(8) isomorphism gives centralizer order 116480. The subgroup
C_P(t) embeds both in that centralizer and in P, whose order is 16384.
Its order therefore divides their gcd, 256, giving index at least 64.
This uses only the already certified local Sylow order and the genuine Suzuki
order formula. No centralizer table or ambient simplicity is assumed.

The product isomorphism remains an explicit model input. Once it is supplied,
this proves the strict greater-than-two bound consumed by Aschbacher–Smith
16.1.8 in case 16.1.7(3)(i), printed pp.1172–1173.
-/

@[expose] public section

open Subgroup
namespace Rudvalis.InvolutionCentralizers

/-- The order of E₄ × Sz(8) forces index at least 64 in every ambient Sylow subgroup. -/
theorem centralizer_sylow_index_ge_sixtyFour_of_card (t : Model)
    (hcard : Nat.card (Centralizer t) = 116480) (P : Sylow 2 Model) :
    64 ≤ ((Centralizer t).subgroupOf P).index := by
  let C := (Centralizer t).subgroupOf P
  have hdP : Nat.card C ∣ 16384 := by
    rw [← sylow_card P]
    exact C.card_subgroup_dvd_card
  let f : C →* Centralizer t :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Centralizer t => z.val) h))
  have hdC : Nat.card C ∣ 116480 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_injective f hf
  have hd : Nat.card C ∣ 256 := by
    have := Nat.dvd_gcd hdP hdC
    norm_num at this
    exact this
  have hle : Nat.card C ≤ 256 := Nat.le_of_dvd (by decide) hd
  have he := C.card_mul_index
  rw [sylow_card] at he
  change 64 ≤ C.index
  nlinarith

/-- The actual E₄ × Sz(8) centralizer shape gives the strict index bound of 16.1.8. -/
theorem suzuki_centralizer_sylow_index (t : Model)
    (e : Centralizer t ≃* Elementary 2 × SzEight) (P : Sylow 2 Model) :
    2 < ((Centralizer t).subgroupOf P).index := by
  have hs : Nat.card SzEight = 29120 := by
    rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)]
    norm_num
  have hc : Nat.card (Centralizer t) = 116480 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hs]
    norm_num [Elementary, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card]
  exact lt_of_lt_of_le (by decide : 2 < 64)
    (centralizer_sylow_index_ge_sixtyFour_of_card t hc P)

end Rudvalis.InvolutionCentralizers
