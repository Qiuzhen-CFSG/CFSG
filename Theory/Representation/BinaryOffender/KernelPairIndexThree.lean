module
public import Theory.Representation.BinaryOffender.InvariantAction
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
/-!
# The two action kernels and an index-three supplement

If a faithful binary action splits as a marked six-group support and its
fixed supplement, and the full support image has order thirty-six, the join
of the two pointwise kernels and a Sylow two subgroup has index dividing
three. Faithfulness identifies the marked six-group with its support image;
its kernel-preimage has index six, and the Sylow excludes the even divisor.

This is the kernel-product step of Aschbacher--Smith 15.1.2, printed p.1085.
The actual local-action consumer is `RatioReduction/ProperOrbitIndexThree`.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

theorem kernel_pair_sylow_index_dvd_three
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (H : Subgroup G) (W : Submodule (ZMod 2) V)
    (hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W)
    (hsup : W ⊔ fixedSpace ρ H = ⊤)
    (hH : Nat.card H = 6) (hI : Nat.card (subspaceActionImage ρ W) = 36)
    (S : Sylow 2 G) :
    (subspaceKernel ρ W ⊤ ⊔ subspaceKernel ρ (fixedSpace ρ H) ⊤ ⊔
      (S : Subgroup G)).index ∣ 3 := by
  let C := subspaceKernel ρ W ⊤
  let D := subspaceKernel ρ (fixedSpace ρ H) ⊤
  let K := C ⊔ D ⊔ (S : Subgroup G)
  have hfaith : subspaceKernel ρ W H = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply mem_bot.mpr
    apply hf
    ext v
    obtain ⟨w,hw,y,hy,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ fixedSpace ρ H from hsup ▸ Submodule.mem_top)
    change ∀ h : H, ρ (h : G) y = y at hy
    simp only [map_one, Module.End.one_apply, map_add, hx.2 w hw, hy ⟨x,hx.1⟩]
  have hcardH : Nat.card (restrictedSubgroup ρ W H) = 6 := by
    have hc := card_subspaceKernel_mul_image ρ W H (le_top.trans hW)
    simpa only [hfaith, Subgroup.card_bot,
      one_mul, hH] using hc
  let q := invariantActionHom ρ W hW
  have hq : Function.Surjective q := invariantActionHom_surjective ρ W hW
  have hmap : (H.map q).index = 6 := by
    rw [invariantActionHom_map ρ W hW H]
    have hc := (restrictedSubgroup ρ W H).index_mul_card
    rw [hcardH, hI] at hc
    omega
  have hC : q.ker = C := invariantActionHom_ker ρ W hW
  have hCH : (H ⊔ C).index = 6 := by
    rw [← hC, ← comap_map_eq, index_comap_of_surjective (H.map q) hq]
    exact hmap
  have hHD : H ≤ D := by
    intro x hx
    exact ⟨mem_top _,fun v hv => hv ⟨x,hx⟩⟩
  have hHK : H ⊔ C ≤ K := sup_le
    (hHD.trans (le_sup_right.trans le_sup_left)) (le_sup_left.trans le_sup_left)
  have hd6 : K.index ∣ 6 := hCH ▸ index_dvd_of_le hHK
  have hn2 : ¬ 2 ∣ K.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (show (S : Subgroup G) ≤ K from le_sup_right)))
  have hcop : Nat.Coprime K.index 2 :=
    Nat.coprime_comm.mpr ((Nat.prime_two.coprime_iff_not_dvd).mpr hn2)
  exact (Nat.Coprime.dvd_mul_right hcop).mp hd6
end Representation.BinaryOffender
