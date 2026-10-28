module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.QuaternionResidual.Image
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions

/-!
# The common four-group from the embedded quaternion core

For a swapping involution a outside a quaternion central product U, the
subgroup A = ⟨a,[U,a]⟩ is elementary of order sixteen. Its centralizer in U
is exactly [U,a], of order eight. Consequently U induces a group of order
four on A. If A is normal in T = U⟨a⟩, this is also the image of T. Every
subgroup normalizing U normalizes that image after restriction to N(A).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. In the application A = J(T); only the resulting
normalization is needed below. No assumption that U = O₂(H) is used.
-/

namespace Subgroup.QuaternionResidual

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The kernel on the actual source sixteen is its fixed quaternion diagonal. -/
public theorem core_centralizer_of_swap (U A : Subgroup G)
    (d : QuaternionCentralProductData U) (a : G)
    (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆) :
    U ⊓ centralizer (A : Set G) = ⁅U, zpowers a⁆ ∧
      Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) = 8 := by
  obtain ⟨hfixed, hele, hcard⟩ := d.elementary_sixteen_of_swap U a ha hout hswap
  have hAC : IsElementaryAbelian 2 A := hA ▸ hele
  let := hAC
  have hcommU : ⁅U, zpowers a⁆ ≤ U := hfixed ▸ inf_le_left
  have hcommA : ⁅U, zpowers a⁆ ≤ A := hA ▸ le_sup_right
  have haA : a ∈ A := hA ▸ mem_sup_left (mem_zpowers a)
  have hker : U ⊓ centralizer (A : Set G) = ⁅U, zpowers a⁆ := by
    apply le_antisymm
    · intro x hx
      rw [hfixed]
      exact ⟨hx.1, mem_centralizer_singleton_iff.mpr (hx.2 a haA).symm⟩
    · exact le_inf hcommU (hcommA.trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  refine ⟨hker, ?_⟩
  have hn : a ∈ normalizer ((⁅U, zpowers a⁆ : Subgroup G) : Set G) := by
    apply centralizer_le_normalizer
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((hfixed ▸ hx).2)
  have hc := card_sup_zpowers_of_normalizing_involution ⁅U, zpowers a⁆ a ha
    (fun h => hout (hcommU h)) hn
  rw [sup_comm, hcard] at hc
  rw [hker]
  omega

/-- The actual T-image is the order-four U-image, normal in the relative
normalizer image of every actor K containing and normalizing U. -/
public theorem common_image_of_swap (U A T K : Subgroup G)
    (d : QuaternionCentralProductData U) (a : G)
    (ha : a ^ 2 = 1) (hout : a ∉ U)
    (hswap : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
      d.right.map U.subtype)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆)
    (hT : T = U ⊔ zpowers a) (hTN : T ≤ normalizer (A : Set G))
    (hUK : U ≤ K) (hKU : K ≤ normalizer (U : Set G)) :
    image A T = image A U ∧ Nat.card (image A T) = 4 ∧
      image A T ≤ image A (K ⊓ normalizer (A : Set G)) ∧
      image A (K ⊓ normalizer (A : Set G)) ≤
        normalizer (image A T : Set (NormalizerAction.Star A)) := by
  obtain ⟨hfixed, hele, _⟩ := d.elementary_sixteen_of_swap U a ha hout hswap
  have hAC : IsElementaryAbelian 2 A := hA ▸ hele
  let := hAC
  have hUN : U ≤ normalizer (A : Set G) := (hT ▸ le_sup_left).trans hTN
  have hTA : T = U ⊔ A := by
    rw [hT, hA]
    apply le_antisymm
    · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)
    · apply sup_le le_sup_left
      exact sup_le le_sup_right ((hfixed ▸ inf_le_left).trans le_sup_left)
  have him : image A T = image A U := by rw [hTA, image_sup_self A U hUN]
  refine ⟨him, ?_, ?_, ?_⟩
  · have hc := card_image_mul_centralizer A U hUN
    rw [(core_centralizer_of_swap U A d a ha hout hswap hA).2, d.card] at hc
    rw [him]
    omega
  · rw [him, image_inf_normalizer]
    exact image_mono A hUK
  · rw [him, image_inf_normalizer]
    exact image_le_normalizer A U K hUN hKU

end Subgroup.QuaternionResidual
