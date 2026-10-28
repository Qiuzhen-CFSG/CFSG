module

public import Theory.GroupTheory.ZStar.CoreFree
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Isolated involutions in a normal subgroup with an involution adjoined

The quotient of A⟨z⟩ by A is a two-group, so triviality of the odd core of A
implies triviality of the odd core of A⟨z⟩. Every conjugate of z in this
extension is already an A-conjugate. The core-free Z-star theorem therefore
turns isolation among those conjugates into centralization of A.

Source: GLS, Volume 4, Chapter 2, Lemma 4.9, the Z-star step in the A ≤ M
branch. Isolation itself must be supplied by the product-disconnection
argument; it is not assumed as part of any source theorem's conclusion.
-/

open Subgroup BenderSuzuki.PFAppendixIII

namespace Glauberman.ZStar
/-- An isolated involution is central in a finite group with trivial odd core. -/
public theorem central_of_isolated_of_oddCore_eq_bot
    {G : Type*} [Group G] [Finite G] {z : G}
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) (hcore : pPrimeCore 2 G = ⊥)
    (hiso : ∀ g : G, Commute (g * z * g⁻¹) z → g * z * g⁻¹ = z) :
    z ∈ center G := by
  obtain ⟨S, hzS, hc, hw⟩ := isolated_involution_local_data z
    (by simpa [pow_two] using hz.sq_eq_one) hz.ne_one (fun g h => hiso g h)
  exact glauberman_zstar_corefree hcore S z hz hzS hc hw

/-- Adjoining a normalizing involution preserves triviality of the odd core. -/
public theorem oddCore_sup_zpowers_eq_bot
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    {z : G} (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) (hA : pPrimeCore 2 A = ⊥) :
    pPrimeCore 2 (A ⊔ zpowers z : Subgroup G) = ⊥ := by
  let H := A ⊔ zpowers z
  have hAH : A ≤ H := le_sup_left
  let zH : H := ⟨z, (show zpowers z ≤ H from le_sup_right) (mem_zpowers z)⟩
  have hzH : BenderSuzuki.PFAppendixIII.IsInvolution zH :=
    ⟨fun h => hz.ne_one (congrArg Subtype.val h), Subtype.ext hz.sq_eq_one⟩
  have hcore : pPrimeCore 2 (A.subgroupOf H) = ⊥ := by
    have hm := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hAH).symm
    rw [hA, Subgroup.map_bot] at hm
    exact hm.symm
  apply pPrimeCore_eq_bot_of_isPGroup_quotient 2 (A.subgroupOf H) hcore
  apply quotient_isPGroup_of_sup_eq_top (zpowers zH) (A.subgroupOf H)
  · apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hzH.sq_eq_one hzH.ne_one
  · apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_subgroupOf_eq_of_le hAH,
      ← MonoidHom.range_eq_map, H.range_subtype]
    exact sup_comm _ _

/-- Isolation among the conjugates by A forces the involution to centralize A,
provided A is normal and has trivial odd core. -/
public theorem centralizes_normal_of_isolated_in_sup_zpowers
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    {z : G} (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) (hA : pPrimeCore 2 A = ⊥)
    (hiso : ∀ a : A, Commute ((a : G) * z * (a : G)⁻¹) z →
      (a : G) * z * (a : G)⁻¹ = z) :
    z ∈ centralizer (A : Set G) := by
  let H := A ⊔ zpowers z
  let zH : H := ⟨z, (show zpowers z ≤ H from le_sup_right) (mem_zpowers z)⟩
  have hzH : BenderSuzuki.PFAppendixIII.IsInvolution zH :=
    ⟨fun h => hz.ne_one (congrArg Subtype.val h), Subtype.ext hz.sq_eq_one⟩
  have hcentral : zH ∈ center H := by
    apply central_of_isolated_of_oddCore_eq_bot hzH (oddCore_sup_zpowers_eq_bot A hz hA)
    intro g hg
    obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_normal_left.mp g.property
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    have he : (g : G) * z * (g : G)⁻¹ = a * z * a⁻¹ := by
      rw [← hac, mul_inv_rev]
      calc
        a * z ^ k * z * ((z ^ k)⁻¹ * a⁻¹) =
            a * (z ^ k * z) * ((z ^ k)⁻¹ * a⁻¹) := by group
        _ = a * (z * z ^ k) * ((z ^ k)⁻¹ * a⁻¹) := by rw [((Commute.refl z).zpow_left k).eq]
        _ = a * z * a⁻¹ := by group
    apply Subtype.ext
    change (g : G) * z * (g : G)⁻¹ = z
    rw [he]
    apply hiso ⟨a, ha⟩
    have hh := congrArg Subtype.val hg.eq
    change ((g : G) * z * (g : G)⁻¹) * z = z * ((g : G) * z * (g : G)⁻¹) at hh
    rwa [he] at hh
  intro a ha
  exact congrArg Subtype.val (mem_center_iff.mp hcentral ⟨a, (show A ≤ H from le_sup_left) ha⟩)

/-- If the involution normally generates G, isolation would force a normal
odd-core-free subgroup to be abelian. -/
public theorem not_isolated_of_normalClosure_eq_top
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    {z : G} (hz : BenderSuzuki.PFAppendixIII.IsInvolution z)
    (hA : pPrimeCore 2 A = ⊥) (hna : ¬ IsMulCommutative A)
    (hgen : normalClosure ({z} : Set G) = ⊤) :
    ¬ (∀ a : A, Commute ((a : G) * z * (a : G)⁻¹) z →
      (a : G) * z * (a : G)⁻¹ = z) := by
  intro hiso
  have hzc := centralizes_normal_of_isolated_in_sup_zpowers A hz hA hiso
  have hle : normalClosure ({z} : Set G) ≤ centralizer (A : Set G) := by
    apply normalClosure_le_normal
    intro x hx
    have he : x = z := Set.mem_singleton_iff.mp hx
    subst x
    exact hzc
  have hc : ∀ x : G, x ∈ centralizer (A : Set G) :=
    fun x => hle (hgen ▸ mem_top x)
  apply hna
  exact ⟨⟨fun a b => Subtype.ext ((hc a) b b.property).symm⟩⟩

end Glauberman.ZStar
