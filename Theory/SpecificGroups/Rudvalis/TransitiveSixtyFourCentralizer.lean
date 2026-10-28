module
public import Theory.SpecificGroups.Rudvalis.TransitiveSixtyFourNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.PointCoreBound
public import Theory.SpecificGroups.SymmetricFive.PentagonNormalizer
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Centralizers of transitive Rudvalis six-spaces

A centralizing quintic would kill the whole six-space in the literal S₅
point quotient, contradicting the native point-core bound. If the module
centralizer has order prime to three, its involution-centralizer order then
makes it a two-group. The transitive normalizer-core theorem identifies it
with the module. The original terminal Chapter13 marking supplies the
coprimality premise from its ambient source context.

Source: Aschbacher--Smith 4.4.3 case (c), printed p.623, using the
Rudvalis local structure from 4.2.13, printed pp.611--612.
-/

public section
namespace Rudvalis
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

/-- A quintic cannot centralize an elementary 64-subgroup containing a
central-class involution: the five-point quotient would kill the whole module. -/
theorem sixtyFour_no_centralizing_five
    (E : Subgroup Model) [IsElementaryAbelian 2 E] (hE : Nat.card E = 64)
    (z : E) (hclass : IsConj (z : Model) (b ^ 2))
    (x : Model) (hx : orderOf x = 5) (hc : x ∈ centralizer (E : Set Model)) : False := by
  let D := centralizer ({(z : Model)} : Set Model)
  have hED : E ≤ D := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hu z.property)
  let xd : D := ⟨x, mem_centralizer_singleton_iff.mpr (hc z z.property).symm⟩
  let q := (InvolutionCentralizers.firstQuotientEquiv hclass).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 D))
  have hqk : q.ker = pCore 2 D := by
    ext u
    change InvolutionCentralizers.firstQuotientEquiv hclass
      (QuotientGroup.mk' (pCore 2 D) u) = 1 ↔ _
    rw [←map_one (InvolutionCentralizers.firstQuotientEquiv hclass),
      (InvolutionCentralizers.firstQuotientEquiv hclass).injective.eq_iff]
    exact QuotientGroup.eq_one_iff u
  have hxo : orderOf xd = 5 := (orderOf_coe xd).symm.trans hx
  have hqx : orderOf (q xd) = 5 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (hqk.symm ▸ pCore_isPGroup) xd (by rw [hxo]; decide)).trans hxo
  have hfive : Nat.card (centralizer (zpowers (q xd) : Set (Equiv.Perm (Fin 5)))) = 5 :=
    Equiv.Perm.five_subgroup_centralizer_card _ (by rw [Nat.card_zpowers,hqx])
  apply PointCoreBound.elementary_not_le_point_core z hclass E hE
  intro u hu
  let ud : D := ⟨u,hED hu⟩
  have hqu : q ud ∈ centralizer (zpowers (q xd) : Set (Equiv.Perm (Fin 5))) := by
    rw [zpowers_eq_closure,centralizer_closure]
    apply mem_centralizer_singleton_iff.mpr
    have he : ud * xd = xd * ud := Subtype.ext (hc u hu)
    simpa only [map_mul] using congrArg q he
  have hd5 : orderOf (q ud) ∣ 5 := by
    simpa only [hfive] using Subgroup.orderOf_dvd_natCard _ hqu
  have hd2 : orderOf (q ud) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [←map_pow]
    have he : ud ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu)
    rw [he,map_one])
  have hker : ud ∈ q.ker := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 5) hd2 hd5)
  exact ⟨ud,hqk ▸ hker,rfl⟩

/-- The centralizer of a transitive elementary 64-subgroup is precisely that
subgroup when its ambient centralizer has order prime to three. -/
theorem transitive_sixtyFour_centralizer
    (B E : Subgroup Model) [IsElementaryAbelian 2 E]
    (hEB : E ≤ B) (hBE : B ≤ normalizer (E : Set Model))
    (hE : Nat.card E = 64) (hB : Nat.card B = 64 * 6048)
    (hcore : B.pCoreIn 2 = E)
    (ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y)
    (hthree : Nat.Coprime 3 (Nat.card (centralizer (E : Set Model)))) :
    centralizer (E : Set Model) = E := by
  let C := centralizer (E : Set Model)
  let N := normalizer (E : Set Model)
  have hne : E ≠ ⊥ := E.one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hclass,hD,_⟩ := transitive_sixtyFour_involution_class B E hBE hE
    (by rw [hB]; exact dvd_mul_left _ _) ht z hz
  have hCD : C ≤ centralizer ({(z : Model)} : Set Model) :=
    centralizer_le (Set.singleton_subset_iff.mpr z.property)
  have hfive : Nat.Coprime 5 (Nat.card C) := by
    apply (Nat.prime_five.coprime_iff_not_dvd).mpr
    intro hd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 hd
    exact sixtyFour_no_centralizing_five E hE z hclass x
      ((orderOf_coe x).trans hx) x.property
  have hCtwo : IsPGroup 2 C := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨14,?_⟩
    have hd := card_dvd_of_le hCD
    rw [hD] at hd
    have hc : Nat.Coprime (Nat.card C) 15 := (hthree.mul_left hfive).symm
    exact hc.dvd_of_dvd_mul_right hd
  have hCN : C ≤ N := centralizer_le_normalizer _
  have hp : C ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hCtwo hCN
    (normalizer_le_normalizer_centralizer E)
  have hPN := transitive_sixtyFour_overgroup_core B E N hEB hBE le_rfl hE hB hcore ht
  exact le_antisymm (hp.trans hPN.le) E.le_centralizer
end Rudvalis
