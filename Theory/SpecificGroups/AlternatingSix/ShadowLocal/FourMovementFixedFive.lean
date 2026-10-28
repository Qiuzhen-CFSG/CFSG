module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Automorphisms
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.GroupAction.AutomorphismFixedTransport

/-! The two four-groups of an inner Sylow D8 distinguish the natural S6
inside Aut(A6): in a two-group containing their inner actions, an automorphism
is natural exactly when it preserves either selected four-group. Therefore an
index-two stabilizing subgroup and one moving element force every outside
element to have nonnatural image. An involution with that image fixes D10,
so five divides the actual ambient relative centralizer.

This is the marked terminal action in Aschbacher--Smith 2.4.29, printed p.546.
It retains the real half-Sylow subgroup and four-group movement; outer action
alone does not imply this conclusion.
-/
public section
open Subgroup
namespace AlternatingSix.ShadowLocal
open Identification SylowGeometry

theorem natural_iff_stabilizes_four_in_two_group
    (A : Subgroup AutA6) (hA : IsPGroup 2 A)
    (F : Subgroup A6) [IsKleinFour F]
    (hFA : F.map (MulAut.conj : A6 →* AutA6) ≤ A)
    (β : A) : (β : AutA6) ∈ natural ↔ F.map (β : AutA6).toMonoidHom = F := by
  obtain ⟨P,hAP⟩ := hA.exists_le_sylow
  let F' := F.map (MulAut.conj : A6 →* AutA6)
  have hFP : F' ≤ (P : Subgroup AutA6) := hFA.trans hAP
  let E := F'.subgroupOf (P : Subgroup AutA6)
  let e : F ≃* E := (F.equivMapOfInjective MulAut.conj inner_injective).trans
    (subgroupOfEquivOfLe hFP).symm
  let : IsKleinFour E := ⟨(Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two⟩
  have hED : E ≤ sylowInner P := by
    intro x hx
    exact map_le_range _ _ hx
  have hnorm : normalizer (E : Set P) = sylowNatural P := by
    rcases kleinFour_subgroups_inner P E hED with h | h
    · rw [h]; exact normalizer_kleinZero P
    · rw [h]; exact normalizer_kleinOne P
  let b : P := ⟨β,hAP β.property⟩
  have hn : b ∈ normalizer (E : Set P) ↔
      (β : AutA6) ∈ normalizer (F' : Set AutA6) := by
    simp only [mem_normalizer_iff]
    constructor
    · intro h x
      by_cases hxP : x ∈ (P : Subgroup AutA6)
      · exact h ⟨x,hxP⟩
      · have hnP : (β : AutA6) ∈ normalizer (P : Set AutA6) := P.toSubgroup.le_normalizer b.property
        have hnmem := mem_normalizer_iff.mp hnP x
        exact iff_of_false (fun hx=>hxP (hFP hx))
          (fun hx=>hxP (hnmem.mpr (hFP hx)))
    · intro h x
      exact h x
  rw [←FourNormalizers.mem_inner_normalizer_iff]
  exact (show (β : AutA6) ∈ natural ↔ b ∈ normalizer (E : Set P) by rw [hnorm];rfl).trans hn
end AlternatingSix.ShadowLocal

open Subgroup
namespace AlternatingSix.ShadowLocal
variable {G : Type*} [Group G]

theorem outside_natural_of_index_two
    (f : G →* AutA6) (R : Subgroup G) (hR : R.index=2)
    (hRn : R ≤ natural.comap f) (hx : ∃x : G, f x ∉ natural)
    (i : G) (hi : i ∉ R) : f i ∉ natural := by
  let N := natural.comap f
  have hN : N ≠ ⊤ := by
    obtain ⟨x,hx⟩ := hx
    intro hn
    exact hx (show x∈N from hn ▸ mem_top x)
  have hd : N.index ∣ 2 := hR ▸ index_dvd_of_le hRn
  have hn : N.index=2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hN (index_eq_one.mp h)).elim
    · exact h
  have he : R=N := by
    have hm := relIndex_mul_index hRn
    rw [hR,hn] at hm
    change R.relIndex N*2=2 at hm
    have hi : R.relIndex N=1 := by omega
    exact le_antisymm hRn (relIndex_eq_one.mp hi)
  exact fun hh=>hi (he.symm ▸ hh)
end AlternatingSix.ShadowLocal

open Subgroup
namespace AlternatingSix.ShadowLocal
variable {G : Type*} [Group G]
theorem five_dvd_relative_centralizer_of_outside_natural
    (K : Subgroup G) (i : normalizer (K : Set G))
    (hi : orderOf (i : G) = 2) (e : K ≃* A6)
    (hn : MulAut.congr e (K.normalizerMonoidHom i) ∉ natural) :
    5 ∣ Nat.card (K ⊓ centralizer ({(i : G)} : Set G) : Subgroup G) := by
  let α := K.normalizerMonoidHom i
  let β := MulAut.congr e α
  have hip : i^2=1 := Subtype.ext (hi ▸ pow_orderOf_eq_one (i:G))
  have hαp : α^2=1 := by
    change (K.normalizerMonoidHom i)^2=1
    rw [←map_pow,hip,map_one]
  have hβp : β^2=1 := by
    change (MulAut.congr e α)^2=1
    rw [←map_pow,hαp,map_one]
  have hβn : β≠1 := by
    intro hh
    apply hn
    change β ∈ natural
    rw [hh]
    exact natural.one_mem
  have hβ : orderOf β=2 := orderOf_eq_prime hβp hβn
  let f : α.fixedSubgroup ≃* (K ⊓ centralizer ({(i:G)} : Set G) : Subgroup G) :=
    K.normalizerFixedEquivCentralizer i
  let g : α.fixedSubgroup ≃* β.fixedSubgroup := MulAut.fixedSubgroupCongr e α
  have hc : Nat.card (K ⊓ centralizer ({(i:G)} : Set G) : Subgroup G) = 10 := by
    calc
      Nat.card (K ⊓ centralizer ({(i:G)} : Set G) : Subgroup G) =
          Nat.card α.fixedSubgroup := (Nat.card_congr f.toEquiv).symm
      _ = Nat.card β.fixedSubgroup := Nat.card_congr g.toEquiv
      _ = 10 := by
        have hf : β.fixedSubgroup = GLS3.Chapter5.automorphismFixedSubgroup β := by
          ext x
          rw [MulAut.mem_fixedSubgroup]
          rfl
        rw [hf]
        exact outside_natural_involution_fixed_card β hβ hn
  rw [hc]
  decide
end AlternatingSix.ShadowLocal

namespace AlternatingSix.ShadowLocal
open Subgroup
variable {P : Type*} [Group P]

theorem outside_natural_of_four_movement
    (f : P →* AutA6) (hP : IsPGroup 2 P)
    (F : Subgroup A6) [IsKleinFour F]
    (hF : F.map (MulAut.conj : A6 →* AutA6) ≤ f.range)
    (R : Subgroup P) (hR : R.index=2)
    (hRF : ∀r∈R, F.map (f r).toMonoidHom=F)
    (hx : ∃x:P, F.map (f x).toMonoidHom≠F)
    (i:P) (hi:i∉R) : f i ∉ natural := by
  have hnat (x:P) : f x∈natural ↔ F.map (f x).toMonoidHom=F :=
    natural_iff_stabilizes_four_in_two_group f.range (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective) F hF ⟨f x,⟨x,rfl⟩⟩
  exact outside_natural_of_index_two f R hR
    (fun r hr=>(hnat r).mpr (hRF r hr))
    (by obtain ⟨x,hx⟩:=hx; exact ⟨x,fun hn=>hx ((hnat x).mp hn)⟩) i hi
end AlternatingSix.ShadowLocal
namespace AlternatingSix.ShadowLocal
open Subgroup
variable {G : Type*} [Group G]

theorem five_dvd_centralizer_of_four_movement
    (K T : Subgroup G) (hTK : T ≤ normalizer (K:Set G))
    (hT : IsPGroup 2 T) (e : K ≃* A6)
    (F : Subgroup A6) [IsKleinFour F]
    (R : Subgroup T) (hR : R.index=2)
    (hF : F.map (MulAut.conj : A6 →* AutA6) ≤
      (((MulAut.congr e).toMonoidHom.comp K.normalizerMonoidHom).comp (inclusion hTK)).range)
    (hRF : ∀r∈R, F.map
      (MulAut.congr e (K.normalizerMonoidHom (inclusion hTK r))).toMonoidHom=F)
    (hx : ∃x:T, F.map
      (MulAut.congr e (K.normalizerMonoidHom (inclusion hTK x))).toMonoidHom≠F)
    (i : T) (hi : i∉R) (hi2 : orderOf (i:G)=2) :
    5 ∣ Nat.card (K ⊓ centralizer ({(i:G)} : Set G) : Subgroup G) := by
  let f := ((MulAut.congr e).toMonoidHom.comp K.normalizerMonoidHom).comp (inclusion hTK)
  have hn : f i∉natural := outside_natural_of_four_movement f hT F hF R hR hRF hx i hi
  exact five_dvd_relative_centralizer_of_outside_natural K (inclusion hTK i) hi2 e hn
end AlternatingSix.ShadowLocal
