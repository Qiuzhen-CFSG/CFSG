module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.MarkedOrdinarySource
public import CFSG.Quasithin.Chapter1.SourceInputs.InvolutionCentralizers
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PrimeCover
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import GorensteinWalter.PSL2Center
/-!
# The actual simple factors in the exchanged prime-source orbit

The source odd-then-two-core quotient determines the central quotient of the quasisimple factor. Its original Chapter1 marked Sylow fixer excludes the double prime-field cover. Thus the actual exchanged factor has trivial center and is isomorphic to the original source K.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection

/-- The actual Chapter 1 marked Sylow fixer excludes the double prime-field
cover on an ordinary component of the original involution centralizer. -/
theorem source_prime_component_center_eq_bot
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (i : G) (hi : orderOf i = 2)
    (J : Subgroup (centralizer ({i} : Set G)))
    (hJ : IsComponent (centralizer ({i} : Set G)) J)
    (e : (J ⧸ oddTwoCore J) ≃* PSL(2,ZMod p)) :
    center J = ⊥ ∧ Nonempty (J ≃* PSL(2,ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsQuasisimple J := hJ.2
  let Q := J ⧸ oddTwoCore J
  let : Nontrivial Q := e.nontrivial
  have hzQ : center Q = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    have he : e x ∈ center PSL(2,ZMod p) := MulEquivClass.apply_mem_center e hx
    simpa only [GorensteinWalter.psl2_center_eq_bot,mem_bot,map_one] using he
  have hz : oddTwoCore J = center J := by
    have hh := IsQuasisimple.comap_center_of_surjective
      (QuotientGroup.mk' (oddTwoCore J)) (QuotientGroup.mk'_surjective _)
    rw [show center (J ⧸ oddTwoCore J) = ⊥ from hzQ,
      MonoidHom.comap_bot,QuotientGroup.ker_mk'] at hh
    exact hh
  let eZ : (J ⧸ center J) ≃* PSL(2,ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hz.symm).trans e
  obtain ⟨P,N,w,h115,_⟩ := Chapter1.involution_component_source_catalogue hG i hi J hJ
  obtain ⟨_,α,T,_,hmark,_⟩ := h115.component_inputs J hJ
  have hmodel : ClassicalGroup.IsPSL (J ⧸ center J) 2 p :=
    ⟨ZMod p,inferInstance,inferInstance,by simp,⟨eZ⟩⟩
  have hbot := hmark.linear_two_prime_center_eq_bot hp (hp.odd_of_ne_two (by omega)) hmodel
  refine ⟨hbot,⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans eZ

private theorem simple_oddTwoCore_eq_bot {D : Type*} [Group D] [Finite D]
    [IsSimpleGroup D] [Group.IsPerfect D] : oddTwoCore D = ⊥ := by
  let : Group.IsSolvable (pPrimeCore 2 D) :=
    odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : Group.IsSolvable (oddTwoCore D) := oddTwoCore_isSolvable
  rcases (inferInstance : (oddTwoCore D).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : Group.IsSolvable (⊤ : Subgroup D) := h ▸ inferInstanceAs (Group.IsSolvable (oddTwoCore D))
    exact (Group.IsPerfect.not_isSolvable D
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom)
        topEquiv.surjective)).elim

/-- The literal exchanged component quotient in the original prime-source
pumpup lifts to the original simple component itself. -/
theorem source_exchanged_component_equiv
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (eK : K ≃* PSL(2,ZMod p))
    (i : G) (hi : orderOf i = 2)
    (J : Subgroup (centralizer ({i} : Set G)))
    (hJ : IsComponent (centralizer ({i} : Set G)) J)
    (e : (J ⧸ oddTwoCore J) ≃* (K ⧸ oddTwoCore K)) :
    center J = ⊥ ∧ Nonempty (J ≃* K) := by
  let : IsSimpleGroup K := (ComponentSelection.MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.1
  let : IsQuasisimple K := (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  let f : (K ⧸ oddTwoCore K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq simple_oddTwoCore_eq_bot).trans QuotientGroup.quotientBot
  obtain ⟨hz,⟨d⟩⟩ := source_prime_component_center_eq_bot hG hp hp7 i hi J hJ
    (e.trans (f.trans eK))
  exact ⟨hz,⟨d.trans eK.symm⟩⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
