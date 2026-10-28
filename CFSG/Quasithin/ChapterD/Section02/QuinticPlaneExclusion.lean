module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportResidual
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo.SmallActor
public import Theory.GroupAction.QuinticPlaneLine

/-!
# Excluding movement of a quintic plane by a two-perfect actor

A binary involution with fixed codimension two moves a normal quintic
plane through an order-five commutator with four-dimensional support.
This is a canonical small-support factor. The original rank-two cover
bounds the complete canonical family by two; a two-perfect actor therefore
normalizes that factor. Its coprime action on the quintic plane is trivial
by the fixed-line theorem, retaining the original quotient cover.

Source: Aschbacher–Smith 14.5.11, pp.1015–1016, and D.2.12–13,
pp.183–185, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD
variable {G E V : Type*} [Group G] [Finite G] [Group E] [Finite E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem involution_support_eq (t : G) (ht : orderOf t = 2) :
    subspaceCommutator ρ ⊤ (zpowers t) = LinearMap.range (ρ t - LinearMap.id) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp ha)
    have hi := Finset.mem_range.mp hi
    rw [ht] at hi
    interval_cases i
    · simp
    · exact ⟨v,by simp⟩
  · rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨t,mem_zpowers t,v,Submodule.mem_top,rfl⟩

/-- The two-perfect actor centralizes the actual quintic plane. -/
theorem quintic_plane_small_actor_centralizes
    (hf : Function.Injective ρ) (f : E →* G) (honto : Function.Surjective f)
    (hrank : primeRank 5 E ≤ 2) (R B X : Subgroup G) [R.Normal]
    [IsElementaryAbelian 5 R] (hR : Nat.card R = 25)
    (hB : IsElementaryTwo B) (hfaith : B ⊓ centralizer (R : Set G) = ⊥)
    (t : G) (ht : orderOf t = 2) (hBt : zpowers t = B)
    (hd : fixedCodim ρ B = 2) (hX : IsPPerfect 2 X)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card R)) :
    X ≤ centralizer (R : Set G) := by
  classical
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ hf
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hRp := IsElementaryAbelian.isPGroup 5 R
  have hrB : rank B = 1 := hBt ▸ (involution_actor_rank_and_fixedCodim ρ t ht).2.1
  have hcu : IsCubic ρ B := hBt ▸
    isCubic_of_isQuadratic (involution_actor_rank_and_fixedCodim ρ t ht).2.2.1
  obtain ⟨_,_,_,_,hc,hdim,hs⟩ := prime_five_small_actor ρ hf (by decide : 3 < 5)
    R B hRp hB hfaith hcu (by omega)
  let D := ⁅R,B⁆
  have hD : D ∈ smallSupportFactors G (Multiplicative V) 2 := by
    refine ⟨(commutator_le_left R B).trans ((show R ≤ pCore 5 G from le_sSup ⟨inferInstance,hRp⟩).trans (pCore_le_fitting G 5)),hc,?_⟩
    rw [BinaryGroupAction.commutator_card,hdim]
  have hti : IsInvolution t := ⟨fun h => by simp [h] at ht,ht ▸ pow_orderOf_eq_one t⟩
  have hsmall : Nat.card (commutatorAction (zpowers t) (Multiplicative V)) = 2 ^ 2 := by
    rw [BinaryGroupAction.commutator_card,involution_support_eq ρ t ht,
      ←fixedCodim_zpowers_eq_displacement_rank,hBt,hd]
  have htR : t ∉ centralizer (R : Set G) := by
    intro htR
    have hBC : B ≤ centralizer (R : Set G) := by rw [←hBt]; exact zpowers_le.mpr htR
    exact hB.1 (bot_unique ((le_inf le_rfl hBC).trans hfaith.le))
  have hbound : Nat.card (smallSupportFactors G (Multiplicative V) 2) ≤ 2 := by
    rcases smallSupportFactors_involution_alternative (V := Multiplicative V)
        (Or.inr rfl) t hti hsmall with hfix | ⟨Z,hZ,_,_,_,hfix⟩
    · have he : ρ t = ρ 1 := by
        ext v
        obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
          (show v ∈ subspaceCommutator ρ ⊤ D ⊔ fixedSpace ρ (D ⊔ B) from
            by rw [hs.sup_eq_top]; trivial)
        have hu' : ρ t u = u := congrArg Multiplicative.toAdd
          ((hfix.1 D hD).2 (Multiplicative.ofAdd u) (by rw [BinaryGroupAction.commutator_eq]; exact hu))
        have hw' : ρ t w = w := hw ⟨t,(show B ≤ D ⊔ B from le_sup_right) (hBt ▸ mem_zpowers t)⟩
        simp only [map_add,hu',hw',map_one,Module.End.one_apply]
      exact False.elim (hti.1 (hf he))
    · let I := smallSupportFactors G (Multiplicative V) 2
      let i : I := ⟨Z,hZ⟩
      have hprod := smallSupportFactors_internalDirectProduct (G := G) (V := Multiplicative V)
        (Or.inr rfl)
      apply commuting_pFamily_card_le_two (by decide : Odd 5) f honto hrank
        R hRp t ht htR (fun Y : I => Y.val) i
      · intro Y
        exact IsPGroup.of_card (n := 1) (by simpa using Y.property.2.1)
      · intro Y heY
        have hcY := Y.property.2.1
        rw [heY,card_bot] at hcY
        norm_num at hcY
      · exact hprod.1.pairwiseDisjoint
      · intro Y Z hne y hy z hz
        exact (hprod.2.1 hne y z hy hz).symm.eq
      · intro Y hne y hy z hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact ((hfix Y.val Y.property (fun e => hne (Subtype.ext e))).1 y hy).eq
  exact twoPerfect_coprime_quintic_line_centralizes X R D hX hcop hR hc
    (commutator_le_left R B) le_normalizer_of_normal
    (smallSupportFactors_twoPerfect_normalizes hbound X hX D hD)
end CFSG.Quasithin.ChapterD
