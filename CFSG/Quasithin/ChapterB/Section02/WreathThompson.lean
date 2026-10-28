module
public import Theory.SpecificGroups.OrthogonalFourBinary.CyclicFourOffenders
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor
import all CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor
/-!
# Thompson subgroups under a natural cyclic-four image

A maximum elementary subgroup crossing the module centralizer gives an
actual offender by B.2.7. Its image lies in the given cyclic four-group,
whose involution has fixed codimension two on the natural moved space.
The rank-one offender inequality is impossible. B.2.10 then identifies
the original Thompson subgroup with that of the two-core and proves its
normality. The fixed complement is retained without an additional
splitting assumption: restricting to the moved space suffices.

Source: Aschbacher–Smith, original 13.2.9, final paragraph, printed p.881.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- Neither full small natural actor allows an offender in a cyclic four-group. -/
theorem SmallNaturalMovedAction.not_offender_le_cyclicFour
    {ρ : Representation (ZMod 2) G V} (h : SmallNaturalMovedAction ρ)
    (r : G) (hr : orderOf r = 4) (B : Subgroup G) (hB : B ≤ zpowers r) :
    ¬ IsOffender ρ B := by
  rcases h with ⟨c,e,he⟩ | ⟨c,e,he⟩
  · have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    have ho : orderOf (e r) = 4 := (orderOf_injective e.toMonoidHom e.injective r).trans hr
    have hd := orderOf_dvd_natCard (e r)
    rw [ho,hc] at hd
    norm_num at hd
  · exact OrthogonalFourBinary.no_offender_le_cyclicFour ρ
      SolvableFFFactors.naturalMovedSubrepresentation e c he r hr B hB

variable {H : Type*} [Group H] [Finite H]
/-- The actual cyclic-four image forces the original Thompson subgroup into
its centralizer kernel, and hence identifies it with the two-core Thompson subgroup. -/
theorem smallNatural_thompson_eq_of_cyclicFour_image
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* G) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set H))
    (R : Subgroup H) (hUR : U ≤ R) (hQR : pCore 2 H ≤ R)
    (hcore : pCore 2 H = R ⊓ centralizer (U : Set H))
    (ha : SmallNaturalMovedAction (NormalElementaryQuotient.representation U q hq hker))
    [IsCyclic (R.map q)] (hcard : Nat.card (R.map q) = 4) :
    thompsonJ R 0 = thompsonJ (pCore 2 H) 0 ∧ (thompsonJ R 0).Normal := by
  obtain ⟨r,hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R.map q)
  have ho : orderOf (r : G) = 4 :=
    (orderOf_injective (R.map q).subtype (R.map q).subtype_injective r).trans (hr.trans hcard)
  have hgen : R.map q = zpowers (r : G) := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr r.property)
    rw [Nat.card_zpowers,ho,hcard]
  have hJ : thompsonJ R 0 ≤ centralizer (U : Set H) := by
    rw [thompsonJ_zero]
    apply sSup_le
    intro A hA
    by_contra hn
    have hn' : ¬ A ≤ q.ker := by rwa [hker]
    have hoff := NormalElementaryQuotient.maxElementary_isOffender U q hq hker R A hUR hA hn'
    exact ha.not_offender_le_cyclicFour (r : G) ho (A.map q)
      ((map_mono hA.1).trans_eq hgen) hoff
  have hresult := lemma_B_2_10_centralizing U R hUR hQR hcore hJ
  exact ⟨hresult.1,hresult.2.2.1⟩
end CFSG.Quasithin.ChapterB
