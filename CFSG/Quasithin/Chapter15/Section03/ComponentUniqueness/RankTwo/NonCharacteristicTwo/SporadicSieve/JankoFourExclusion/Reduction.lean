module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.InnerGeometry

/-!
# A solvable-radical obstruction to the J₄ rank-two configuration

The full Frattini shadow makes YS solvable and forces nine to divide |Y|.
Once the component fills the centralizer quotient, the source normality is
normality inside M. Thus the solvable radical of M has order divisible by
nine. Full innerness of the marked model makes the component fill this
quotient, by the exact inner-preimage theorem for its faithful action.

The innerness premise is explicit here; an outer two-group bound cannot
replace it. Source: Aschbacher--Smith, 15.3.41--42, printed p.1138.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
open Parabolics.BinaryRecognition.InnerGeometry

variable {H : Type*} [Group H] [Finite H]

/-- The complete local shadow and relative normality force a factor of nine
in the order of the actual local solvable radical. -/
theorem nine_dvd_local_radical {M Y S : Subgroup H}
    (d : LocalConfiguration (⊤ : Subgroup H) M Y S) :
    9 ∣ Nat.card (solvableRadical M) := by
  have hYM : Y ≤ M := d.yplus_le.trans inf_le_left
  let : Group.IsSolvable (Y ⊔ S : Subgroup H) := shadow_join_solvable d.shadow
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show Y ≤ Y ⊔ S from le_sup_left)) (inclusion_injective _)
  let a := subgroupOfEquivOfLe hYM
  let : Group.IsSolvable (Y.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective
  have hle := le_solvableRadical (Y.subgroupOf M) (normal_y_subgroupOf d) inferInstance
  have h9 := nine_dvd_card_y d
  rw [← Nat.card_congr a.toEquiv] at h9
  exact h9.trans (card_dvd_of_le hle)

/-- An actual local-model equivalence transfers the radical obstruction. -/
theorem no_localConfiguration_of_radical_bound {A : Type*} [Group A] [Finite A]
    {M Y S : Subgroup H} (d : LocalConfiguration (⊤ : Subgroup H) M Y S)
    (e : M ≃* A) (ha : ¬ 9 ∣ Nat.card (solvableRadical A)) : False := by
  apply ha
  have he : Nat.card (solvableRadical M) = Nat.card (solvableRadical A) := by
    rw [← map_solvableRadical_equiv e, card_map_of_injective e.injective]
  exact he ▸ nine_dvd_local_radical d

variable {G : Type*} [Group G] {I L M Y S : Subgroup G}
variable [(L.subgroupOf I).Normal]

/-- Full innerness, rather than a bound on Out, fills the component quotient. -/
theorem componentImage_eq_top_of_inner {A : Type*} [Group A]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* A)
    (hi : Function.Surjective (MulAut.conj : A →* MulAut A)) :
    componentImage I L L = ⊤ := by
  have ht : MulAut.innerSubgroup A = ⊤ :=
    (MulAut.conj : A →* MulAut A).range_eq_top_of_surjective hi
  rw [← modelAction_comap_inner d e, ht, comap_top]

/-- The actual component coordinates extend to the whole centralizer quotient
when every automorphism of the supplied model is inner. -/
noncomputable def ambientModelOfInner {A : Type*} [Group A]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* A)
    (hi : Function.Surjective (MulAut.conj : A →* MulAut A)) :
    ComponentQuotient I L ≃* A :=
  ((Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr
    (componentImage_eq_top_of_inner d e hi).symm)).trans (componentModel d e)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoFourExclusion
