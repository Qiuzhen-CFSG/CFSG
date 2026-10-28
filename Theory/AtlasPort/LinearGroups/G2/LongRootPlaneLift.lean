module

public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Theory.GroupTheory.PrimeRankInvolutionLift

/-!
# The elementary long-root plane in a central cover of G₂(4)

The two actual octonion root groups A and B give an elementary subgroup
of order sixteen. The E-root shear and the long Weyl reflection, as proved
in `ShortRootProducts.longRootLocal_isLong`, conjugate every nonidentity
element to a highest-root element, which is central in a Sylow two-group.
Thus I.2.2(5a) need only lift this plane. Its full inverse image through a
central kernel of order two is elementary of order thirty-two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(5a), printed p.409, and 16.3.9, printed p.1181. The covering
theorem is an explicit input; the root plane and its marking are proved.
The imported root formulas retain the attribution in LICENSES/ATLAS.txt.
-/

public section

namespace Atlas.G2.LongRootPlaneLift
open Subgroup Theory.GroupTheory
variable {F : Type*} [Field F] [CharP F 2]

theorem elementary : IsElementaryAbelian 2 (longRootLocal (F := F)) := by
  refine { toIsMulCommutative := inferInstance
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  obtain ⟨p, hp⟩ := x.property
  change (x : Model F) ^ 2 = 1
  rw [← hp, ← map_pow]
  have he : p ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change p.toAdd + p.toAdd = 0
    ext <;> exact CharTwo.add_self_eq_zero _
  rw [he, map_one]

theorem nonidentity_twoCentral [Finite F] {x : Model F}
    (hx : x ∈ longRootLocal) (hne : x ≠ 1) : IsSylowCentralInvolution x :=
  (ShortRootProducts.longRootLocal_isLong hx hne).twoCentral

omit [CharP F 2] in
theorem card_eq_sixteen [Finite F] (hF : Nat.card F = 4) :
    Nat.card (longRootLocal (F := F)) = 16 := by
  rw [card_longRootLocal, hF]
  norm_num

/-- The two-central lifting clause of I.2.2(5a), specialized to a given
central quotient. No lifting of the other involution class is assumed. -/
def CentralInvolutionLifting (K : Type*) [Group K] : Prop :=
  ∀ x : K ⧸ center K, IsSylowCentralInvolution x →
    ∃ y : K, QuotientGroup.mk' (center K) y = x ∧ orderOf y = 2

/-- The long-root plane proves rank at least five in the actual double
cover, from precisely the earlier two-central lifting clause. -/
theorem rank_ge_five {K : Type*} [Group K] [Finite K] [Finite F]
    (e : (K ⧸ center K) ≃* Model F) (hF : Nat.card F = 4)
    (hZ : Nat.card (center K) = 2) (hlift : CentralInvolutionLifting K) :
    5 ≤ primeRank 2 K := by
  let E : Subgroup (K ⧸ center K) := longRootLocal.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (longRootLocal (F := F)) := elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (center K) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        simpa only [hZ] using (pow_card_eq_one' (x := x))) }
  have hE : Nat.card E = 2 ^ 4 := by
    rw [Nat.card_congr (longRootLocal.equivMapOfInjective
      e.symm.toMonoidHom e.symm.injective).toEquiv.symm]
    exact card_eq_sixteen hF
  apply primeRank_ge_of_central_elementary_lifts (center K) le_rfl E hE
    (show Nat.card (center K) = 2 ^ 1 by simpa using hZ)
  intro x hx _
  by_cases hx1 : x = 1
  · exact ⟨1, by simpa using hx1.symm, one_pow _⟩
  · obtain ⟨w, hw, rfl⟩ := hx
    have hw1 : w ≠ 1 := fun he => hx1 (by simp [he])
    obtain ⟨y, hy, hy2⟩ := hlift _ ((nonidentity_twoCentral hw hw1).map e.symm)
    exact ⟨y, hy, hy2 ▸ pow_orderOf_eq_one y⟩

end Atlas.G2.LongRootPlaneLift
