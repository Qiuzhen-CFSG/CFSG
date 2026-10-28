module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FamilyTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure
public import Theory.ElementaryAbelian.AbelianNormalClosure
/-!
# The eight-actor in the centralizer radical quotient

At p = 3 the full centralizer is solvable and is trapped. For p > 3, the
actor's actual inner four-group survives the radical, so the existing SL₂
structure gives all E₂ clauses, including the corrected local tau orbit.
If the radical kills a four-group, this E₂ member has rank at most one and
traps the full centralizer. Otherwise the central involution forces the
kernel to have order two, and the original eight-actor has image of order
four. This remaining case requires quotient geometry, especially at p = 5.

Source: Aschbacher--Smith E.1.2, E.1.5, E.1.13--14, pp.210--214;
A.3.21(a), p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- The small-prime branch, valid in every normal PSU₃(3) two-extension. -/
theorem centralizer_le_of_prime_three (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU L 3 3) (d : LargeFamilyObstruction T)
    {z : G} (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let := inner_centralizer_solvable_of_prime_three L T hLT hmodel z hzL hz
  exact solvable_sylow_overgroup_le d _ hTz

/-- The full E₂ structure for the original actor follows from its inner four-group.
This asserts no rank-one bound on its radical quotient image. -/
theorem eight_actor_component (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hinner : Nat.card (A ⊓ L : Subgroup G) = 4)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ECaseComponent (T : Subgroup G) A (centralizerResidualOvergroup T z) := by
  let : IsElementaryAbelian 2 (A ⊓ L : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  have hs := inner_four_not_le_centralizerResidual_radical L T hLT hp ho hlarge hmodel
    (A ⊓ L) hinner (inf_le_left.trans hAT) inf_le_right z hz ⟨hzA, hzL⟩ hTz
  exact inner_centralizer_component_of_not_le_radical L T hLT hp ho hlarge hmodel A z
    hzL hz hTz (fun h => hs ((comap_mono inf_le_left).trans h))

/-- An actual radical intersection of order at least four completes containment. -/
theorem centralizer_le_of_radical_four (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hcard : Nat.card A = 8) (hinner : Nat.card (A ⊓ L : Subgroup G) = 4)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hfour : 4 ≤ Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z))) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let := d.elementary.1 A hA
  let K := centralizerResidualOvergroup T z
  have hc := eight_actor_component L hLT hp ho hlarge hmodel A hAT hinner hzA hzL hz hTz
  have hm : IsEMemberAt 1 (T : Subgroup G) A K :=
    ⟨⟨inferInstance, hAT, hAT.trans le_sup_right,
      le_inf (tau_le _ _) ((tau_le _ _).trans le_sup_right),
      ⟨T.subtype le_sup_right, rfl⟩, Or.inr hc⟩,
      Or.inr ⟨hc, (radical_rank_le_one_iff (hAT.trans le_sup_right) hcard).mpr hfour⟩⟩
  have hKM := d.members_le A hA hAT K hm
  exact sylow_overgroup_le_of_solvable_quotient d (centralizer ({z} : Set G)) hTz
    (solvableResidual _) (le_sup_left.trans hKM)

/-- If the rank-one kernel condition fails, the original actor maps to a four-group.
The central involution supplies the literal order-two kernel. -/
theorem quotient_actor_card_four_of_small_radical_intersection
    {T : Sylow 2 G} {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hcard : Nat.card A = 8) {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4) :
    Nat.card ((A.subgroupOf (centralizerResidualOvergroup T z)).map
      (QuotientGroup.mk' (solvableRadical (centralizerResidualOvergroup T z)))) = 4 := by
  let K := centralizerResidualOvergroup T z
  let a := A.subgroupOf K
  let R := solvableRadical K
  let w : K := ⟨z, (show (T : Subgroup G) ≤ K from le_sup_right) (hAT hzA)⟩
  have hwC : w ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (centralizerResidualOvergroup_le hTz k.property))
  let : Group.IsSolvable (center K) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hwR : w ∈ R := le_solvableRadical (center K) inferInstance inferInstance hwC
  let v : (a ⊓ R : Subgroup K) := ⟨w, hzA, hwR⟩
  have hv : orderOf v = 2 := by
    exact (orderOf_submonoid v).symm.trans ((orderOf_submonoid w).symm.trans hz)
  have hd : 2 ∣ Nat.card (a ⊓ R : Subgroup K) := hv ▸ orderOf_dvd_natCard v
  have hk : Nat.card (a ⊓ R : Subgroup K) = 2 := by
    have hp := Nat.card_pos (α := (a ⊓ R : Subgroup K))
    change Nat.card (a ⊓ R : Subgroup K) < 4 at hsmall
    omega
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map a (QuotientGroup.mk' R)
  rw [QuotientGroup.ker_mk', hk] at hprod
  have ha : Nat.card a = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hAT.trans le_sup_right)).toEquiv).trans hcard
  rw [ha] at hprod
  change Nat.card (a.map (QuotientGroup.mk' R)) = 4
  omega
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
