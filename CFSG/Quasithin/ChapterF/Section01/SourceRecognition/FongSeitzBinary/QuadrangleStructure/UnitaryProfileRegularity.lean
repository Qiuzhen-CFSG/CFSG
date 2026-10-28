module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.CoreOrderRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitarySpecialRadical

/-!
# The unitary-five source profile gives both original kernels

The given full amalgam marking transports the original endpoint two-core
without assuming regularity. Its order therefore agrees with the order of
the actual quotient parabolic core. On the unitary quadrangle, the two
full-Borel indices determine root orders q^2 and q^3, hence the unitary
complementary section has order q^7. DGS (11.8)(f) gives this same order
for the original unitary two-core. Containment and equality of orders
identify these subgroups and establish (2B). The original elementary
linear Sylow quotient supplies regularity at the other endpoint.

Both literal core preimages are retained, for either orientation and every
positive parameter. ProfileCoordinates applies this to the actual SU3
cover and natural action. The original profile clauses, marked quotient,
split data, and rotation order four remain earlier source inputs; these
results do not assert that the source profile or a full U5 comparison has
been constructed. The profile producer is qt-dgs85-commuting-one-profile;
qt-dgs85-apartment-exchange supplies the marked quotient construction.
Source: DGS (11.5), (11.8)(a),(d),(f), pp.172,175--176; Fong--Seitz I (2B).
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open Theory.GroupTheory
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e in
/-- The original core order transports through the given endpoint marking before (2B). -/
theorem marked_core_card (i : Fin 2) :
    Nat.card ((Q.tits.standardParabolic {Q.simple i}).pCoreIn 2) =
      Nat.card ((parabolic L S i).pCoreIn 2) := by
  rw [←marked_core_map Q e i]
  have hf : Function.Injective (MarkedLocal.endpointMap Q e i) :=
    (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp (MarkedLocal.endpoint Q e i).injective
  rw [card_map_of_injective hf]
  exact Nat.card_congr (subgroupOfEquivOfLe ((parabolic L S i).pCoreIn_le 2)).toEquiv
include e in
/-- An original core of the complementary-section order gives the actual kernel containment and core preimage. -/
theorem marked_regularity_of_core_card (i : Fin 2)
    (hc : Nat.card (simpleRemainder Q split i) ≤ Nat.card ((parabolic L S i).pCoreIn 2)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      (simpleRemainder Q split i).comap (MarkedLocal.endpointMap Q e i) =
        pCore 2 (parabolic L S i) := by
  have hr := PanelKernel.remainder_le_kernel_of_core_card Q split i
    (by rw [marked_core_card Q e i]; exact hc)
  exact ⟨hr,MarkedLocal.remainder_comap_of_containment Q e split i hr⟩
include e h in
/-- The genuine unitary source profile supplies both regularity containments, including the binary branch. -/
theorem marked_unitary_profile_regularity
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (q : ℕ) (hq : 0 < q)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = q^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = q^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : Nat.card ((parabolic L S j).pCoreIn 2) = q^7) :
    ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q e k) =
        pCore 2 (parabolic L S k) := by
  have hi := regularity_of_sylow_core Q e h split i hQi
  have hj := marked_regularity_of_core_card Q e split j (by
    rw [(marked_unitary_root_orders Q e h split hm i j hij q hq hindexi hindexj).2.2.2.1,hQj])
  intro k
  by_cases hk : k = i
  · subst k; exact hi
  · have hk' : k = j := by omega
    subst k; exact hj
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
