module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound

/-!
# The actual order-32 closure in the L₃(2) branch

For the selected counterexample, the earlier source implications establish
that the nonabelian closure U is extraspecial with center the marked point.
When |U| = 32, its original elementary seed V has order eight and contains
that center. The intrinsic extraspecial theorem therefore gives two commuting
quaternion subgroups generating U. The extraspecial pairing also gives
C_U(V) = V. For the omitted-point conjugator, the source Frattini calculation
makes the intersection E elementary, whence E = V.

These statements use the literal closure, seed and conjugate intersection.
They establish the quaternion and intersection conclusions of 14.4.2 and
14.4.4(2), without assuming the later nonsplit block or fusion conclusions.
The ambient normalizer and fusion arguments of 14.4.4–5 remain necessary.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, printed
pp.1006–1008; the earlier naturality input is `Earlier1332CaseOne` and the
structural/escape inputs are `Structural1222` and `Theorem12213`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem seed_card (F : InvariantFlag T V 3) : Nat.card V = 8 := by
  simpa [F.last] using F.card 3 (by decide)

omit [Finite G] in
private theorem center_le_seed (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    center F.U ≤ V.subgroupOf F.U := by
  rw [center_point F hZ]
  exact subgroupOf_mono _ (F.le_seed 1)

/-- The original order-32 closure admits embedded commuting quaternion factors. -/
theorem source_quaternion (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (QuaternionCentralProductData F.U) := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let : IsElementaryAbelian 2 (V.subgroupOf F.U) := IsElementaryAbelian.subgroupOf hVU
  let : (V.subgroupOf F.U).Normal := Normal.of_commutator_le F.U (by
    rw [IsExtraspecial.commutator_eq_center (p := 2)]
    exact center_le_seed F hZ)
  have hV : Nat.card (V.subgroupOf F.U) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans (seed_card F)
  obtain ⟨B, C, hB, hC, hspan, hinter, hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary hcard
      (V.subgroupOf F.U) hV (center_le_seed F hZ)
  exact ⟨⟨B, C, hB, hC, hinter, hcomm, hspan⟩⟩

/-- The original seed is its own centralizer inside the extraspecial closure. -/
theorem source_seed_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    F.U ⊓ centralizer (V : Set G) = V := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let : IsElementaryAbelian 2 (V.subgroupOf F.U) := IsElementaryAbelian.subgroupOf hVU
  have hV : Nat.card (V.subgroupOf F.U) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans (seed_card F)
  have hc := extraspecial_two_centralizer_eq_of_card_sq (V.subgroupOf F.U)
    (center_le_seed F hZ) (by rw [hV, hcard]; decide)
  apply le_antisymm
  · intro x hx
    have hm : (⟨x, hx.1⟩ : F.U) ∈ centralizer (V.subgroupOf F.U : Set F.U) := by
      intro v hv
      exact Subtype.ext (hx.2 v hv)
    rw [hc] at hm
    exact hm
  · exact le_inf hVU (le_centralizer V)

omit [Finite G] in
/-- The point normalizer is the ambient centralizer of the actual center of U. -/
theorem point_centralizer (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    F.H = centralizer (F.ZU : Set G) := by
  rw [hZ]
  exact le_antisymm (normalizer_le_centralizer_of_card_two _
    (by simpa using F.card 1 (by decide))) (Subgroup.centralizer_le_normalizer _)

/-- Source 14.4.4(2): the literal omitted-point intersection equals the seed. -/
theorem source_intersection_eq_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  let := chosen.elementary
  have hgV := F.P_le_seed_normalizer L chosen.normalizes hgP
  obtain ⟨htwo, hphi, hc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have hpU : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi, map_subgroupOf_eq_of_le hpU]
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g htwo hPhi
    (disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) hc g hgV hgH))
  have hVE := F.seed_le_E_of_normalizes g hgV
  apply le_antisymm _ hVE
  exact (show F.E g ≤ F.U ⊓ centralizer (V : Set G) from
    le_inf (inf_le_left.trans inf_le_left)
      ((le_centralizer (F.E g)).trans (centralizer_le hVE))).trans_eq
    (source_seed_centralizer d earlier hq chosen structural alternatives F hne hZ hcard)

/-- The original quotient U/Z(U) has order sixteen. -/
theorem source_quotient_card (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nat.card F.Uhat = 16 := by
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen structural alternatives F hne hZ hcard
  exact q.quotient_card

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
