module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearMS
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredChief
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.DoubledExclusion

/-!
# The covered linear-three row has only two cubic layers

The point-radical MS pair has a natural commutator core: the doubled case
would put its Thompson subgroup in the two-core, contradicting MS3. On every
embedded subgroup N of K, cubic movement in O₂(N) has at most one layer in
the ambient two-core and one in its SL₃(2) image. Both layers use the same
literal inclusion N → K Baum(R).

For the original covered L₀, this contradicts the three-layer lower bound
on the same intrinsic O₂(L₀). Thus L₀ cannot lie in the selected linear-three
component. The source residual-placement argument giving that containment,
and the remaining 13.4.10--17 assembly, stay with the nonsolvable owner.
Earlier source inputs and LargeDistanceInput retain their independent producers.

Source: Aschbacher--Smith 13.4.10(2), printed p.908; C.1.37, pp.141--143.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource ChapterC.NaturalPointControl
open NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
universe u

private theorem ambient_embedded_core_length
    {G : Type u} [Group G] [Finite G] (K X : Subgroup G) (hKX : K ≤ X)
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (a : NaturalAction U) (hres : pResidual 2 X = K.subgroupOf X)
    (hi : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ)
    (N : Subgroup G) (hNK : N ≤ K) (A : Subgroup G)
    (hA : IsPGroup 3 A) (hAN : A ≤ N) :
    conjugationCubicLength A (N.pCoreIn 2) ≤ 2 := by
  let fi : N →* X := inclusion (hNK.trans hKX)
  let f : N →* a.J := fi.codRestrict a.J (fun n =>
    (show pResidual 2 X ≤ a.J from le_sup_left)
      (show fi n ∈ pResidual 2 X from hres.symm ▸ hNK n.property))
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun x : a.J => x.val.val) hxy)
  have hfK : f.range ≤ a.LJ := by
    rintro x ⟨n,rfl⟩
    change fi n ∈ pResidual 2 X
    rw [hres]
    exact hNK n.property
  obtain ⟨e,hm⟩ := a.natural_core_of_msInput hi
  let : IsElementaryAbelian 2 (U.subgroupOf a.J) := IsElementaryAbelian.subgroupOf a.module_le_J
  have hb := a.inMSGroup.embedded_core_length_le_two hi e hm f hf hfK
    (A.subgroupOf N) hA.comap_subtype
  have he := length_map_injective N.subtype N.subtype_injective (A.subgroupOf N) (pCore 2 N)
  rw [map_subgroupOf_eq_of_le hAN] at he
  exact he ▸ hb

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The covered row bounds cubic movement on the intrinsic core of every
actual subgroup of K, using its constructed Baumann MS pair. -/
theorem covered_linear_embedded_core_length_le_two
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (N : Subgroup G) (hNK : N ≤ K) (A : Subgroup G)
    (hA : IsPGroup 3 A) (hAN : A ≤ N) :
    conjugationCubicLength A (N.pCoreIn 2) ≤ 2 := by
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨hn,hel,a,_,hres,⟨hi⟩⟩ := covered_linear_component_ms hl h₀ h structural modules
    D m h1332 fixed hindex hc z hzT hzL hKz hHN hKM hfK eK
  let := hn
  let := hel
  exact ambient_embedded_core_length K X le_sup_left (U.subgroupOf X)
    a hres hi N hNK A hA hAN

/-- The three-layer lower bound and two-layer upper bound refer to the same
cubic and the same intrinsic O₂(L₀), excluding L₀ ≤ K. -/
theorem covered_zero_not_le_linear_component
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ¬ zero L ≤ K := by
  intro hZK
  have hq := Solvable.covered_zero_core_card hc
  have hd : 3 ∣ Nat.card (zero L) := by
    rw [←hq,←index_eq_card]
    exact (pCore 2 (zero L)).index_dvd_card
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := zero L) 3 hd
  let A := zpowers (a : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,(zero L).orderOf_coe a,ha]
  have hAZ : A ≤ zero L := zpowers_le.mpr a.property
  have hlo := covered_zero_cubic_length_ge_three h.toHypothesis1221 hc A hA hAZ
  have hup := covered_linear_embedded_core_length_le_two hl h₀ h structural modules
    D m h1332 fixed hindex hc z hzT hzL hKz hHN hKM hfK eK
    (zero L) hZK A (IsPGroup.of_card (n := 1) (by simpa using hA)) hAZ
  omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
