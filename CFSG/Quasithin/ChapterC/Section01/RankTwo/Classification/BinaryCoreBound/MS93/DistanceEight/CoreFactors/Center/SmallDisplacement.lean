module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.FirstHatSmallDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.DerivedFirst
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Upper
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.SmallCommutatorMiddle
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Small central displacement in the large binary core

A subgroup of the actual distance-eight core whose commutators with the core
lie in a locally central subgroup of order at most two centralizes the core.
This is the local no-new-center statement used for the original first fixed
line in Aschbacher--Smith 15.3.25.

Take the full commutator preimage of the small layer. It is locally normalized
and centralizes the core's derived subgroup by the three-subgroups lemma.
The derived first-hat bound puts it in the second hat. The marked doubled-dual
pairing then puts it in the first hat, and the full commutator rows force it
into Z, which centralizes the core.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4), printed pp.898--899;
Aschbacher--Smith 15.3.31, printed p.1132.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- A core subgroup with locally central displacement of order at most two
centralizes the actual core. -/
theorem small_core_displacement_centralizes
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (A N : Subgroup (FreeAmalgam R))
    (hAK : A ≤ core R (alpha R)) (hNK : N ≤ core R (alpha R))
    (hNP : N ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)))
    (hcard : Nat.card N ≤ 2) (hdisp : ⁅A,core R (alpha R)⁆ ≤ N) :
    A ≤ centralizer (core R (alpha R) : Set (FreeAmalgam R)) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  have hfirst := first_le_core_derived_sup_Z common earlier p
  let K := core R (alpha R)
  let P := stabilizer R (alpha R)
  let D := commutatorPreimage K K N
  have hKP : K ≤ P := fun _ hx => (DistanceTwo.core_le_Q _ hx).1
  have hPN : P ≤ normalizer N :=
    (le_centralizer_iff.mpr hNP).trans (Subgroup.centralizer_le_normalizer _)
  have hDK : D ≤ K := commutatorPreimage_le K K N
  have hDN : ⁅D,K⁆ ≤ N := commutator_commutatorPreimage_le K K N (hKP.trans hPN)
  have hPD : P ≤ normalizer D := commutatorPreimage_normalized K K N P
    (hKP.trans hPN) (DistanceTwo.core_normalized _) (DistanceTwo.core_normalized _) hPN
  have hZK := Quotients.FirstDirect.Z_centralizes_core common earlier
  have hNZ : ⁅N,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hNP.trans (centralizer_le hKP))
  have hrotate : ⁅⁅D,K⁆,K⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hDN le_rfl).trans_eq hNZ)
  have hderived : ⁅⁅K,K⁆,D⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by rwa [commutator_comm K D]) hrotate
  have hDfirst : D ≤ centralizer (hatV R (alpha R) (p.walk.getVert 6) : Set _) := by
    apply le_centralizer_iff.mpr
    apply hfirst.trans
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hderived)
      (hZK.trans (centralizer_le hDK))
  have hDsecond : D ≤ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
    have h := le_inf hDK hDfirst
    rw [first_centralizer_eq_second common earlier p] at h
    exact h.trans inf_le_right
  have hsecondComm : ⁅D,hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≤ N := by
    apply (commutator_mono le_rfl (second_le_core_sup_Z common earlier p)).trans
    rw [← commutator_eq_of_centralizing_sup (sup_comm (Z R (alpha R)) K)
      (hZK.trans (centralizer_le hDK)) (hKP.trans hPD)]
    exact hDN
  let : Finite K := DistanceTwo.finite_core (alpha R)
  let : Finite N := Finite.of_injective (inclusion hNK) (inclusion_injective hNK)
  have hDhat := second_small_commutator_le_first common earlier p hDsecond hPD ((card_le_of_le hsecondComm).trans hcard)
  have hDZ := first_hat_small_core_displacement_le_Z common earlier p D N hDhat hNK hcard hDN
  exact (le_commutatorPreimage hAK hdisp).trans (hDZ.trans hZK)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
