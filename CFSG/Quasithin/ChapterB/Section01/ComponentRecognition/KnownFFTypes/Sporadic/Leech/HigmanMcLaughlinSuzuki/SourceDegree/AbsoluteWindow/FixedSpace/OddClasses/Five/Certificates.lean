module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Five.Certificates
import all CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Five.Certificates
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup

/-!
# Three-class coverage of the certified HS five-subgroup

The existing square-fusion actors cover the nonidentity normal forms by four
families. One further word in the original ATLAS generators joins the two
families represented by x and y. A finite table records a conjugator of at
most three certified actors and a power of two for each of the 124 forms.
The square-fusion theorem then removes the power and gives three classes.
Every identity is checked in the kernel on the literal degree-100 carrier.

The internal imports reuse the existing private permutation tables and actors;
they introduce no new public dependencies on those implementation details.
Source: ATLAS HSG1-p100B0, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
Discovery scripts and reproducible encodings are retained in `source/`.
-/

public section
namespace Sporadic.LeechRelated.HS.OddClassBound.Five
open Theory.GroupTheory OrderCertificate
set_option maxRecDepth 100000

/-- Three actual five-subgroup elements covering the nonidentity forms. -/
@[expose] def representative (i : Fin 3) : Carrier :=
  FiveFusion.normalForm (if i = 0 then 1 else if i = 1 then 7 else 25)

private def bridgeMap (i : Fin 100) : Fin 100 :=
  ⟨(810522175690714346154530723586266488359817672283568363947020934935327697639037371904713639613289308295727290744568550837884932924726436662538571526558205233820085288179131313954220191457695033540705060304488329 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private def bridgeInvMap (i : Fin 100) : Fin 100 :=
  ⟨(1480242689525571711674747430097625398385971455433941518510377503065453730136896741235114687175957324589053996825300275767039575276937426282875239832162629829703081703616879741718184113450265236653585210972479372 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩
private theorem bridgeLeft : ∀ i, bridgeInvMap (bridgeMap i) = i := by
  apply allFin
  decide +kernel
private def bridgePerm : Equiv.Perm (Fin 100) :=
  tablePerm bridgeMap bridgeInvMap bridgeLeft (rightInverse_of_leftInverse_fin bridgeLeft)
private def bridgeWord : Carrier := evalWord FiveFusion.letter [1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0]
private theorem bridgePerm_eq : bridgePerm = inclusion bridgeWord := by
  apply Equiv.ext
  apply allFin
  decide +kernel
private def bridge : Carrier := ⟨bridgePerm, bridgePerm_eq.symm ▸ bridgeWord.property⟩

private def actor (i : Fin 14) : Carrier :=
  if i = 0 then 1 else if i.val ≤ 10 then FiveFusion.actor ⟨(i.val - 1) % 10,
    Nat.mod_lt _ (by decide)⟩
  else if i = 11 then FiveSubgroup.x else if i = 12 then FiveSubgroup.y else bridge

private def row (t : Fin 125) : ℕ :=
  (96565192951228793489774564548539856317634486847257036641889152439984604589185974878792681300054829162371815374501465921143989584754076011099105493641705953425762575328590690126095430050008836017704775664242017459154419357143452778793353943249459499309018163975653340092719716603557563777871331050385935685338162152287660539624462802702205186695877619435127516791719549676126960301419791066073184102770093994810724246856094442327271510761739873281284073327440609151918199275267400426681236601200325293126188695119353610222251082115273666986244435522347195410641097144342517999897362402348581317915967488 >>> (16 * t.val)) % 65536
private def family (t : Fin 125) : Fin 3 :=
  ⟨row t % 4 % 3, Nat.mod_lt _ (by decide)⟩
private def exponent (t : Fin 125) : ℕ := (row t >>> 2) % 4
private def digit (t : Fin 125) (j : ℕ) : Fin 14 :=
  ⟨(row t >>> (4 + 4 * j)) % 16 % 14, Nat.mod_lt _ (by decide)⟩
private def conjugator (t : Fin 125) : Carrier :=
  actor (digit t 0) * actor (digit t 1) * actor (digit t 2)

private theorem conjugates (t : Fin 125) (ht : t ≠ 0) :
    conjugator t * representative (family t) ^ (2 ^ exponent t) * (conjugator t)⁻¹ =
      FiveFusion.normalForm t := by
  have h : ∀ s : Fin 125, s ≠ 0 → ∀ i : Fin 100,
      inclusion (conjugator s * representative (family s) ^ (2 ^ exponent s) *
        (conjugator s)⁻¹) i = inclusion (FiveFusion.normalForm s) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t ht))

private theorem square_iterate {G : Type*} [Group G] (r : G)
    (h : IsConj r (r ^ 2)) (n : ℕ) : IsConj r (r ^ (2 ^ n)) := by
  induction n with
  | zero => simpa using IsConj.refl r
  | succ n ih =>
    simpa only [← pow_mul, ← pow_succ'] using ih.trans (h.pow (2 ^ n))

/-- All 124 nonidentity normal forms are conjugate to one of the three
marked representatives, using the already checked square fusion. -/
theorem normalForm_conjugate (t : Fin 125) (ht : t ≠ 0) :
    ∃ i : Fin 3, IsConj (FiveFusion.normalForm t) (representative i) := by
  refine ⟨family t, ?_⟩
  have hc : IsConj (representative (family t) ^ (2 ^ exponent t))
      (FiveFusion.normalForm t) := isConj_iff.mpr ⟨conjugator t, conjugates t ht⟩
  exact hc.symm.trans (square_iterate _ (FiveFusion.normalForm_square _) _).symm

end Sporadic.LeechRelated.HS.OddClassBound.Five
