module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Enumeration
public import Theory.GroupTheory.PrimeRankElementary

/-!
# A sixteen-color bound for elementary subgroups of the HS Sylow subgroup

The existing enumeration identifies every element of the marked two-subgroup
with one of 512 words in the exact degree-100 ATLAS carrier. A kernel-checked
certificate puts every square-one word in a list of 88 rows. A second certificate
assigns sixteen colors so that distinct rows with the same color fail to commute
on point 1 or point 4. Thus the color map is injective on every elementary
abelian two-subgroup, whether or not it is normal.

The reproduction script in `source/` reads the existing ATLAS word data and
recomputes just these small certificates. Python supplies candidate numerals;
Lean checks every identity used by the proof.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3(2),
printed p.348 (PDF p.359), and the degree-100 ATLAS HSG1-p100B0 carrier.
-/

namespace Sporadic.LeechRelated.HS.TwoRankCertificate
open EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 10000
set_option Elab.async false

private def involutionRow (i : Fin 88) : Fin 512 :=
  ⟨(25842941754205622174836715059924846328650457192783793612765462994727942257882991832422279230160203910437340472355565670263169454074597768316661663118024266301801698942007130100672000993236629900959984286791246104667131275958126193553179136 >>> (9 * i.val)) % 512, Nat.mod_lt _ (by decide)⟩

private def involutionCode (i : Fin 512) : Fin 88 :=
  ⟨(198765408126929868674490317236996052172988681460534619078747735413054884221180445258913270544251834994529662648023022048495306392758340332137269286711805500172092137921344149472501631682220358371854391314928461908493992699106941123618553172494835752138931409039695467554295305375364216839073798911570295512109613618001793045045976097763904699864955970695309229956618596680462717356371858715869930161928171136679240508050677176910126380472027124940694190207215038960523364909055642727936562562445994925890530026389807298028660799455809387458594034466745332286560741786706444814409967126352265798450207965821843947954864521410482401452599142648408536059279805976883715381083018324148077775287628865624427605078424150595236647665070914028546385917536530231544770035634665220595323258902745720581478075177322072358407569157502755582401336749340209014338757828979819166189809897674133142245162262682708653663420878743903080300318682791630011784131559300417989123158859206202536704556853071749299310730580503400274830538065652611185897116369589989087748004995293646108315648128 >>> (7 * i.val)) % 128 % 88, Nat.mod_lt _ (by decide)⟩

private def color (i : Fin 88) : Fin 16 :=
  ⟨(8466218839486246279383390593392003616512749031736732974671106576954204060285782140492069100402946671712288 >>> (4 * i.val)) % 16, Nat.mod_lt _ (by decide)⟩

private theorem square_one_coverage : ∀ i : Fin 512,
    point i (point i 1) = 1 → point i (point i 4) = 4 →
      involutionRow (involutionCode i) = i := by
  apply allFin
  decide +kernel

private theorem same_color_separation : ∀ i j : Fin 88,
    color i = color j →
    point (involutionRow i) (point (involutionRow j) 1) =
      point (involutionRow j) (point (involutionRow i) 1) →
    point (involutionRow i) (point (involutionRow j) 4) =
      point (involutionRow j) (point (involutionRow i) 4) → i = j := by
  apply allFin₂
  decide +kernel

open Subgroup Theory.GroupTheory EvenLocalCandidates
open scoped IsMulCommutative

/-- Every elementary abelian two-subgroup of the marked HS Sylow has order at most sixteen. -/
public theorem elementary_card_le (E : Subgroup subgroup) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 16 := by
  let row (x : E) : Fin 512 := enumeration.symm x.val
  have row_spec (x : E) : element (row x) = x.val.val :=
    congrArg Subtype.val (enumeration.apply_symm_apply x.val)
  have square_point (x : E) (k : Fin 100) : point (row x) (point (row x) k) = k := by
    have hs : x.val.val ^ 2 = 1 :=
      congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian x.val x.property)
    rw [← row_spec x] at hs
    have h := congrArg (fun z : Carrier => (z : Equiv.Perm (Fin 100)) k) hs
    simpa only [pow_two, Subgroup.coe_mul, Equiv.Perm.coe_mul,
      Function.comp_apply, element_point, Subgroup.coe_one, Equiv.Perm.one_apply] using h
  have cover (x : E) : involutionRow (involutionCode (row x)) = row x :=
    square_one_coverage (row x) (square_point x 1) (square_point x 4)
  let f (x : E) : Fin 16 := color (involutionCode (row x))
  have hf : Function.Injective f := by
    intro x y hxy
    have hcomm (k : Fin 100) :
        point (row x) (point (row y) k) = point (row y) (point (row x) k) := by
      have hc : x.val.val * y.val.val = y.val.val * x.val.val :=
        congrArg (fun z : E => z.val.val) (mul_comm x y)
      rw [← row_spec x, ← row_spec y] at hc
      have h := congrArg (fun z : Carrier => (z : Equiv.Perm (Fin 100)) k) hc
      simpa only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply,
        element_point] using h
    have hc := same_color_separation (involutionCode (row x))
      (involutionCode (row y)) hxy
      (by simpa only [cover] using hcomm 1)
      (by simpa only [cover] using hcomm 4)
    have hr : row x = row y := by
      simpa only [cover] using congrArg involutionRow hc
    exact Subtype.ext (enumeration.symm.injective hr)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
end Sporadic.LeechRelated.HS.TwoRankCertificate
