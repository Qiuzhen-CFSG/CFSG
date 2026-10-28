module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Contracts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction
public import Theory.GroupTheory.PResidual.PrimeToAction

/-!
# The residual-to-centralizer argument for 11.2.2(2)

The local residual condition kills the two-part of the literal automizer
image. A nontrivial remaining image has an odd prime-order element; its
model fixed-codimension estimate contradicts the small corank of U.
Consequently C_M(U)=C_M(V). The proved maximal-action theorem E.6.11
then forces any escaping centralizer to give r=1, contrary to the lower
bound. Both residuals below are O^{2′}, computed in the indicated groups.

The natural fixed-codimension calculation, E.6.1 setup and r lower bound
remain explicit source obligations. This is their conditional consumer,
not an unconditional assertion of 11.2.2.
Source: Aschbacher--Smith, printed pp.767--768, using E.6.12, p.250.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem odd_image_of_residual {M U : Subgroup G}
    (hCN : M ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hres : oddCentralizerCondition M V U) :
    Odd (Nat.card (inducedAutomizer V (M ⊓ centralizer (U : Set G)))) := by
  let C := M ⊓ centralizer (U : Set G)
  let f : C →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hCN)
  have hf : f.range = inducedAutomizer V C := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨inclusion hCN x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hk : primeToResidual 2 C ≤ f.ker := by
    intro x hx
    have hc := (hres (mem_map_of_mem C.subtype hx)).2
    have hn : inclusion hCN x ∈ V.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hc
    apply Subtype.ext
    exact hn
  have hcard := coprime_card_range_of_primeToResidual_le_ker 2 f hk
  rw [hf] at hcard
  exact Nat.coprime_two_left.mp hcard

/-- The model's odd prime estimates turn the residual condition into equality
of the full local centralizers; no splitting of their kernel is used. -/
theorem localCentralizer_eq_of_residual {c : Coordinates D S.field}
    (hmodel : FixedCodimensions D S c)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    {U : Subgroup G} (hUV : U ≤ V)
    (hk : subgroupCorank V U < 2 * naturalParameter D S c)
    (hres : oddCentralizerCondition (normalizer (L : Set G)) V U) :
    normalizer (L : Set G) ⊓ centralizer (U : Set G) =
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  let := D.elementary
  have hU : U ≠ ⊥ := by
    rintro rfl
    exact (not_lt_of_ge hmodel.dimension.le) hk
  let C := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  have hCN : C ≤ normalizer (V : Set G) := hE.localCentralizer_le_normalizer hU hUV
  let I := inducedAutomizer V C
  have hodd : Odd (Nat.card I) := odd_image_of_residual hCN hres
  have hdim : fixedCodim (automizerRepresentation V) I ≤ subgroupCorank V U := by
    rw [fixedCodim_inducedAutomizer V C hCN]
    exact subgroupCorank_antitone (le_inf hUV (le_centralizer_iff.mpr inf_le_right))
  have hI : I = ⊥ := by
    by_contra hn
    have hc : Nat.card I ≠ 1 := (I.one_lt_card_iff_ne_bot.mpr hn).ne'
    let p := (Nat.card I).minFac
    have hp : p.Prime := Nat.minFac_prime hc
    have hd : p ∣ Nat.card I := Nat.minFac_dvd _
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left (by
      intro he
      rw [he] at hd
      exact hodd.not_two_dvd_nat hd)
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := I) p hd
    have ha' : orderOf (a : Automizer V) = p := (Subgroup.orderOf_coe a).trans ha
    have hm := (hmodel.odd_prime_lower p hp hpodd a ha').trans
      ((fixedCodim_mono (automizerRepresentation V) (zpowers_le.mpr a.property)).trans hdim)
    exact (not_lt_of_ge hm) hk
  have hC := (inducedAutomizer_eq_bot_iff hCN).mp hI
  exact le_antisymm (le_inf inf_le_left hC)
    (inf_le_inf_left _ (Subgroup.centralizer_le hUV))

/-- The literal statement of 11.2.2(2), conditional only on the preceding
model calculation, E.6.1 and the independently proved rank lower bound. -/
theorem centralizer_control {c : Coordinates D S.field}
    (hmodel : FixedCodimensions D S c)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V)
    (hk : subgroupCorank V U < 2 * naturalParameter D S c)
    (hres : oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  have hU : U ≠ ⊥ := by
    rintro rfl
    exact (not_lt_of_ge hmodel.dimension.le) hk
  have heq := localCentralizer_eq_of_residual D S hmodel hE hUV hk hres
  have hC : centralizer (U : Set G) ≤ normalizer (L : Set G) := by
    by_contra hn
    obtain ⟨W, _, _, _, _, hW⟩ := hE.hyperplane_escape_of_maximal_action
      (fun W hW hmax hn => maximal_escape_action_knownSimple hE hW hmax hn)
      hU hUV heq hn
    have hm : (1 : ℕ∞) < naturalParameter D S c := by
      exact_mod_cast naturalParameter_gt_one D S c
    rw [hW] at hr
    exact (not_le_of_gt hm) hr
  have hCM : normalizer (L : Set G) ⊓ centralizer (U : Set G) =
      centralizer (U : Set G) := inf_eq_right.mpr hC
  unfold oddCentralizerCondition at hres
  rw [hCM] at hres
  exact ⟨hC, hres⟩

/-- A specialized alternative to invoking the general E.6.3 theorem.
For these fixed-codimension estimates, every failure of r≥m enlarges to
an escaping hyperplane. Thus a model proof controlling hyperplanes suffices,
also in the nonsplit case. No Held-cover premise is used in this reduction. -/
theorem lower_bound_of_hyperplanes {c : Coordinates D S.field}
    (hmodel : FixedCodimensions D S c)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hhyper : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    (naturalParameter D S c : ℕ∞) ≤ globalR V := by
  let := D.elementary
  by_contra hn
  have hr : globalR V < (naturalParameter D S c : ℕ∞) := lt_of_not_ge hn
  have hm := localM_of_fixedCodimensions D S hmodel
  have hrm : globalR V < (localM V : ℕ∞) := by rwa [hm]
  obtain ⟨U, ⟨hUV, hU, he, hres⟩, hcor⟩ := hE.exists_minimal_obstruction hrm
  have hsmall : subgroupCorank V U < naturalParameter D S c := by
    apply ENat.natCast_lt_natCast.mp
    rwa [hcor]
  have hk : subgroupCorank V U < 2 * naturalParameter D S c := by omega
  have hC := localCentralizer_eq_of_residual D S hmodel hE hUV hk hres
  obtain ⟨W, _, hWV, hWcor, hWout, _⟩ := hE.hyperplane_escape_of_maximal_action
    (fun W hW hmax hn => maximal_escape_action_knownSimple hE hW hmax hn)
    hU hUV hC he
  exact hWout (hhyper W hWV hWcor)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
