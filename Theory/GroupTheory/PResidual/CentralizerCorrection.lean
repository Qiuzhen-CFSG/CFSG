module
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Central corrections detected by a binary fixed line

For a two-perfect actor L on a two-group N, the displacement of
C_N([N,L]) lies in [Z([N,L]),L]. When that layer is elementary, averaging
over the odd number of component Sylow cosets corrects each Sylow-fixed
element to an L-central element. If the correction space has at most two
elements, any subgroup moved by L detects the same centralizer as the
whole corrected subgroup.

The actual natural-layer application is the omega-center comparison in
Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.
LinearThree.NaturalCenter. The argument supplies the centralizer comparison
used in Aschbacher--Smith, preliminary 15.2.23, printed pp.1115--1116;
refs/quasithin.pdf. The elementary averaging lemma is reused unchanged.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A binary fixed line detected by W also detects every corrected point. -/
theorem centralizer_eq_of_binary_fixed_corrections
    (L U P Z W : Subgroup G) (hWZ : W ≤ Z)
    (hmove : ¬ W ≤ centralizer (L : Set G))
    (hcard : Nat.card (U ⊓ centralizer (P : Set G) : Subgroup G) ≤ 2)
    (hsplit : ∀ z ∈ Z, ∃ u ∈ U ⊓ centralizer (P : Set G),
      u⁻¹ * z ∈ centralizer (L : Set G)) :
    L ⊓ centralizer (W : Set G) = L ⊓ centralizer (Z : Set G) := by
  classical
  obtain ⟨w,hw,hwc⟩ : ∃ w ∈ W, w ∉ centralizer (L : Set G) := by
    by_contra! hh
    exact hmove hh
  obtain ⟨u,hu,huc⟩ := hsplit w (hWZ hw)
  have hu1 : u ≠ 1 := by
    intro he
    apply hwc
    simpa only [he, inv_one, one_mul] using huc
  let F := U ⊓ centralizer (P : Set G)
  have hn : Nontrivial F := ⟨⟨⟨u,hu⟩,1,fun h => hu1 (congrArg Subtype.val h)⟩⟩
  let := hn
  have hc : Nat.card F = 2 := le_antisymm hcard
    (Nat.succ_le_of_lt (Finite.one_lt_card (α := F)))
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hWZ))
  rintro l ⟨hl,hlW⟩
  refine ⟨hl,?_⟩
  have hlu : l * u = u * l := by
    have h1 := hlW w hw
    have h2 := huc l hl
    have hh : l * u⁻¹ = u⁻¹ * l := by
      apply mul_right_cancel (b := w)
      simpa only [mul_assoc, ← h1] using h2
    exact (Commute.inv_right_iff.mp hh).eq
  intro z hz
  obtain ⟨v,hv,hvc⟩ := hsplit z hz
  by_cases hv1 : v = 1
  · simpa only [hv1, inv_one, one_mul] using (hvc l hl).symm
  have he : v = u := congrArg Subtype.val
    (((Nat.card_eq_two_iff' (1 : F)).mp hc).unique
      (show (⟨v,hv⟩ : F) ≠ 1 from fun h => hv1 (congrArg Subtype.val h))
      (show (⟨u,hu⟩ : F) ≠ 1 from fun h => hu1 (congrArg Subtype.val h)))
  subst v
  have hh := hvc l hl
  have hinv := (Commute.inv_right hlu).eq
  symm
  calc
    l * z = u * (l * (u⁻¹ * z)) := by rw [← mul_assoc l, hinv]; group
    _ = u * ((u⁻¹ * z) * l) := by rw [hh]
    _ = z * l := by group

/-- A p-perfect actor moves the centralizer of its core commutator through
that commutator's central layer. -/
theorem core_centralizer_displacement_le_center_commutator
    (L N : Subgroup G) (hL : IsPPerfect 2 L) (hN : IsPGroup 2 N)
    (hLN : L ≤ normalizer (N : Set G)) :
    ⁅N ⊓ centralizer ((⁅N,L⁆ : Subgroup G) : Set G),L⁆ ≤
      ⁅(center (⁅N,L⁆ : Subgroup G)).map (⁅N,L⁆ : Subgroup G).subtype,L⁆ := by
  let Q := ⁅N,L⁆
  let B := N ⊓ centralizer (Q : Set G)
  have hLC : L ≤ normalizer (centralizer (Q : Set G) : Set G) :=
    (normalizer_commutator_ge_right N L).trans (normalizer_le_normalizer_centralizer Q)
  have hLB : L ≤ normalizer (B : Set G) :=
    (le_inf hLN hLC).trans inf_normalizer_le_normalizer_inf
  have hBZ : ⁅B,L⁆ ≤ (center Q).map Q.subtype := by
    have hBQ : ⁅B,L⁆ ≤ Q := commutator_mono inf_le_left le_rfl
    have hBC : ⁅B,L⁆ ≤ centralizer (Q : Set G) :=
      (commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hLC)
    intro x hx
    exact ⟨⟨x,hBQ hx⟩,mem_center_iff.mpr (fun q => Subtype.ext (hBC hx q q.property)),rfl⟩
  rw [← commutator_isPPerfect_idempotent L B hL (hN.to_le inf_le_left) hLB]
  exact commutator_mono hBZ le_rfl

/-- Central displacement can be corrected in an elementary layer; the correction
is fixed by the actual component Sylow subgroup. -/
theorem fixed_correction_of_center_commutator
    (L N U : Subgroup G) [IsMulCommutative U]
    (hL : IsPPerfect 2 L) (hN : IsPGroup 2 N)
    (hLN : L ≤ normalizer (N : Set G))
    (hLU : L ≤ normalizer (U : Set G)) (he : ∀ u ∈ U, u ^ 2 = 1)
    (hZU : ⁅(center (⁅N,L⁆ : Subgroup G)).map (⁅N,L⁆ : Subgroup G).subtype,L⁆ ≤ U)
    (P : Sylow 2 L) (z : G) (hzN : z ∈ N)
    (hzQ : z ∈ centralizer ((⁅N,L⁆ : Subgroup G) : Set G))
    (hzP : z ∈ centralizer ((P : Subgroup L).map L.subtype : Set G)) :
    ∃ u ∈ U ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G),
      u⁻¹ * z ∈ centralizer (L : Set G) := by
  have hcomm := (core_centralizer_displacement_le_center_commutator L N hL hN hLN).trans hZU
  obtain ⟨v,hv,hvc⟩ := fixed_coset_of_sylow L U hLU he P z
    (fun l hl => by
      rw [commutator_comm] at hcomm
      exact commutator_le.mp hcomm l hl z ⟨hzN,hzQ⟩)
    (fun l hl => hzP l (mem_map_of_mem L.subtype hl))
  have hvP : v ∈ centralizer ((P : Subgroup L).map L.subtype : Set G) := by
    have hh := (centralizer ((P : Subgroup L).map L.subtype : Set G)).mul_mem
      (centralizer_le (map_subtype_le _) hvc) ((centralizer _).inv_mem hzP)
    simpa only [mul_inv_cancel_right] using hh
  refine ⟨v⁻¹,⟨U.inv_mem hv,(centralizer _).inv_mem hvP⟩,?_⟩
  simpa only [inv_inv] using hvc

end Subgroup
