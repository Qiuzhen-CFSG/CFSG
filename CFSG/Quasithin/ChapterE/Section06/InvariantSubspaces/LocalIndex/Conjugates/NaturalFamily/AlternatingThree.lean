module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily.FixedSpaces
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Covers

/-!
# Full fixed spaces for the alternating-three block

The intrinsic covering theorem proves `C_U(L) = 1` using the actual
commutator-generated action and Maschke's theorem for the odd-order actor A₃.
The genuine binary A₃ model then gives `|U| = 4`. For an element `v` of `Uˣ` acting nontrivially
on U, a nonidentity commutator lies in both modules, since each normalizes
the other. As `Uˣ` is abelian, that commutator is fixed by v. Its subgroup
therefore exhausts the proper fixed subgroup in the four-element U.
Thus `C_U(v) ≤ Uˣ`.

Using the authorized factorizations `Q = UD` and `S = UˣQ`, the
Frattini-zero hypothesis makes Q and `UˣD` elementary abelian. Cancelling
the Q-factor of an actor and the D-factor of a fixed element now gives
`C_Q(s) = Q ∩ UˣD` for every `s ∈ S − Q`.

The final assembly supplies the proved intrinsic assertion `C_U(L) = 1`
to the conditional adapter. Thus the fixed-space identity concerns the full
commutator layer, not just `U/C_U(L)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.13(c),
printed pp.124–125; proof of C.5.6, printed pp.156–157 (PDF pp.167–168),
and C.5.7, printed p.160 (PDF p.171).
-/

public section

open Subgroup
open scoped commutatorElement Pointwise

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily

universe u
variable {G : Type u} [Group G]

private theorem commute_of_mem {P : Subgroup G} [IsMulCommutative P]
    {a b : G} (ha : a ∈ P) (hb : b ∈ P) : Commute a b :=
  congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : P) (⟨b, hb⟩ : P))

variable [Finite G]

private theorem fixed_four_le {V W : Subgroup G} [IsMulCommutative W]
    (hcard : Nat.card V = 4)
    (hVW : V ≤ normalizer (W : Set G)) (hWV : W ≤ normalizer (V : Set G))
    {w : G} (hw : w ∈ W) (hmove : w ∉ centralizer (V : Set G)) :
    V ⊓ centralizer ({w} : Set G) ≤ W := by
  let C := V ⊓ centralizer ({w} : Set G)
  have hne : C ≠ V := by
    intro he
    apply hmove
    intro v hv
    have hc : v ∈ centralizer ({w} : Set G) := (he.symm ▸ hv : v ∈ C).2
    exact mem_centralizer_singleton_iff.mp hc
  have hdiv : Nat.card C ∣ 2 ^ 2 := by
    simpa [hcard] using (card_dvd_of_le (show C ≤ V from inf_le_left))
  have hC : Nat.card C ≤ 2 := by
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    interval_cases i
    · omega
    · omega
    · exact False.elim (hne (eq_of_le_of_card_ge inf_le_left (by omega)))
  obtain ⟨v, hv, hcomm⟩ : ∃ v ∈ V, ¬ v * w = w * v := by
    by_contra! hAll
    exact hmove (fun v hv => hAll v hv)
  let c := ⁅v, w⁆
  have hcne : c ≠ 1 := fun he => hcomm (commutatorElement_eq_one_iff_mul_comm.mp he)
  have hcV : c ∈ V := le_normalizer_iff_commutator_le_left.mp hWV
    (commutator_mem_commutator hv hw)
  have hcW : c ∈ W := le_normalizer_iff_commutator_le_right.mp hVW
    (commutator_mem_commutator hv hw)
  have hcC : c ∈ C := ⟨hcV, mem_centralizer_singleton_iff.mpr
    (commute_of_mem hcW hw).eq⟩
  have hnontriv : C ⊓ W ≠ ⊥ := by
    intro he
    exact hcne (show c ∈ (⊥ : Subgroup G) from he ▸ ⟨hcC, hcW⟩)
  have hbound := (C ⊓ W).one_lt_card_iff_ne_bot.mpr hnontriv
  have he : C ⊓ W = C := eq_of_le_of_card_ge inf_le_left (by omega)
  change C ≤ W
  rw [← he]
  exact inf_le_right

/-- The four-element full module forces the fixed-space identity. Relative
normality of both modules puts each nontrivial action commutator in their
intersection, and this commutator generates the fixed line. -/
theorem fixedSpaceCalculation_of_card_four
    {K : GroupClass.{u}} {A H R L : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hx : x ∈ A) (hp : Factorization R L x) (hf : F R L = ⊥)
    (hcard : Nat.card (U L) = 4) : FixedSpaceCalculation R L x := by
  let V := (U L).map (MulAut.conj x).toMonoidHom
  let E := opposite R L x
  have hQelem := (elementary_candidates_of_frattini_eq_bot h hb hp hf).1
  have hEelem := (elementary_candidates_of_frattini_eq_bot h hb hp hf).2
  let : IsElementaryAbelian 2 (Q R L) := hQelem
  let : IsElementaryAbelian 2 E := hEelem
  let : IsElementaryAbelian 2 (U L) := elementary_U h
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hVS : V ≤ S R := le_sup_left.trans hp.span.ge
  have hVQ : V ≤ normalizer (Q R L : Set G) := hVS.trans (S_normalizes_Q R L)
  have hUnV : U L ≤ normalizer (V : Set G) :=
    (hb.module_le.trans inf_le_left).trans (Factorizations.R_normalizes_conjugate h hx)
  have hVnU : V ≤ normalizer (U L : Set G) :=
    (hVS.trans inf_le_left).trans (Factorizations.R_normalizes_U h)
  have hDQ : D R L ≤ Q R L := hp.core ▸ le_sup_right
  have hDCU : D R L ≤ centralizer (U L : Set G) :=
    hDQ.trans (hb.core_eq ▸ inf_le_right)
  have hUD : U L ≤ normalizer (D R L : Set G) :=
    (le_centralizer_iff.mp hDCU).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨?_⟩
  intro s hs hsq
  have hsm : s ∈ (V : Set G) * (Q R L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right V (Q R L) hVQ]
    exact hp.span ▸ hs
  obtain ⟨v, hv, q, hq, hvq⟩ := hsm
  have hvmove : v ∉ centralizer (U L : Set G) := by
    intro hvC
    apply hsq
    rw [hb.core_eq]
    refine ⟨hs, ?_⟩
    rw [← hvq]
    exact (centralizer (U L : Set G)).mul_mem hvC ((hb.core_eq ▸ hq).2)
  ext y
  constructor
  · rintro ⟨hyQ, hyC⟩
    have hys : Commute y s := mem_centralizer_singleton_iff.mp hyC
    have hyq : Commute y q := commute_of_mem hyQ hq
    have hyv : Commute y v := by
      have hh := hys.mul_right hyq.inv_right
      simpa only [← hvq, mul_inv_cancel_right] using hh
    have hym : y ∈ (U L : Set G) * (D R L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right (U L) (D R L) hUD]
      exact hp.core ▸ hyQ
    obtain ⟨u, hu, d, hd, hud⟩ := hym
    have hdv : Commute d v := commute_of_mem
      (P := E) (mem_sup_right hd) (mem_sup_left hv)
    have huv : Commute u v := by
      have hh := hyv.mul_left hdv.inv_left
      simpa only [← hud, mul_inv_cancel_right] using hh
    have huV : u ∈ V := fixed_four_le hcard hUnV hVnU hv hvmove
      ⟨hu, mem_centralizer_singleton_iff.mpr huv.eq⟩
    refine ⟨hyQ, ?_⟩
    rw [← hud]
    exact E.mul_mem (mem_sup_left huV) (mem_sup_right hd)
  · rintro ⟨hyQ, hyE⟩
    refine ⟨hyQ, mem_centralizer_singleton_iff.mpr ?_⟩
    have hyv : Commute y v := commute_of_mem (P := E) hyE (mem_sup_left hv)
    have hyq : Commute y q := commute_of_mem hyQ hq
    rw [← hvq]
    exact (hyv.mul_right hyq).eq

omit [Finite G] in
/-- Triviality of the actual fixed layer transfers the defining binary
A₃-module order to the full embedded commutator module. -/
theorem alternatingThree_U_card_of_blockFixed_eq_bot
    {L : Subgroup G} (hL : ChapterC.IsAlternatingBlock L 3)
    (hz : ChapterC.blockFixed L = ⊥) : Nat.card (U L) = 4 := by
  have hquot : Nat.card (ChapterC.BlockModule L) = Nat.card (ChapterC.blockU L) := by
    change Nat.card (ChapterC.blockU L ⧸ ChapterC.blockFixed L) = _
    rw [hz]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  rw [U, card_map_of_injective L.subtype_injective, ← hquot,
    hL.module_card_odd (by decide)]
  rfl

/-- Assembly of the A₃ fixed spaces from the intrinsic central-layer theorem. -/
theorem alternatingThreeInput_of_cover
    (hcover : Factorizations.NaturalIndices.AlternatingThreeCoverInput (G := G))
    (K : GroupClass.{u}) : AlternatingThreeInput (G := G) K := by
  intro A H R L h hb hL x hx _ hp hf
  exact fixedSpaceCalculation_of_card_four h hb hx hp hf
    (alternatingThree_U_card_of_blockFixed_eq_bot hL (hcover L hL))

/-- The A₃ block has the required full fixed subgroups for every actor in
`S − Q`. The intrinsic covering theorem discharges the central-layer premise. -/
theorem alternatingThreeInput (K : GroupClass.{u}) :
    AlternatingThreeInput (G := G) K :=
  alternatingThreeInput_of_cover Factorizations.NaturalIndices.alternatingThreeCoverInput K

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.NaturalFamily
