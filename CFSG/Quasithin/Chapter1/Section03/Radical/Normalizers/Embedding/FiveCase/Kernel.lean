module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Models
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.MarkTransport

/-!
# Uniqueness of the elementary kernel and the Sylow marking

A normal subgroup with either of the two Ξ quotient shapes must equal the
specified elementary kernel of an SL₂ extension: its odd image in SL₂ is
trivial, its prime therefore agrees with the kernel prime, and the orders
force equality. For any map with p-group image, every chosen Sylow p-subgroup
has the whole image. The latter statement preserves the map and every choice
of Sylow subgroup; it does not select a new abstract kernel.

These are ingredients of the case-(10) deduction in Aschbacher–Smith,
proof of 1.3.8, printed p.513. Establishing the required properties of the
actual quotient image in that deduction is a separate obligation.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02.LocalModels
universe u v
variable {B : Type u} [Group B] [Finite B]

/-- Cardinality in the concrete elementary model. -/
theorem elementary_card {s n : ℕ} {A : Type*} [Group A]
    (h : ElementaryModel s n A) : Nat.card A = s ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin n → ZMod s) = s ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- The prime and subgroup are forced; the extraspecial alternative cannot fit. -/
theorem normal_xi_eq_kernel {p s : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hs : s.Prime) (hs3 : 3 < s) (U D : Subgroup B) [U.Normal] [D.Normal]
    (hU : ElementaryModel s 2 U)
    (e : B ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s))
    (hD : XiOddQuotient p D) : p = s ∧ D = U := by
  have hDodd : Odd (Nat.card D) := by
    rcases hD with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> exact hpodd.pow
  have hle : D ≤ U := odd_normal_le_kernel hs hs3 U D e hDodd
  have hcardU := elementary_card hU
  have hpD : p ∣ Nat.card D := by
    rcases hD with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> exact dvd_pow_self p (by decide)
  have hps : p = s := (Nat.prime_dvd_prime_iff_eq hp hs).mp
    (hp.dvd_of_dvd_pow (hcardU ▸ hpD.trans (card_dvd_of_le hle)))
  refine ⟨hps, eq_of_le_of_card_ge hle ?_⟩
  rw [hcardU, ← hps]
  rcases hD with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact hc.ge
  · rw [hc, pow_succ]
    exact Nat.le_mul_of_pos_right _ hp.pos

omit [Finite B] in
/-- Every chosen Sylow subgroup maps onto a p-group image. -/
theorem sylow_map_eq_range {A : Type v} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (f : A →* B) (hf : IsPGroup p f.range)
    (P : Sylow p A) : (P : Subgroup A).map f = f.range := by
  have htop : (P : Subgroup A).map f.rangeRestrict = ⊤ :=
    (P.mapSurjective f.rangeRestrict_surjective).is_maximal'
      (hf.to_subgroup ⊤) le_top |>.symm
  have hh := congrArg (map f.range.subtype) htop
  simpa only [map_map, MonoidHom.subtype_comp_rangeRestrict,
    ← MonoidHom.range_eq_map, range_subtype] using hh

/-- The marked subgroup equals the named kernel when its actual normal image
has a Ξ quotient shape. -/
theorem normal_xi_marked_five {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (A P : Subgroup H) (hPA : P ≤ A) [(P.subgroupOf A).Normal]
    (hP : XiOddQuotient p P)
    (hA : HasExtension A (ElementaryModel 5 2) (fun X _ => IsSL X 2 5)) :
    p = 5 ∧ MarkedFiveExtension A P := by
  obtain ⟨U, hn, hU, hquot⟩ := hA
  let := hn
  obtain ⟨e⟩ := (isSL_prime_iff (by decide : Nat.Prime 5)).mp hquot
  have hPin : XiOddQuotient p (P.subgroupOf A) :=
    hP.of_mulEquiv (subgroupOfEquivOfLe hPA).symm
  obtain ⟨hp5, hPU⟩ := normal_xi_eq_kernel hp hpodd (by decide) (by decide)
    U (P.subgroupOf A) hU e hPin
  refine ⟨hp5, hPA, ?_, inferInstance, ?_⟩
  · obtain ⟨eU⟩ := hU
    exact ⟨(subgroupOfEquivOfLe hPA).symm.trans
      ((MulEquiv.subgroupCongr hPU).trans eU)⟩
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hPU).trans e⟩

/-- Once the Fitting kernel is identified, its prime support is exact. -/
theorem odd_fitting_prime_iff {s : ℕ} (hs : s.Prime) (hs3 : 3 < s)
    (U : Subgroup B) [U.Normal] (hU : ElementaryModel s 2 U)
    (e : B ⧸ U ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod s))
    (hF : Odd (Nat.card (fittingSubgroup B))) {q : ℕ} (hq : q.Prime) :
    q ∣ Nat.card (fittingSubgroup B) ↔ q = s := by
  rw [fitting_eq_extension_kernel hs hs3 U hU e hF, elementary_card hU]
  constructor
  · intro hd
    exact (Nat.prime_dvd_prime_iff_eq hq hs).mp (hq.dvd_of_dvd_pow hd)
  · rintro rfl
    exact dvd_pow_self q (by decide)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
