module
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import CFSG.Quasithin.ChapterG.Section07.MathieuRecognition.DegreeBounds
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M24.Properties.AutomorphismTwoRank
public import Theory.Mathieu.M24.Properties.Simplicity
/-!
# Sharp-degree exclusions for the Mathieu and triple-A6 rows

At the original sharp bound d ≤ m+2 the actor's faithful conjugation action
bounds d by the automorphism two-rank plus two. The actual Mathieu orders
force binary degree at least ten or eleven, strictly above this threshold.
The M22 central-quotient argument retains every perfect cover. The actual
triple-A6 cover has degree exactly six at the ordinary G.9 bound, whereas
the sharp bound permits at most five.

Source: Aschbacher–Smith G.9.3(0)–(5), G.11.6–8, printed pp.353–356,366–369.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterG.Section09
open Sporadic.Mathieu
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}
  (h : ComponentHypothesis K ρ A L L m)
include h
private theorem sharp_rank_bound (hd : Module.finrank (ZMod 2) V ≤ m+2) :
    Module.finrank (ZMod 2) V ≤ primeRank 2 (MulAut L) + 2 := by
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  exact hd.trans (Nat.add_le_add_right (h.toSetup.rank_le_automorphisms (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]; exact le_top)) 2)

theorem ComponentHypothesis.not_m12_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2) (e : L ≃* M12) : False := by
  have hr : primeRank 2 (MulAut M12) ≤ 7 := by
    apply primeRank_le_of_prime_pow_not_dvd
    rw [← Nat.card_congr M12ExceptionalExtension.automorphismEquiv.toEquiv,
      M12ExceptionalExtension.carrier_order]
    decide
  have hu := sharp_rank_bound h hd
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hl := Section07.MathieuRecognition.ten_le_finrank_of_m12
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e
  omega

/-- The simple M22 carrier is too large in the sharp degree range. -/
theorem ComponentHypothesis.not_m22_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2) (e : L ≃* M22) : False := by
  have hu := sharp_rank_bound h hd
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m22_automorphism_twoRank_le_five
  have hl := Section07.MathieuRecognition.ten_le_finrank_of_m22
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e
  omega

theorem ComponentHypothesis.not_m22_central_quotient_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2)
    (e : (L ⧸ center L) ≃* M22) : False := by
  let : IsQuasisimple L := h.component.2
  have hr := m22_automorphism_twoRank_le_five
  have hu := DefiningCharacteristic.TwistedExclusions.actor_rank_le_of_central_quotient h e hr
  have hdv : 11 ∣ Nat.card L := by
    have hq := (center L).card_quotient_dvd_card
    rw [Nat.card_congr e.toEquiv, m22_order] at hq
    exact (by norm_num : 11 ∣ 443520).trans hq
  have hl := BinaryPrimeDegree.orderOf_le_finrank (ρ.comp L.subtype)
    (h.faithful.comp L.subtype_injective) (by decide : Nat.Prime 11) (by decide) hdv
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hl
  omega

theorem ComponentHypothesis.not_m23_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2) (e : L ≃* M23) : False := by
  have hu := sharp_rank_bound h hd
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m23_automorphism_twoRank_le_four
  have hl := Section07.MathieuRecognition.eleven_le_finrank_of_m23
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e
  omega

theorem ComponentHypothesis.not_m24_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2) (e : L ≃* M24) : False := by
  let : Group.IsPerfect L := h.component.2.toIsPerfect
  let : Group.IsPerfect M24 := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  have hz : center M24 = ⊥ := by
    rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative M24 (center_eq_top_iff.mp h)).elim
  have hu := sharp_rank_bound h hd
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := m24_automorphism_rank_le_six hz
  have hl := Section07.MathieuRecognition.eleven_le_finrank_of_m24
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e
  omega

theorem ComponentHypothesis.not_triple_alternating_six_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2)
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center L) = 3) : False := by
  let : IsQuasisimple L := h.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hr := DefiningCharacteristic.AlternatingSixCover.cover_automorphism_two_rank e
  have hl := DefiningCharacteristic.AlternatingSixCover.small_degree_eq_six e hz
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) h.single_component_degree_bound
  have hu := sharp_rank_bound h hd
  omega
end CFSG.Quasithin.ChapterG.Section09
