module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Central-cover reductions for the even cases of 1.1.5

Innerness and inversion of the odd core make the center a two-group. An odd
universal kernel then kills this center: the marked central projection is a
perfect cover, so its kernel is a quotient of the universal kernel. The
center-free case gives precisely source alternative (a). The exceptional
linear and G₂ cases instead permit alternative (b).

The rank-two interface bridge uses the actual Ree local-block equivalence.
Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--503, and I.1.3.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
open Section02.LocalModels

variable {L H : Type*} [Group L] [Group H]

/-- The two rank-two source interfaces agree on every family, including the
genuine Ree construction and both small derived groups. -/
theorem rankTwoTheoremC_of_model {f : ℕ}
    (h : ChapterA.Section02.IsTheoremCRankTwoModel H f) : RankTwoTheoremC H := by
  cases h with
  | linear hf iso => exact .linear f hf iso
  | symplectic hf iso => exact .symplectic f hf iso
  | g2 hf iso => exact .g2 f hf iso
  | triality hf iso => exact .triality f hf iso
  | ree_f4 m hm _ iso =>
      exact .ree m hm ((ReeF4.exists_localBlockInput_mulEquiv_iff H m).mpr iso)
  | symplectic_derived _ iso => exact .symplectic_derived iso
  | g2_derived _ iso => exact .g2_derived iso
  | tits _ iso => exact .tits iso

private theorem rankTwo_transport (h : RankTwoTheoremC H) (e : L ≃* H) :
    RankTwoTheoremC L := by
  cases h with
  | linear f hf iso => exact .linear f hf (iso.of_mulEquiv e)
  | symplectic f hf iso => exact .symplectic f hf (iso.of_mulEquiv e)
  | g2 f hf iso => exact .g2 f hf (iso.of_mulEquiv e)
  | triality f hf iso => exact .triality f hf (iso.of_mulEquiv e)
  | ree m hm iso =>
      obtain ⟨a, ⟨b⟩⟩ := iso
      exact .ree m hm ⟨a, ⟨e.trans b⟩⟩
  | symplectic_derived iso => exact .symplectic_derived (iso.map e.trans)
  | g2_derived iso => exact .g2_derived (iso.map e.trans)
  | tits iso => exact .tits (iso.map e.trans)

private theorem lie_transport (h : LieTypeTwoModel H) (e : L ≃* H) :
    LieTypeTwoModel L := by
  rcases h with h | h | ⟨n, hn, h⟩
  · exact .inl (h.of_mulEquiv e)
  · exact .inr (.inl (rankTwo_transport h e))
  · exact .inr (.inr ⟨n, hn, h.of_mulEquiv e⟩)

variable [Finite L] [IsQuasisimple L] {α : MulAut L} {P : Sylow 2 L}

/-- Apply a proved model Sylow-fixer calculation to the original action. -/
theorem MarkedInvolution.inner_of_model_fixer (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* H)
    (hH : ∀ (Q : Sylow 2 H) (b : MulAut H),
      (∀ y ∈ Q, b y = y) → ∃ y ∈ Q, b = MulAut.conj y) :
    α ∈ (MulAut.conj (G := L)).range := by
  obtain ⟨x, _, hx⟩ := MulAut.fixing_sylow_inner_of_centralQuotient e hH P α d.fixes
  exact ⟨x, hx.symm⟩

omit [Finite L] in
/-- The center of the marked cover divides the literal universal kernel. -/
theorem center_card_dvd_universal_kernel (e : L ⧸ center L ≃* H) :
    Nat.card (center L) ∣ Nat.card (universalProjection H).ker := by
  let c := centralQuotientCover e
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective c.surjective
  obtain ⟨a, ha, _⟩ := universalProjection_existsUnique_lift
    c.toMonoidHom c.surjective c.ker_le_center
  have hs : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect c.toMonoidHom a
      (ha ▸ universalProjection_surjective H) c.ker_le_center
  simpa only [c, centralQuotientCover_ker] using
    kernel_card_dvd_of_surjective_factor (universalProjection H) c.toMonoidHom a hs ha

/-- Only the two-primary multiplier exclusion is needed after innerness;
odd multiplier factors are irrelevant to this source branch. -/
theorem MarkedInvolution.center_eq_bot_of_odd_universal_kernel
    (d : MarkedInvolution α P) (hi : α ∈ (MulAut.conj (G := L)).range)
    (e : L ⧸ center L ≃* H) (hm : ¬ 2 ∣ Nat.card (universalProjection H).ker) :
    center L = ⊥ := by
  have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
  have hp : IsPGroup 2 (center L) := hz ▸ pCore_isPGroup
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hn : ¬ 2 ∣ Nat.card (center L) :=
    fun h => hm (h.trans (center_card_dvd_universal_kernel e))
  have hk0 : k = 0 := by
    by_contra h
    apply hn
    rw [hk]
    exact dvd_pow_self 2 h
  exact Subgroup.card_eq_one.mp (by simpa only [hk0, pow_zero] using hk)

omit [Finite L] in
/-- The center-free source alternative, retaining the original automorphism. -/
theorem MarkedInvolution.lie_of_center_eq_bot (_d : MarkedInvolution α P)
    (hmodel : LieTypeTwoModel (L ⧸ center L))
    (hi : α ∈ (MulAut.conj (G := L)).range) (hz : center L = ⊥) :
    ModelAction115 L α := by
  let e : L ≃* L ⧸ center L :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact .lie e.isSimpleGroup (lie_transport hmodel e) hi

/-- The allowed nontrivial two-covers require no exceptional multiplier table. -/
theorem MarkedInvolution.exceptional_of_inner (d : MarkedInvolution α P)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 3 4 ∨
      IsG2At (L ⧸ center L) 4)
    (hi : α ∈ (MulAut.conj (G := L)).range) : ModelAction115 L α := by
  have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
  by_cases hzero : center L = ⊥
  · apply d.lie_of_center_eq_bot _ hi hzero
    apply Or.inr ∘ Or.inl
    rcases hmodel with h | h
    · exact .linear 2 (by decide) h
    · exact .g2 2 (by decide) h
  · exact .two_cover hzero hz
      (hmodel.imp (fun h => h.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hz.symm))
        (fun h => h.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hz.symm))) hi

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
