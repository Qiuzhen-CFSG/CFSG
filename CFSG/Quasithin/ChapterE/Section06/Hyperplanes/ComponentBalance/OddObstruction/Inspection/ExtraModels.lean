module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.SmallBorel
public import Theory.SpecificGroups.PSL2.AdjacentPowerOddCore
public import Theory.SpecificGroups.BinaryLinear.SylowFixedOddCore
public import Theory.SpecificGroups.PSL3Three.SylowFixedOddCore
public import Theory.Mathieu.M11.Properties.SylowFixedOddCore
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# The additional adequate E.6.8 models in the E.6.19 inspection

The linear-four and odd rows are excluded directly from their actual group
models and faithful Sylow-fixing action. No equality A=C_V(L) is used.
The binary linear, ternary linear and Mathieu calculations have trivial
odd core in the original actor centralizer. The Fermat–Mersenne arithmetic
gives the adjacent power of two needed by the reflected-torus calculation;
genuine quasisimplicity excludes the solvable prime-three endpoint.

The last theorem applies to the original detected component and its induced
automorphism group. Source: Aschbacher–Smith E.6.8(3),(5), pp.247–248,
and E.6.19, p.252 (PDF p.263).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
variable {L : Subgroup G} {φ : H →* MulAut L} {E : Subgroup H}

/-- The exact remaining model part of the adequate linear-four and odd rows. -/
def ExtraModel (L : Subgroup G) : Prop :=
  ClassicalGroup.IsPSL L 4 2 ∨
  (∃ p : ℕ, IsFermatOrMersennePrime p ∧
    ClassicalGroup.IsPSL L 2 p) ∨
  ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)

private theorem parameter_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
  · rw [hk]
    exact (even_two.pow_of_ne_zero (pow_ne_zero k (by decide : (2 : ℕ) ≠ 0))).add_odd odd_one
  · have hk0 : k ≠ 0 := by
      intro h
      have := hp.1.two_le
      simp [h] at hk
      omega
    have hEven : Even (p + 1) := hk ▸ (even_two.pow_of_ne_zero hk0)
    rw [Nat.even_iff] at hEven
    exact Nat.odd_iff.mpr (by omega)

/-- The original prime-linear actor centralizer has trivial odd core. -/
theorem fermat_mersenne_oddCore_eq_bot [IsQuasisimple L]
    (d : Theory.GroupAction.SylowFixedInvolution φ E) {p : ℕ}
    (hp : IsFermatOrMersennePrime p)
    (hm : ClassicalGroup.IsPSL L 2 p) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := hm
  have ho : Odd p := parameter_odd hp
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : Nontrivial PSL(2,F) := e.symm.toEquiv.nontrivial
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hl : 3 < p := by
    rw [← hF]
    exact Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF ▸ ho) (Group.IsPerfect.not_isSolvable _)
  let : Fact p.Prime := ⟨hp.1⟩
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp.1
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  have hk : ∃ k : ℕ, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
    rcases hp.2 with ⟨k,hk⟩ | ⟨k,hk⟩
    · exact ⟨2 ^ k,Or.inl (by omega)⟩
    · exact ⟨k,Or.inr hk⟩
  obtain ⟨k,hk⟩ := hk
  exact Theory.PSL2.prime_adjacent_sylowFixedInvolution_oddCore_eq_bot ho hl hk
    (d.equiv (e.trans (Atlas.fieldEquivPSL 2 f)))

/-- Every additional adequate model is excluded on the original actor centralizer. -/
theorem extra_oddCore_eq_bot [IsQuasisimple L]
    (d : Theory.GroupAction.SylowFixedInvolution φ E) (hm : ExtraModel L) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  rcases hm with h4 | hp | h3 | hM
  · obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := h4
    let := Fintype.ofFinite F
    let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    let j := (e.trans (Atlas.fieldEquivPSL 4 f)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
    exact BinaryLinear.OuterCyclic.sylowFixedInvolution_oddCore_eq_bot (Or.inl rfl) (d.equiv j)
  · obtain ⟨p,hp,hm⟩ := hp
    exact fermat_mersenne_oddCore_eq_bot d hp hm
  · obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ := h3
    let := Fintype.ofFinite F
    let f : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    exact Matrix.PSL3Three.sylowFixedInvolution_oddCore_eq_bot
      (d.equiv (e.trans (Atlas.fieldEquivPSL 3 f)))
  · obtain ⟨e⟩ := hM
    exact Sporadic.Mathieu.m11_sylowFixedInvolution_oddCore_eq_bot (d.equiv e)

omit [Finite H] in
/-- The actual E.6.19 detected component cannot realize any additional adequate row. -/
theorem detected_not_extraModel {A U V M : Subgroup G}
    {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (hUV : U ≤ V) (hindex : A.relIndex U = 2)
    (d : DetectedComponent A U V L) : ¬ ExtraModel L := by
  intro hm
  let : IsQuasisimple L := d.quasisimple
  exact d.action_oddCore (extra_oddCore_eq_bot
    (detected_sylowFixedInvolution h hA hUV hindex d) hm)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
