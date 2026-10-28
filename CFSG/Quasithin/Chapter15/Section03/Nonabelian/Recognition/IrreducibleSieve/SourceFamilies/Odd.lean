module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Common
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Alternating
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.G2
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Binary
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank

/-!
# Excluding the odd-characteristic source components

The original actor order bounds the degree by twice one more than the full
component automorphism two-rank. The proved Chapter G degree sieve reduces
odd PSL₂ groups to A₅, PSL₃(2), and A₆. The binary PSL₃ catalogue rules out
the middle endpoint; the actual alternating source exclusions close the others.
The ternary families reduce to PSU₃(3), whose derived G₂ identification feeds
the source quadratic obstruction. No generic G.9 classification is assumed.

Source: Aschbacher–Smith, G.7.2–3 and 15.3.58, printed pp.347–348,1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Odd

open Subgroup Representation ChapterG.Section09 ChapterG.Section07
open Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
attribute [local instance] ZMod.algebra

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

theorem not_linear_three_binary (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hm : ClassicalGroup.IsPSL K 3 2) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  let a : K ≃* SL(3, ZMod 2) :=
    (e.trans (Atlas.fieldEquivPSL 3 f)).trans Matrix.PSL3Two.equiv.symm
  have hr : primeRank 2 (MulAut K) = 2 := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two F hc
  have hd := h.degree_le_component_automorphisms hK
  rw [hr] at hd
  let σ := (ρ.comp K.subtype).comp a.symm.toMonoidHom
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    a.symm.toMonoidHom a.symm.surjective (ρ.comp K.subtype)).mpr inferInstance
  have hnon : ∃ g, σ g ≠ 1 := by
    by_contra! hh
    have hsub : Subsingleton K := ⟨by
      intro x y
      apply Subtype.ext
      apply h.faithful
      have hx := hh (a x)
      have hy := hh (a y)
      simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, Subgroup.coe_subtype] using hx.trans hy.symm⟩
    let := hsub
    exact hK.nonsolvable inferInstance
  obtain ⟨h3, _⟩ := DefiningCharacteristic.LinearThreeRecognition.binary_small_module σ hnon hd
  have := h.six_le_degree
  omega

theorem not_linear_unitary_three (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : OddCharacteristic.IsLinearUnitaryThree K p) : False := by
  let := hsimple
  let : IsQuasisimple K := ChapterA.Section02.Sporadic.SourceAssembly.simple_quasisimple hnonab
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  have hr := OddCharacteristic.linearUnitaryThree_automorphism_two_rank_le_three hp ho hm
  have hd := h.degree_le_component_automorphisms hK
  obtain ⟨_, hpsu, _⟩ := OddCharacteristic.linear_unitary_three_small_degree
    (ρ.comp K.subtype) (h.faithful.comp Subtype.val_injective) hp ho hm (by omega)
  exact h.not_g2_derived_component hK
    (OddCharacteristic.psu33_nonempty_equiv_g2_derived hpsu)

theorem linear_two_alternating (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ e)) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  let := hsimple
  let : Group.IsPerfect K := ⟨
    (inferInstance : (commutator K).Normal).eq_bot_or_eq_top.resolve_left
      (fun he => hnonab ((commutator_eq_bot_iff K).mp he))⟩
  have he : 0 < e := by
    by_contra hh
    have he0 : e = 0 := by omega
    obtain ⟨F, _, _, hc, _⟩ := hm
    have := Finite.one_lt_card (α := F)
    simp only [he0, pow_zero] at hc
    omega
  have hsmall := OddCharacteristic.psl2_parameter_le_nine_of_degree_le_automorphism_rank
    (ρ.comp K.subtype) (h.faithful.comp Subtype.val_injective)
    hp ho he hm (h.degree_le_component_automorphisms hK)
  rcases OddCharacteristic.psl2_small_odd_identification ho.pow hsmall hm with
    h5 | h7 | h9
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h5
    exact .inl ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5 hc)⟩
  · exact (not_linear_three_binary h hK h7).elim
  · obtain ⟨e⟩ := h9
    exact .inr ⟨e.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- Every odd-characteristic Theorem C model is impossible for the actual
irreducible component and source action. The SQTK hypothesis is unnecessary
once the model has been selected. -/
theorem exclude (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hsimple : IsSimpleGroup K) (hnonab : ¬ IsMulCommutative K)
    (hm : ChapterA.Section02.IsTheoremCOddModel K) : False := by
  cases hm with
  | linear_two p e hp ho _ hm =>
    rcases linear_two_alternating h hK hsimple hnonab hp ho hm with h5 | h6
    · obtain ⟨a⟩ := h5
      exact Alternating.not_five_component h hK a
    · obtain ⟨a⟩ := h6
      exact Alternating.not_six_component h hK a
  | linear_three p hp ho hm =>
    exact not_linear_unitary_three h hK hsimple hnonab hp ho (.inl hm)
  | unitary_three p hp ho hm =>
    exact not_linear_unitary_three h hK hsimple hnonab hp ho (.inr (.inr (.inl hm)))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Odd
