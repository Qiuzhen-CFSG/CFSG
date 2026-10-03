module
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.ElementaryAbelian.TenPointConfiguration
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Five-four actions on an elementary sixteen

Let C₅ ⋊ C₄ act faithfully on an elementary abelian group V of order sixteen.
Every nonidentity orbit either has five elements or contains generators
v₀,v₁,v₂,v₃ together with v₀v₁,v₀v₂,v₀v₃.

The restricted five-action is nontrivial by faithfulness, hence fixes only
the identity by the finite-action cardinality lemma. Its action on any
nonidentity orbit has no fixed points, so that orbit has size divisible by
five. Unless its size is five, it has at least ten points. The general
geometry of ten-point subsets of an elementary sixteen then gives exactly
the required configuration. This proof also shows that faithfulness of the
C₄ action on C₅ is not needed for this weaker orbit alternative.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
factor group H/E and Lemma 4, printed pp.674–675.
-/

open MulAction

namespace Theory.GroupAction

private abbrev C5 := Multiplicative (ZMod 5)
private abbrev C4 := Multiplicative (ZMod 4)

/-- Every nonidentity orbit of a faithful five-four action on a group of order
sixteen has cardinality divisible by five. -/
public theorem five_dvd_orbit_card_of_faithful_five_four_action
    {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (x : V) (hx : x ≠ 1) :
    5 ∣ (Set.range (fun g => f g x)).ncard := by
  let M := SemidirectProduct C5 C4 φ
  let : MulDistribMulAction M V := MulDistribMulAction.compHom V f
  let i : C5 →* M := SemidirectProduct.inl
  let : MulDistribMulAction C5 V := MulDistribMulAction.compHom V i
  have hC5 : Nat.card C5 = 5 := by change Nat.card (ZMod 5) = 5; simp
  have hne : FixedPoints.subgroup C5 V ≠ ⊤ := by
    intro htop
    have ha (a : C5) : f (i a) = 1 := by
      ext v
      have hv : v ∈ FixedPoints.subgroup C5 V := by rw [htop]; trivial
      exact hv a
    have hai : (Multiplicative.ofAdd (1 : ZMod 5) : C5) = 1 := by
      apply SemidirectProduct.inl_injective (φ := φ)
      apply hf
      exact (ha _).trans (map_one f).symm
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 5) : C5) ≠ 1) hai
  have hfixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hC5 hV hne
  let : MulAction C5 (orbit M x) := MulAction.compHom (orbit M x) i
  have hempty : fixedPoints C5 (orbit M x) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyv : (y : V) ∈ FixedPoints.subgroup C5 V := by
      intro a
      exact congrArg Subtype.val (hy a)
    have hyone : (y : V) = 1 := hfixed.le hyv
    obtain ⟨g, hg⟩ := y.property
    exact hx ((f g).injective (hg.trans (hyone.trans (map_one (f g)).symm)))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 C5 := IsPGroup.of_card (n := 1) (by simp)
  have hmod := hp.card_modEq_card_fixedPoints (orbit M x)
  have hz : Nat.card (fixedPoints C5 (orbit M x)) = 0 := by
    rw [hempty]
    exact Nat.card_of_isEmpty
  rw [hz] at hmod
  have horbit : orbit M x = Set.range (fun g => f g x) := rfl
  rw [← horbit]
  exact Nat.modEq_zero_iff_dvd.mp hmod

/-- A nonidentity orbit has five points, or contains four generators and all
three products of the first generator with the other three. -/
public theorem five_four_sixteen_orbit_eq_five_or_generating_configuration
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (_hφ : Function.Injective φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (x : V) (hx : x ≠ 1) :
    (Set.range (fun g => f g x)).ncard = 5 ∨
      ∃ v : Fin 4 → V, Subgroup.closure (Set.range v) = ⊤ ∧
        (∀ i, ∃ g, f g x = v i) ∧
        (∀ j : Fin 4, j ≠ 0 → ∃ g, f g x = v 0 * v j) := by
  classical
  let O : Set V := Set.range (fun g => f g x)
  have hdiv : 5 ∣ O.ncard :=
    five_dvd_orbit_card_of_faithful_five_four_action hV φ f hf x hx
  have hpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite O)).mpr ⟨x, 1, by simp⟩
  by_cases hfive : O.ncard = 5
  · exact Or.inl hfive
  have hten : 10 ≤ O.ncard := by
    obtain ⟨k, hk⟩ := hdiv
    omega
  have hzero : (1 : V) ∉ O := by
    rintro ⟨g, hg⟩
    exact hx ((f g).map_eq_one_iff.mp hg)
  exact Or.inr (Theory.ElementaryAbelian.exists_generating_configuration_of_ten_le_ncard
    hV O hzero hten)

end Theory.GroupAction
