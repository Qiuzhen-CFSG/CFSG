module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Coordinates
/-!
# Coordinates for binary five-space flags with a factor five

A subgroup of order five fixes exactly a line in binary five-space. Orbit
counting on each invariant subspace excludes dimensions two and three and
excludes a nested invariant line and hyperplane. Consequently any nonempty
proper flag whose stabilizer has order divisible by five consists of a single
line or hyperplane. Extending a basis of that subspace puts the actual embedded
stabilizer into the endpoint coordinates used by the two-core quotient API.

The orbit-counting proof extends the coordinate argument of
`Residuals.FlagTypes` to arbitrary subspaces. The intended application supplies
its factor five from the literal A₅ residual; no flag-coordinate premise remains.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.2.7(3)(h), pp.145–147, and 14.7.68(2), pp.1071–1072.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry.GeometricFlags
open OuterCyclic
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) (matrixEquivLinear 5).toEquiv

private theorem fixedSpace_card_two (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 5 Q) (hQ0 : Q ≠ ⊥) : Nat.card (fixedSpace Q) = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have he : MulAction.fixedPoints Q (Space 5) = (fixedSpace Q : Set (Space 5)) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    change (∀ q : Q, q.val v = v) ↔ ∀ q ∈ Q, q v = v
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h q => h q.val q.property⟩
  have hc := hQ.card_modEq_card_fixedPoints (Space 5)
  rw [he] at hc
  change Nat.card (Space 5) ≡ Nat.card (fixedSpace Q) [MOD 5] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space 5),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace Q)] at hc
  norm_num [Space] at hc
  have hd := Submodule.finrank_lt (fixedSpace_ne_top hQ0)
  norm_num [Space] at hd
  have hd1 : Module.finrank (ZMod 2) (fixedSpace Q) = 1 := by
    interval_cases hh : Module.finrank (ZMod 2) (fixedSpace Q) <;>
      first | rfl | norm_num [Nat.ModEq, hh] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd1]
  norm_num

private abbrev invariantAction (Q : Subgroup (LinearGroup 5))
    (W : Submodule (ZMod 2) (Space 5)) (hW : Q ≤ parabolic W) : MulAction Q W where
  smul q w := ⟨q.val w.val, (hW q.property w.val).mpr w.property⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

private theorem invariant_card_residue (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 5 Q) (hc : Nat.card (fixedSpace Q) = 2)
    (W : Submodule (ZMod 2) (Space 5)) (hW : Q ≤ parabolic W) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ Nat.card W ≡ n [MOD 5] ∧
      (fixedSpace Q ≤ W → n = 2) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : MulAction Q W := invariantAction Q W hW
  let toFixed : MulAction.fixedPoints Q W → fixedSpace Q := fun x =>
    ⟨x.val.val, fun q hq => congrArg Subtype.val
      ((MulAction.mem_fixedPoints.mp x.property) ⟨q, hq⟩)⟩
  have hinj : Function.Injective toFixed := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : fixedSpace Q => x.val) he
  have hle := Nat.card_le_card_of_injective toFixed hinj
  rw [hc] at hle
  have hz : (0 : W) ∈ MulAction.fixedPoints Q W := by
    rw [MulAction.mem_fixedPoints]
    intro q
    apply Subtype.ext
    exact q.val.map_zero
  let : Nonempty (MulAction.fixedPoints Q W) := ⟨⟨0, hz⟩⟩
  refine ⟨Nat.card (MulAction.fixedPoints Q W), Nat.card_pos, hle,
    hQ.card_modEq_card_fixedPoints W, ?_⟩
  intro hcontain
  let fromFixed : fixedSpace Q → MulAction.fixedPoints Q W := fun x =>
    ⟨⟨x.val, hcontain x.property⟩, MulAction.mem_fixedPoints.mpr (fun q =>
      Subtype.ext (x.property q.val q.property))⟩
  have hinj' : Function.Injective fromFixed := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun x : MulAction.fixedPoints Q W => x.val.val) he
  have hge := Nat.card_le_card_of_injective fromFixed hinj'
  rw [hc] at hge
  omega


/-- A factor five forces invariant proper subspaces to be endpoints, with no nesting. -/
theorem invariant_subspaces_of_five_dvd (P : Subgroup (LinearGroup 5))
    (hfive : 5 ∣ Nat.card P) :
    (∀ W : Submodule (ZMod 2) (Space 5), W ≠ ⊥ → W ≠ ⊤ → P ≤ parabolic W →
      Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 4) ∧
    (∀ W U : Submodule (ZMod 2) (Space 5), W ≠ ⊥ → U ≠ ⊤ →
      P ≤ parabolic W → P ≤ parabolic U → W ≤ U → W = U) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let Q : Subgroup (LinearGroup 5) := zpowers g.val
  have hQc : Nat.card Q = 5 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective P.subtype Subtype.val_injective g).trans hg
  have hQ : IsPGroup 5 Q := IsPGroup.of_card (n := 1) (by simpa using hQc)
  have hQ0 : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hQc
    omega
  have hQP : Q ≤ P := zpowers_le.mpr g.property
  have hc := fixedSpace_card_two Q hQ hQ0
  have dims (W : Submodule (ZMod 2) (Space 5)) (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
      (hWP : P ≤ parabolic W) :
      Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 4 := by
    obtain ⟨n, hn1, hn2, hn, _⟩ := invariant_card_residue Q hQ hc W (hQP.trans hWP)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hn
    have hpos : 0 < Module.finrank (ZMod 2) W :=
      Nat.pos_of_ne_zero (fun hz => hW (Submodule.finrank_eq_zero.mp hz))
    have hlt := Submodule.finrank_lt hWt
    rw [Module.finrank_fin_fun] at hlt
    interval_cases hd : Module.finrank (ZMod 2) W
    · exact Or.inl rfl
    · norm_num [Nat.ModEq] at hn; omega
    · norm_num [Nat.ModEq] at hn; omega
    · exact Or.inr rfl
  refine ⟨dims, ?_⟩
  intro W U hW hUt hWP hUP hWU
  by_contra hne
  have hlt := Submodule.finrank_strictMono (lt_of_le_of_ne hWU hne)
  dsimp only at hlt
  have hWt : W ≠ ⊤ := fun he => hUt (top_unique (he ▸ hWU))
  have hU : U ≠ ⊥ := fun he => hW (bot_unique (he ▸ hWU))
  have hdW := dims W hW hWt hWP
  have hdU := dims U hU hUt hUP
  have hdW1 : Module.finrank (ZMod 2) W = 1 := by omega
  have hdU4 : Module.finrank (ZMod 2) U = 4 := by omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hvW : Submodule.span (ZMod 2) {v} = W :=
    Submodule.eq_of_le_of_finrank_eq (by rw [Submodule.span_singleton_le_iff_mem]; exact hv)
      ((finrank_span_singleton hv0).trans hdW1.symm)
  have hWfix : W ≤ fixedSpace Q := by
    rw [← hvW, Submodule.span_singleton_le_iff_mem]
    intro q hq
    have hp := hQP.trans hWP hq
    rw [← hvW, pointParabolic_eq_stabilizer hv0] at hp
    exact hp
  have hdFix : Module.finrank (ZMod 2) (fixedSpace Q) = 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hc)
  have heq : W = fixedSpace Q := Submodule.eq_of_le_of_finrank_eq hWfix
    (hdW1.trans hdFix.symm)
  obtain ⟨n, _, _, hn, hne⟩ := invariant_card_residue Q hQ hc U (hQP.trans hUP)
  rw [hne (heq ▸ hWU), Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    hdU4] at hn
  norm_num [Nat.ModEq] at hn


open SylowOvergroups

/-- A subspace of the prescribed dimension is a coordinate cut for some basis. -/
theorem exists_flagSpace (W : Submodule (ZMod 2) (Space 5)) (i : Fin 4)
    (hd : Module.finrank (ZMod 2) W = i.val + 1) :
    ∃ b : FiveBasis, flagSpace b i = W := by
  let f := LinearEquiv.ofFinrankEq (flagSpace standardBasis i) W
    ((finrank_flagSpace standardBasis i).trans hd.symm)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨standardBasis.map e, ?_⟩
  rw [flagSpace_map]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    change e w ∈ W
    rw [← he ⟨w, hw⟩]
    exact (f ⟨w, hw⟩).property
  · intro hx
    refine ⟨(f.symm ⟨x, hx⟩).val, (f.symm ⟨x, hx⟩).property, ?_⟩
    change e (f.symm ⟨x, hx⟩).val = x
    rw [← he]
    exact congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)

/-- Transport an actual nonempty flag to one endpoint using its factor five. -/
theorem exists_endpoint_coordinates {k : ℕ} (hk : 0 < k)
    (s : Fin k → Submodule (ZMod 2) (Space 5)) (hmono : Monotone s)
    (hzero : ∀ i, s i ≠ ⊥) (htop : ∀ i, s i ≠ ⊤)
    (hfive : 5 ∣ Nat.card (⨅ i, parabolic (s i) : Subgroup (LinearGroup 5))) :
    ∃ (b : FiveBasis) (i : Fin 4), (i = 0 ∨ i = 3) ∧
      (⨅ j, parabolic (s j)) = flagStabilizer b {i} := by
  let P := ⨅ i, parabolic (s i)
  have hPi (i : Fin k) : P ≤ parabolic (s i) := iInf_le _ i
  obtain ⟨hdim, heq⟩ := invariant_subspaces_of_five_dvd P hfive
  let first : Fin k := ⟨0, hk⟩
  have hs (i : Fin k) : s i = s first :=
    (heq (s first) (s i) (hzero first) (htop i) (hPi first) (hPi i)
      (hmono (show first ≤ i from Nat.zero_le i.val))).symm
  have hP : P = parabolic (s first) := by
    apply le_antisymm (hPi first)
    apply le_iInf
    intro i
    rw [hs i]
  rcases hdim (s first) (hzero first) (htop first) (hPi first) with hd | hd
  · obtain ⟨b, hb⟩ := exists_flagSpace (s first) 0 hd
    exact ⟨b, 0, Or.inl rfl, hP.trans (by rw [flagStabilizer_singleton, hb])⟩
  · obtain ⟨b, hb⟩ := exists_flagSpace (s first) 3 hd
    exact ⟨b, 3, Or.inr rfl, hP.trans (by rw [flagStabilizer_singleton, hb])⟩

end BinaryLinear.FiveFlagGeometry.GeometricFlags

end
