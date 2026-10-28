module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The action dimension for the binary higher-linear components

The actual conjugation action fixes a Sylow subgroup pointwise. Binary-linear
rigidity makes each such automorphism inner, with a conjugator in the center
of that Sylow subgroup. Its center has order at most two. Transport through
the field and projective matrix equivalences therefore bounds the actual
action image by two, and component escape forces action corank and r to be one.

These conclusions do not identify the kernel with U or construct the S₈
quotient. Those are distinct remaining clauses of E.6.8(3).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and 16.1.6, printed p.1172.
The field comparison uses the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes
variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G}

private noncomputable def binaryEquiv {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) : L ≃* LinearGroup n := Classical.choice <| by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e₀.trans ((Atlas.fieldEquivPSL n f.symm).trans (projectiveEquivLinear hn))⟩

private theorem binary_fixing_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : L ≃* LinearGroup n) (S : Sylow 2 L) (a : MulAut L)
    (hfix : ∀ x ∈ S, a x = x) : ∃ x ∈ S, a = MulAut.conj x := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : ∀ x ∈ R, MulAut.congr e a x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hfix y hy]
  obtain ⟨g, hg, he⟩ := sylow_fixing_inner hn R (MulAut.congr e a) hR
  obtain ⟨x, hx, rfl⟩ := hg
  refine ⟨x, hx, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj]
  exact he

/-- The full induced action image has order at most two in either binary
higher-linear model. This is a bound on actual automorphisms, not a model tag. -/
theorem binary_action_image_card_le_two {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL L n 2) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    Nat.card (inducedAutomizer L V) ≤ 2 := by
  let e := binaryEquiv (by omega : 0 < n) hm
  let J := (inducedAutomizer L V).map (Automizer L).subtype
  let c : S →* MulAut L := (MulAut.conj : L →* MulAut L).comp (S : Subgroup L).subtype
  have hJ : J ≤ (center S).map c := by
    rintro a ⟨b, ⟨v, hv, rfl⟩, rfl⟩
    have hf : ∀ x ∈ S, L.normalizerMonoidHom v x = x := by
      intro x hx
      apply Subtype.ext
      exact hfix v hv ⟨x, hx⟩
    obtain ⟨x, hx, he⟩ := binary_fixing_inner hn e S (L.normalizerMonoidHom v) hf
    refine ⟨⟨x, hx⟩, ?_, he.symm⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hy := hf y y.property
    rw [he] at hy
    change x * (y : L) * x⁻¹ = y at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm
  calc
    Nat.card (inducedAutomizer L V) = Nat.card J :=
      (Subgroup.card_map_of_injective (Automizer L).subtype_injective).symm
    _ ≤ Nat.card ((center S).map c) :=
      Nat.card_le_card_of_injective (inclusion hJ) (inclusion_injective hJ)
    _ ≤ Nat.card (center S) := Nat.le_of_dvd Nat.card_pos ((center S).card_map_dvd c)
    _ = Nat.card (center (S.mapSurjective (f := e.toMonoidHom) e.surjective)) :=
      BinaryLinear.sylow_center_card_congr e S
    _ ≤ 2 := BinaryLinear.linear_sylow_center_card_le_two (by omega) _

/-- Fixing a Sylow subgroup pointwise leaves at most one binary action dimension. -/
theorem binary_actionCorank_le_one {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL L n 2) (hN : V ≤ normalizer (L : Set G))
    (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    actionCorank V L ≤ 1 := by
  rw [actionCorank, ← rank_inducedAutomizer L V hN]
  exact (Nat.log_mono_right (binary_action_image_card_le_two hn hm S hfix)).trans (by decide)

/-- The dimension and weak-closure clauses needed by the surviving PSL₄(2)
case follow already from the common source hypotheses. The same bound is
available before excluding PSL₅(2). -/
theorem binary_component_rank_one {K : GroupClass} {T : Sylow 2 G}
    {M U : Subgroup G} (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL L n 2) :
    actionCorank V L = 1 ∧ globalR V = 1 := by
  obtain ⟨hN, S, _, hfix⟩ := component_sylow_action h hU hL rfl
  exact h.fixedSpace_corank_eq_one (component_not_le h earlier hU hL)
    (binary_actionCorank_le_one hn hm hN S hfix)

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes
