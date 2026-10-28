module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeSylowContainment.SolvableOrder
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeObstruction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint
public import Mathlib.GroupTheory.IndexNormal

/-!
# The binary derived G₂ Sylow-overgroup obstruction

Let D be the actual commutator subgroup of the split-octonion model G₂(2).
A proper solvable subgroup H containing the marked Sylow two-subgroup, with
no prime divisors other than two and three, has order not divisible by nine.
Simplicity of D is retained as an inherited hypothesis.

If nine divides |H|, the known order |D| = 6048 and Sylow divisibility give
|H| = 288 or 864. The second possibility has index seven, whose faithful
coset action contradicts 6048 not dividing 7!. A solvable group of order 288
has a nontrivial two-core. Map that core into the concrete octonion group:
the proved hexagon fixed-point theorem places its normalizer in a conjugate
of a standard parabolic. The existing parabolic order obstructions then
exclude nine. Every transport uses the actual subgroup inclusions and
conjugation maps; no abstract model identification is assumed.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). The split-octonion and root conventions
are those of the licensed ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

public section

namespace Atlas.G2.BinaryParabolicPair.ThreeSylowContainment
open Subgroup LieParabolicSetup EvenLocal.NormalizerCover

private theorem derived_card : Nat.card DerivedModel = 6048 := by
  change Nat.card (commutator (Model (ZMod 2))) = 6048
  rw [commutator_eq_longRootClosure]
  exact BinaryException.card_H

private theorem not_card_864 [IsSimpleGroup DerivedModel]
    (H : Subgroup DerivedModel) (hH : H ≠ ⊤) : Nat.card H ≠ 864 := by
  intro hc
  have hi : H.index = 7 := by
    have he := H.card_mul_index
    rw [hc, derived_card] at he
    omega
  have hb : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hH (top_unique (h ▸ H.normalCore_le)))
  have hd : H.normalCore.index ∣ H.index.factorial := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (MulAction.toPermHom DerivedModel (DerivedModel ⧸ H)).range
  rw [hb, index_bot, derived_card, hi] at hd
  norm_num at hd

private theorem card_288_of_nine_dvd [IsSimpleGroup DerivedModel]
    (H : Subgroup DerivedModel) (hH : H ≠ ⊤)
    (hU : (derivedSylow : Subgroup DerivedModel) ≤ H)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3)
    (h9 : 9 ∣ Nat.card H) : Nat.card H = 288 := by
  have h32 : 32 ∣ Nat.card H :=
    (derivedSylow.pow_dvd_card_of_pow_dvd_card
      (show (2 : ℕ)^5 ∣ Nat.card DerivedModel by rw [derived_card]; decide)).trans
      (card_dvd_of_le hU)
  have h7 : ¬ 7 ∣ Nat.card H := by
    intro hd
    have := hprimes 7 (by decide) hd
    omega
  have h288 : 288 ∣ Nat.card H :=
    (show Nat.Coprime 32 9 by decide).mul_dvd_of_dvd_of_dvd h32 h9
  obtain ⟨k, hk⟩ := h288
  have hk21 : k ∣ 21 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 288)).mp
    have hd := H.card_subgroup_dvd_card
    rw [derived_card, hk] at hd
    exact hd
  have hkc : k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 21 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 21) hk21
    interval_cases k <;> norm_num at *
  rcases hkc with rfl | rfl | rfl | rfl
  · simpa using hk
  · exact False.elim (not_card_864 H hH hk)
  · exact False.elim (h7 (by rw [hk]; decide))
  · exact False.elim (h7 (by rw [hk]; decide))

private theorem nine_not_dvd_of_twoCore_ne_bot
    (H : Subgroup DerivedModel) (hcore : pCore 2 H ≠ ⊥) : ¬ 9 ∣ Nat.card H := by
  let f : H →* Model (ZMod 2) := DerivedModel.subtype.comp H.subtype
  have hf : Function.Injective f := DerivedModel.subtype_injective.comp H.subtype_injective
  let Q : Subgroup (Model (ZMod 2)) := (pCore 2 H).map f
  have hQ : Q ≠ ⊥ := fun h => hcore
    (((pCore 2 H).map_eq_bot_iff_of_injective hf).mp h)
  have hpQ : IsPGroup 2 Q := pCore_isPGroup.map f
  obtain ⟨v, hv⟩ := normalizer_fixed_vertex_of_fixed_edge
    OctonionHexagon.hexagonData Q hQ hpQ (exists_fixed_edge Q hpQ)
  have hnorm (h : H) : f h ∈ normalizer (Q : Set (Model (ZMod 2))) := by
    apply (pCore 2 H).le_normalizer_map f
    apply mem_map.mpr
    exact ⟨h, by rw [normalizer_eq_top]; trivial, rfl⟩
  obtain ⟨g, hg⟩ := normalizer_conjugate_le_of_fixed_vertex Q v hv
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hf
  have hcard : Nat.card j.range = Nat.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  intro h9
  rcases hg with hfirst | hsecond
  · apply ThreeObstruction.first_nine_not_dvd
    have hle : j.range ≤ firstParabolic := by
      rw [← parabolic₁_binary]
      rintro _ ⟨h, rfl⟩
      exact hfirst (mem_map.mpr ⟨f h, hnorm h, rfl⟩)
    exact h9.trans (hcard ▸ card_dvd_of_le hle)
  · apply ThreeObstruction.second_nine_not_dvd
    have hle : j.range ≤ BinaryCore.secondParabolic := by
      rintro _ ⟨h, rfl⟩
      exact hsecond (mem_map.mpr ⟨f h, hnorm h, rfl⟩)
    exact h9.trans (hcard ▸ card_dvd_of_le hle)

/-- A proper solvable two-and-three-prime overgroup of the actual derived
binary Sylow subgroup has order not divisible by nine. -/
theorem nine_not_dvd_card_of_sylow_le [IsSimpleGroup DerivedModel]
    (H : Subgroup DerivedModel) (hH : H ≠ ⊤) (hs : Group.IsSolvable H)
    (hU : (derivedSylow : Subgroup DerivedModel) ≤ H)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) :
    ¬ 9 ∣ Nat.card H := by
  intro h9
  have hc := card_288_of_nine_dvd H hH hU hprimes h9
  exact nine_not_dvd_of_twoCore_ne_bot H (twoCore_ne_bot_of_card_288 H hs hc) h9

end Atlas.G2.BinaryParabolicPair.ThreeSylowContainment
