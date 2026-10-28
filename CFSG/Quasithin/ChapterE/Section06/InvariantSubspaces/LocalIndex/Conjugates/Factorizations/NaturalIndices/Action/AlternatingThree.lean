module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Action.Projection
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The actual binary plane action of an A₃ block

When the supplied central layer is trivial, the alternating module model gives
an elementary commutator group of order four. A two-group acting on that plane
fixes a nonzero vector. Choose that vector as the first basis vector; every
automorphism fixing it is a binary shear. Thompson escape from O₂(H), together
with the supplied centralizer bound, makes the Baumann action nontrivial, so
its parameter fills ZMod 2. The projection is an isomorphism on the actual U,
and the parameter kernel is its full centralizer in S.

This proves the A₃ coordinate contract with its explicit central-layer premise.
It neither proves that premise nor invokes the rank-one Baumann theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),(4),
printed p.155, and C.5.6 (*), printed p.156.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

private abbrev Plane := Multiplicative (Fin 2 → ZMod 2)
private def first : Plane := Multiplicative.ofAdd ![1, 0]
private def second : Plane := Multiplicative.ofAdd ![0, 1]
private def shear (t : ZMod 2) (v : Plane) : Plane :=
  Multiplicative.ofAdd ![v.toAdd 0 + t * v.toAdd 1, v.toAdd 1]

private def basisChange (i : Fin 3) (v : Plane) : Plane :=
  if i = 0 then v else if i = 1 then Multiplicative.ofAdd ![v.toAdd 1, v.toAdd 0]
  else Multiplicative.ofAdd ![v.toAdd 0, v.toAdd 0 + v.toAdd 1]

set_option synthInstance.maxSize 1024 in
private theorem move_to_first : ∀ v : Plane, v ≠ 1 →
    ∃ i : Fin 3, Function.Bijective (basisChange i) ∧ basisChange i 1 = 1 ∧
      (∀ x y, basisChange i (x * y) = basisChange i x * basisChange i y) ∧
      basisChange i v = first := by
  decide +kernel

private theorem fixing_first (f : Plane → Plane) (hf : Function.Injective f)
    (h1 : f 1 = 1) (hm : ∀ x y, f (x * y) = f x * f y) (hfirst : f first = first)
    (v : Plane) : f v = shear ((f second).toAdd 0) v := by
  have hw1 : f second ≠ 1 := fun hh =>
    (show second ≠ 1 from by decide) (hf (hh.trans h1.symm))
  have hwf : f second ≠ first := fun hh =>
    (show second ≠ first from by decide) (hf (hh.trans hfirst.symm))
  have hw : ∀ w : Plane, w ≠ 1 → w ≠ first →
      w = shear (w.toAdd 0) second ∧ first * w = shear (w.toAdd 0) (first * second) :=
    by decide +kernel
  have hv : v = 1 ∨ v = first ∨ v = second ∨ v = first * second := by
    exact (show ∀ x : Plane, x = 1 ∨ x = first ∨ x = second ∨ x = first * second from
      by decide +kernel) v
  rcases hv with rfl | rfl | rfl | rfl
  · rw [h1]
    exact (show ∀ t, (1 : Plane) = shear t 1 from by decide +kernel) _
  · rw [hfirst]
    exact (show ∀ t, first = shear t first from by decide +kernel) _
  · exact (hw _ hw1 hwf).1
  · rw [hm, hfirst]
    exact (hw _ hw1 hwf).2

private theorem shear_zero : ∀ v, shear 0 v = v := by decide +kernel
private theorem shear_comp : ∀ t t' v, shear t (shear t' v) = shear (t + t') v :=
  by decide +kernel
private theorem shear_second : ∀ t, (shear t second).toAdd 0 = t := by decide +kernel

private theorem binary_action_coordinates {P : Type*} [Group P]
    (hp : IsPGroup 2 P) (ρ : P →* MulAut Plane)
    (hn : ∃ s, ρ s ≠ 1) :
    ∃ (e : Plane ≃* Plane) (t : P →* Multiplicative (ZMod 2)),
      Function.Surjective t ∧ (∀ s, t s = 1 ↔ ρ s = 1) ∧
      ∀ s v, e (ρ s v) = shear (t s).toAdd (e v) := by
  classical
  let : MulAction P Plane := MulAction.compHom Plane ρ
  have hz : (1 : Plane) ∈ MulAction.fixedPoints P Plane := by
    rw [MulAction.mem_fixedPoints]
    intro s
    exact map_one (ρ s)
  obtain ⟨w, hw, hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point Plane
    (by norm_num [Plane, Nat.card_eq_fintype_card] : 2 ∣ Nat.card Plane) hz
  obtain ⟨i, hf, hf1, hfm, hfw⟩ := move_to_first w (Ne.symm hne)
  let e : Plane ≃* Plane := MulEquiv.ofBijective
    (show Plane →* Plane from ⟨⟨basisChange i, hf1⟩, hfm⟩) hf
  let τ : P →* MulAut Plane := (MulAut.congr e).toMonoidHom.comp ρ
  have hτw (s : P) : τ s first = first := by
    change e (ρ s (e.symm first)) = first
    have hew : e w = first := hfw
    rw [← hew, e.symm_apply_apply]
    exact congrArg e (MulAction.mem_fixedPoints.mp hw s)
  have heq (s : P) (v : Plane) : τ s v = shear ((τ s second).toAdd 0) v :=
    fixing_first (τ s) (τ s).injective (map_one _) (map_mul _) (hτw s) v
  let t : P →* Multiplicative (ZMod 2) :=
    { toFun := fun s => Multiplicative.ofAdd ((τ s second).toAdd 0)
      map_one' := by simp [second]
      map_mul' := by
        intro s r
        change (τ (s * r) second).toAdd 0 =
          (τ s second).toAdd 0 + (τ r second).toAdd 0
        rw [map_mul]
        change (τ s (τ r second)).toAdd 0 = _
        rw [heq s, heq r, shear_comp]
        simp only [shear_second] }
  have hker (s : P) : t s = 1 ↔ ρ s = 1 := by
    have heker : t s = 1 ↔ τ s = 1 := by
      constructor
      · intro hs
        have hs' : (τ s second).toAdd 0 = 0 := hs
        ext v
        rw [heq, hs', shear_zero]
        rfl
      · intro hs
        change (τ s second).toAdd 0 = 0
        rw [hs]
        rfl
    rw [heker]
    exact (MulAut.congr e).map_eq_one_iff
  have hsurj : Function.Surjective t := by
    obtain ⟨s, hs⟩ := hn
    have ht : t s ≠ 1 := fun ht => hs ((hker s).mp ht)
    have ht1 : (t s).toAdd = 1 := by
      exact (show ∀ z : ZMod 2, z ≠ 0 → z = 1 from by decide) _ ht
    intro z
    have hz : z.toAdd = 0 ∨ z.toAdd = 1 := by
      exact (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) z.toAdd
    rcases hz with hz | hz
    · refine ⟨1, ?_⟩
      rw [map_one]
      exact hz.symm
    · exact ⟨s, ht1.trans hz.symm⟩
  refine ⟨e, t, hsurj, hker, ?_⟩
  intro s v
  have he := heq s (e v)
  change e (ρ s (e.symm (e v))) = shear (t s).toAdd (e v) at he
  simpa only [e.symm_apply_apply] using he

private theorem binary_module_equiv {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : ChapterC.IsAlternatingBlock L 3) (hz : ChapterC.blockFixed L = ⊥) :
    Nonempty (U L ≃* Plane) := by
  classical
  let _ : IsElementaryAbelian 2 (U L) := hL.2.1.elementary.map L.subtype
  have hc : Nat.card (U L) = 4 := by
    have hq := hL.module_card_odd (by decide)
    have e := (QuotientGroup.quotientMulEquivOfEq hz).trans
      (QuotientGroup.quotientBot.trans (intrinsicModuleEquiv L))
    exact (Nat.card_congr e.toEquiv).symm.trans hq
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive (U L)) = 2 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (U L))
    change Nat.card (U L) = _ at hsize
    simpa only [Nat.card_zmod, hc, show 2 ^ 2 = 4 from rfl] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive (U L)) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive (U L)) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

private theorem thompson_le_S {G : Type*} [Group G] (R : Subgroup G) :
    Stellmacher.elementaryAbelianMaxJ R ≤ S R := by
  refine le_inf (sSup_le fun _ hE => hE.1) ?_
  intro j hj
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨wJ, hwJ, rfl⟩ := hw
  obtain ⟨wZ, _, rfl⟩ := hwJ
  exact congrArg Subtype.val
    ((mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm

private theorem baumann_moves_module {G : Type*} [Group G] [Finite G]
    {K : GroupClass} {A H R L : Subgroup G} (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) : ¬ S R ≤ centralizer (U L : Set G) := by
  intro hc
  apply Baumann.thompson_not_le_HCore h
  exact (le_inf (sSup_le fun _ hE => hE.1) ((thompson_le_S R).trans hc)).trans hb.centralizer_le

/-- The full Baumann action on the actual A₃ commutator module has binary shear coordinates. -/
theorem alternatingThreeCoordinatesInput {G : Type*} [Group G] [Finite G]
    (K : GroupClass) : AlternatingThreeCoordinatesInput (G := G) K := by
  intro A H R L h hb hL hz
  obtain ⟨e₀⟩ := binary_module_equiv hL hz
  have hnorm : S R ≤ normalizer (U L : Set G) :=
    (show S R ≤ R from inf_le_left).trans (R_normalizes_U h)
  let σ : S R →* MulAut (U L) := (U L).normalizerMonoidHom.comp (inclusion hnorm)
  let ρ : S R →* MulAut Plane := (MulAut.congr e₀).toMonoidHom.comp σ
  have hk (s : S R) : ρ s = 1 ↔ (s : G) ∈ centralizer (U L : Set G) := by
    change MulAut.congr e₀ (σ s) = 1 ↔ _
    rw [(MulAut.congr e₀).map_eq_one_iff]
    change inclusion hnorm s ∈ (U L).normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hp : IsPGroup 2 (S R) :=
    (Chapter1.isSylowIn_iff.mp h.sylow).1.to_le inf_le_left
  have hne : ∃ s, ρ s ≠ 1 := by
    by_contra! he
    exact baumann_moves_module h hb (fun s hs => (hk ⟨s, hs⟩).mp (he ⟨s, hs⟩))
  obtain ⟨e, t, ht, htk, he⟩ := binary_action_coordinates hp ρ hne
  refine ⟨{
    normalizes := hnorm
    parameter := t
    parameter_surjective := ht
    parameter_kernel := fun s => (htk s).trans (hk s)
    projection := (e₀.trans e).toMonoidHom
    projection_surjective := (e₀.trans e).surjective
    projection_kernel := ?_
    equivariant := ?_ }⟩
  · intro v
    exact (e₀.trans e).map_eq_one_iff.trans (centralizer_iff_eq_one_of_blockFixed_eq_bot hz v).symm
  · intro s v
    have he' := he s (e₀ v)
    change e (e₀ (σ s (e₀.symm (e₀ v)))) = shear (t s).toAdd (e (e₀ v)) at he'
    rw [e₀.symm_apply_apply] at he'
    exact congrArg Multiplicative.toAdd he'

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

end
