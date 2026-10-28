module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SylowCubic
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Capturing the cubic through the actual offender intersection

Let I be a normal subgroup with the recovered parity-actor coordinates.
A Sylow-normalized two-perfect subgroup R with order dividing 3 times a
power of two need not initially lie in I. Its nontrivial binary-plane
image and the full commutator [X,C] = X force the same cubic image on
R ∩ I. The two-residual of that intersection is normalized by the actual
Sylow intersection. The checked parity restriction identifies it with X;
two-perfectness then removes the two-group quotient R/X.

Only the plane action extends to the ambient group. No ambient parity
isomorphism or subnormality of R is assumed. The marked star application
in `OuterAction` supplies every premise on the original quotient.

Source: Aschbacher–Smith, B.5.7 and 13.6.13, printed pp.106 and 929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.OuterIntersection

private theorem image_three {D : Type*} [Group D] [Finite D]
    (f : D →* Equiv.Perm (Fin 3)) (R : Subgroup D) (hp : IsPPerfect 2 R)
    (hne : R.map f ≠ ⊥) : R.map f = alternatingGroup (Fin 3) := by
  have hp' := hp.of_surjective (f.subgroupMap R) (f.subgroupMap_surjective R)
  have hle := le_pResidual_of_isPPerfect (R.map f) hp'
  rw [Equiv.Perm.twoResidual_eq_alternating] at hle
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd : Nat.card (R.map f) ∣ 3 := by
    simpa only [hc] using card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact (hne ((card_le_one_iff_eq_bot _).mp h.le)).elim
  · exact eq_of_le_of_card_ge hle (by rw [h, hc])

private theorem eq_cubic_of_contains {D : Type*} [Group D]
    (X R : Subgroup D) [X.Normal] (hX : Nat.card X = 3)
    (hp : IsPPerfect 2 R) (hle : X ≤ R)
    {n : ℕ} (hc : Nat.card R ∣ 3 * 2 ^ n) : R = X := by
  let N := X.subgroupOf R
  have hN : Nat.card N = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hX
  have hd : N.index ∣ 2 ^ n := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3)
    have hh : 3 * N.index = Nat.card R := by simpa only [hN] using N.card_mul_index
    rw [hh]
    exact hc
  have ht := hp N inferInstance (IsPGroup.of_card_dvd_pow hd)
  apply le_antisymm _ hle
  intro r hr
  exact (show (⟨r, hr⟩ : R) ∈ N from ht.symm ▸ mem_top _)

/-- The residual of the actual intersection supplies the parity-actor input.
Only the plane action is extended to the original ambient group. -/
theorem eq_cubic_of_plane_action {D : Type*} [Group D] [Finite D]
    (I : Subgroup D) [I.Normal] (e : I ≃* SixPoint.Actor)
    (X R C : Subgroup D) [X.Normal]
    (hXI : X ≤ I) (hX : Nat.card X = 3) (hpX : IsPPerfect 2 X)
    (hmark : (X.subgroupOf I).map e.toMonoidHom = SixPoint.cubic)
    (P : Sylow 2 D) (hn : (P : Subgroup D) ≤ normalizer (R : Set D))
    (hCI : C ≤ I) (hCP : C ≤ P) (hfull : ⁅X, C⁆ = X)
    (hp : IsPPerfect 2 R) {n : ℕ} (hc : Nat.card R ∣ 3 * 2 ^ n)
    (f : D →* Equiv.Perm (Fin 3))
    (hker : ∀ i : I, f i = 1 ↔ SixPoint.secondProjection (e i) = 1)
    (hfX : X.map f ≠ ⊥) (hfR : R.map f ≠ ⊥) : R = X := by
  let H := R.subgroupOf I
  let B := (pResidual 2 H).map H.subtype
  let fi := f.comp I.subtype
  have hRf := image_three f R hp hfR
  have hXf := image_three f X hpX hfX
  have hcomm : ⁅R, C⁆ ≤ R ⊓ I :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (hCP.trans hn))
      ((commutator_mono le_rfl hCI).trans (commutator_le_right R I))
  have hHf : H.map fi = alternatingGroup (Fin 3) := by
    have hsub : H.map fi = (R ⊓ I).map f := by
      dsimp only [fi]
      rw [← map_map, subgroupOf_map_subtype]
    rw [hsub]
    apply le_antisymm
    · exact (map_mono inf_le_left).trans hRf.le
    · have he : ⁅R, C⁆.map f = alternatingGroup (Fin 3) := by
        rw [map_commutator, hRf, ← hXf, ← map_commutator, hfull, hXf]
      exact he.symm.le.trans (map_mono hcomm)
  have hpHf : IsPPerfect 2 (H.map fi) := by
    rw [hHf, ← Equiv.Perm.twoResidual_eq_alternating]
    exact isPPerfect_pResidual 2
  have hBf : B.map fi = alternatingGroup (Fin 3) := by
    change ((pResidual 2 H).map H.subtype).map fi = _
    rw [map_embedded_pResidual, (pResidual_eq_top_iff 2 _).mpr hpHf,
      ← MonoidHom.range_eq_map, range_subtype, hHf]
  have hBne : (B.map e.toMonoidHom).map SixPoint.secondProjection ≠ ⊥ := by
    intro hz
    have hz' : B.map fi = ⊥ := by
      apply (map_eq_bot_iff B).mpr
      intro b hb
      apply (hker b).mpr
      exact (show SixPoint.secondProjection (e b) ∈ (⊥ : Subgroup _) from
        hz ▸ mem_map_of_mem _ (mem_map_of_mem _ hb))
    rw [hBf] at hz'
    have hh := congrArg (fun A : Subgroup (Equiv.Perm (Fin 3)) => Nat.card A) hz'
    have hc3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hc1 : Nat.card (⊥ : Subgroup (Equiv.Perm (Fin 3))) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    rw [hc3, hc1] at hh
    contradiction
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal I
  have hQH : (Q : Subgroup I) ≤ normalizer (H : Set I) := by
    rw [hQ]
    intro q hq
    apply mem_normalizer_iff.mpr
    intro r
    exact mem_normalizer_iff.mp (hn hq) r
  have hQB : (Q : Subgroup I) ≤ normalizer (B : Set I) :=
    hQH.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hpB : IsPPerfect 2 (B.map e.toMonoidHom) :=
    (isPPerfect_embedded_pResidual 2 H).of_surjective
      (e.toMonoidHom.subgroupMap B) (e.toMonoidHom.subgroupMap_surjective B)
  have hcB : Nat.card (B.map e.toMonoidHom) ∣ 3 * 2 ^ n := by
    apply (card_map_dvd B _).trans
    apply (card_dvd_of_le (map_subtype_le (pResidual 2 H))).trans
    let j : H →* R := (I.subtype.comp H.subtype).codRestrict R (fun h => h.property)
    apply (card_dvd_of_injective j ?_).trans hc
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : R => (x : D)) he
  have heq := SixPoint.eq_cubic_of_sylow_normalized
    (Q.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (by rw [Sylow.coe_mapSurjective]; exact (map_mono hQB).trans (le_normalizer_map _))
    hpB hcB hBne
  have hXB : X.subgroupOf I = B := map_injective e.injective (hmark.trans heq.symm)
  apply eq_cubic_of_contains X R hX hp _ hc
  intro x hx
  have hxB : (⟨x, hXI hx⟩ : I) ∈ B := hXB ▸ hx
  exact map_subtype_le (pResidual 2 H) hxB

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.OuterIntersection
