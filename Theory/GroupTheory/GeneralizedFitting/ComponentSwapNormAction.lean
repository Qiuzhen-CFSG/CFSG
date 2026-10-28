module

public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapDiagonal
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Automorphisms of a component norm pair

An element commuting with the swapping involution preserves the norm image
whenever it preserves the component pair. If it normalizes the first component
and centralizes the norm image, perfectness lifts trivial action across the
norm's central kernel. If it sends the first component outside the pair, its
conjugate norm image commutes with the original one.

These are the action comparisons in GLS2, Chapter B, Lemma 3.27(ix), and
Chapter G, Theorem 25.14, Step 3. No direct-product assumption is made.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.NormPair
variable {G : Type*} [Group G] {L : Subgroup G} {a : G}
  (hL : IsComponent G L) (hm : L.map (MulAut.conj a).toMonoidHom ≠ L)

abbrev normRange : Subgroup G := (componentSwapNorm hL hm).range

private lemma conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

lemma norm_le_pair : normRange hL hm ≤ L ⊔ L.map (MulAut.conj a).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact mul_mem (mem_sup_left x.property) (mem_sup_right (mem_map_of_mem _ x.property))

private lemma conj_comm {b : G} (hb : Commute b a) (x : G) :
    MulAut.conj b (MulAut.conj a x) = MulAut.conj a (MulAut.conj b x) := by
  change b * (a * x * a⁻¹) * b⁻¹ = a * (b * x * b⁻¹) * a⁻¹
  calc
    _ = (b * a) * x * (b * a)⁻¹ := by group
    _ = (a * b) * x * (a * b)⁻¹ := by rw [hb.eq]
    _ = _ := by group

lemma normalizes_norm {b : G} (hb : Commute b a)
    (hN : b ∈ normalizer (L : Set G)) : b ∈ normalizer (normRange hL hm : Set G) := by
  apply mem_normalizer_iff.mpr
  intro z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨L.normalizerMonoidHom ⟨b, hN⟩ x, ?_⟩
    change MulAut.conj b (x : G) * MulAut.conj a (MulAut.conj b (x : G)) =
      MulAut.conj b ((x : G) * MulAut.conj a (x : G))
    rw [map_mul, conj_comm hb]
  · rintro ⟨x, hx⟩
    refine ⟨L.normalizerMonoidHom ⟨b⁻¹, inv_mem hN⟩ x, ?_⟩
    change MulAut.conj b⁻¹ (x : G) * MulAut.conj a (MulAut.conj b⁻¹ (x : G)) = z
    rw [← conj_comm hb.inv_left, ← map_mul]
    change b⁻¹ * ((x : G) * (a * x * a⁻¹)) * (b⁻¹)⁻¹ = z
    change (x : G) * (a * x * a⁻¹) = b * z * b⁻¹ at hx
    rw [hx]
    group

lemma centralizes_norm_normalizes_component {b : G} (hb : Commute b a)
    (hN : b ∈ normalizer (L : Set G))
    (hC : b ∈ Subgroup.centralizer (normRange hL hm : Set G)) : b ∈ Subgroup.centralizer (L : Set G) := by
  let := hL.2
  let f := L.normalizerMonoidHom ⟨b, hN⟩
  have hf : (componentSwapNorm hL hm).comp f.toMonoidHom =
      (componentSwapNorm hL hm).comp (MonoidHom.id L) := by
    ext x
    change MulAut.conj b (x : G) * MulAut.conj a (MulAut.conj b (x : G)) =
      componentSwapNorm hL hm x
    rw [← conj_comm hb, ← map_mul]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp hC _ ⟨x, rfl⟩).symm
  have he := PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    (componentSwapNorm hL hm) (componentSwapNorm_ker_le_center hL hm)
    f.toMonoidHom (MonoidHom.id L) hf
  apply mem_centralizer_iff.mpr
  intro x hx
  have hx' := congrArg (fun u : L →* L => (u ⟨x, hx⟩ : G)) he
  change b * x * b⁻¹ = x at hx'
  exact (mul_inv_eq_iff_eq_mul.mp hx').symm

lemma conjugate_norm_centralizes_of_outside_pair (ha : a ^ 2 = 1)
    {b : G} (hb : Commute b a)
    (hbL : L.map (MulAut.conj b).toMonoidHom ≠ L)
    (hbLa : L.map (MulAut.conj b).toMonoidHom ≠
      L.map (MulAut.conj a).toMonoidHom) :
    (normRange hL hm).map (MulAut.conj b).toMonoidHom ≤ Subgroup.centralizer (normRange hL hm : Set G) := by
  have hLc : L ⊔ L.map (MulAut.conj a).toMonoidHom ≤
      Subgroup.centralizer (L.map (MulAut.conj b).toMonoidHom : Set G) :=
    sup_le (commutator_eq_bot_iff_le_centralizer.mp
      (hL.commutator_eq_bot_of_ne (hL.map_conj b) hbL.symm))
      (commutator_eq_bot_iff_le_centralizer.mp
        ((hL.map_conj a).commutator_eq_bot_of_ne (hL.map_conj b) hbLa.symm))
  have hbc : L.map (MulAut.conj b).toMonoidHom ≤ Subgroup.centralizer (normRange hL hm : Set G) :=
    le_centralizer_iff.mp ((norm_le_pair hL hm).trans hLc)
  have haC : a ∈ Subgroup.centralizer (normRange hL hm : Set G) := by
    exact mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_singleton_iff.mp
        (componentSwapNorm_range_le_centralizer hL hm ha hx))
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  change MulAut.conj b ((x : G) * MulAut.conj a (x : G)) ∈ _
  rw [map_mul, conj_comm hb]
  exact mul_mem (hbc (mem_map_of_mem _ x.property))
    ((mem_normalizer_iff.mp ((Subgroup.centralizer (normRange hL hm : Set G)).le_normalizer haC) _).mp
      (hbc (mem_map_of_mem _ x.property)))

lemma normalizes_norm_of_pair (ha : a ^ 2 = 1) {b : G} (hb : Commute b a)
    (hpair : L.map (MulAut.conj b).toMonoidHom = L ∨
      L.map (MulAut.conj b).toMonoidHom = L.map (MulAut.conj a).toMonoidHom) :
    b ∈ normalizer (normRange hL hm : Set G) := by
  rcases hpair with h | h
  · exact normalizes_norm hL hm hb (mem_normalizer_iff_map_conj_eq.mpr h)
  · have haa : a * a = 1 := by simpa [pow_two] using ha
    have hN : a * b ∈ normalizer (L : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change L.map (MulAut.conj (a * b)).toMonoidHom = L
      rw [conj_mul, h, ← conj_mul, haa]
      convert L.map_id using 1
      ext x
      simp
    have haC : a ∈ Subgroup.centralizer (normRange hL hm : Set G) :=
      mem_centralizer_iff.mpr fun x hx =>
        (mem_centralizer_singleton_iff.mp
          (componentSwapNorm_range_le_centralizer hL hm ha hx))
    have hab : a * b ∈ normalizer (normRange hL hm : Set G) :=
      normalizes_norm hL hm ((Commute.refl a).mul_left hb) hN
    have hh := mul_mem (centralizer_le_normalizer _ haC) hab
    simpa only [← mul_assoc, haa, one_mul] using hh

end Theory.GroupTheory.NormPair

end
