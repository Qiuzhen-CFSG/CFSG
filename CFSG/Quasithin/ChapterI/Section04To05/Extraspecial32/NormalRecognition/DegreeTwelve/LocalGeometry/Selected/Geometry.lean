module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Intersection.Cardinality

/-!
# Geometry for the selected fusion configuration

The published degree-twelve intersection is definitionally the same literal
left-conjugate intersection used in the earlier local calculation. No
quaternion-nonnormality hypothesis is used by those intersection lemmas.

Saturation of its sharp set is equivalent to equality with the canonical
fusion eight. Conjugation by the involution centralizer preserves failure
of this equality. Two distinct such eights meet in a four-group: their
intersection contains the distinct nonidentity elements z and g*z*g⁻¹,
and its order is a proper divisor of eight.

The inverter contract isolates the remaining source selection, retaining
the original chosen Sylow three-subgroup and the literal conjugate core.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.4, 2.8 and 4.1.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The marked involution part of source 2.4 and 4.1. Its producer may
arrange g by left multiplication in C_G(z), but must invert the given h.X. -/
public structure InverterData (h : Hypotheses z) (g : G) where
  u : G
  u_order : orderOf u = 2
  u_centralizes : u ∈ Centralizer z
  u_conjugate_core : u ∈ conjugateCore z g
  u_not_core : u ∉ coreInG z
  u_fused : IsConj z u
  u_inverts_X : ∀ x : h.X,
    u * ((x : Centralizer z) : G) * u⁻¹ = ((x : Centralizer z) : G)⁻¹

/-- The exact source sharp-set equality is equivalent to equality of the two eights. -/
public theorem fusionSaturated_iff (h : Hypotheses z) (d : FusionEightData z) (g : G) :
    NonnormalRecognition.FusionSaturated z g ↔ coreIntersection z g = fusionCore z := by
  constructor
  · intro hs
    ext x
    exact (hs.mem_iff x).trans (d.mem_iff x).symm
  · intro he x
    change (x ∈ coreIntersection z g ∧ x ≠ 1) ↔ _
    rw [he]
    constructor
    · rintro ⟨hx, hx1⟩
      exact ⟨fusionCore_le z hx, d.fusion x hx hx1⟩
    · rintro ⟨hx, hc⟩
      refine ⟨subset_closure ⟨hx, hc⟩, ?_⟩
      intro hx1
      have ho : orderOf x = 2 := by
        obtain ⟨a, rfl⟩ := isConj_iff.mp hc
        exact ((MulAut.conj a).orderOf_eq z).trans h.involution
      simp [hx1] at ho

/-- Conjugation in H preserves the canonical fusion eight. -/
public theorem fusionCore_map_conj (h : Hypotheses z) {a : G} (ha : a ∈ Centralizer z) :
    (fusionCore z).map (MulAut.conj a).toMonoidHom = fusionCore z :=
  mem_normalizer_iff_map_conj_eq.mp (h.centralizer_le_normalizer_fusionCore ha)

/-- Arranging the conjugator within H preserves the distinction from the fusion eight. -/
public theorem intersection_ne_fusion_of_conj (h : Hypotheses z) {a : G}
    (ha : a ∈ Centralizer z) (g : G) (hne : coreIntersection z g ≠ fusionCore z) :
    coreIntersection z (a * g) ≠ fusionCore z := by
  intro he
  apply hne
  apply (map_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective)
  change (NonnormalRecognition.coreIntersection z g).map _ = _
  rw [NonnormalRecognition.coreIntersection_map_conj h ha]
  exact he.trans (fusionCore_map_conj h ha).symm

/-- Left multiplication by H preserves both clauses of the original fusion witness. -/
public theorem conjugated_fusion_witness (h : Hypotheses z) {a : G}
    (ha : a ∈ Centralizer z) (g : G)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z) :
    (a * g) * z * (a * g)⁻¹ ∈ coreInG z ∧ (a * g) * z * (a * g)⁻¹ ≠ z := by
  have he : (a * g) * z * (a * g)⁻¹ = (MulAut.conj a) (g * z * g⁻¹) := by
    simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]
  have haz : (MulAut.conj a) z = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp ha)
  rw [he]
  refine ⟨?_, fun hx => hg ((MulAut.conj a).injective (hx.trans haz.symm))⟩
  exact (mem_normalizer_iff.mp (h.normalizer_core.symm ▸ ha) _).mp hgQ

omit [Finite G] in
/-- The conjugated fusion eight has exactly the ambient z-conjugates in the conjugate core. -/
public theorem mem_conjugate_fusion_iff (d : FusionEightData z) (g x : G) :
    x ∈ (fusionCore z).map (MulAut.conj g).toMonoidHom ↔
      x = 1 ∨ (x ∈ conjugateCore z g ∧ IsConj z x) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (d.mem_iff y).mp hy with rfl | ⟨hyQ, hf⟩
    · exact Or.inl (map_one _)
    · exact Or.inr ⟨mem_map_of_mem _ hyQ, hf.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩
  · rintro (rfl | ⟨⟨y, hy, rfl⟩, hf⟩)
    · exact one_mem _
    · refine mem_map_of_mem _ (subset_closure ⟨hy, ?_⟩)
      exact hf.trans (isConj_iff.mpr (show ∃ a : G, a * y * a⁻¹ = (MulAut.conj g) y
        from ⟨g, rfl⟩)).symm

/-- An intersection different from F is also different from its left conjugate Fᵍ. -/
public theorem intersection_ne_conjugate_fusion (h : Hypotheses z) (d : FusionEightData z)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hne : coreIntersection z g ≠ fusionCore z) :
    coreIntersection z g ≠ (fusionCore z).map (MulAut.conj g).toMonoidHom := by
  intro he
  apply hne
  apply eq_of_le_of_card_ge
  · intro x hx
    rcases (mem_conjugate_fusion_iff d g x).mp (he ▸ hx) with rfl | hxF
    · exact (fusionCore z).one_mem
    · exact subset_closure ⟨hx.1, hxF.2⟩
  · exact (d.card.trans (NonnormalRecognition.coreIntersection_card h g hgQ hg).symm).le

/-- The two distinct elementary eights meet in a four-group, as required in source 4.1. -/
public theorem intersection_fusion_card (h : Hypotheses z) (d : FusionEightData z)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hne : coreIntersection z g ≠ fusionCore z) :
    Nat.card (coreIntersection z g ⊓ fusionCore z : Subgroup G) = 4 := by
  classical
  let V := coreIntersection z g ⊓ fusionCore z
  have hzV : z ∈ V := ⟨NonnormalRecognition.involution_mem_coreIntersection h g hgQ hg,
    h.involution_mem_fusionCore⟩
  have hsV : g * z * g⁻¹ ∈ V :=
    ⟨NonnormalRecognition.conjugate_mem_coreIntersection h g hgQ,
      subset_closure ⟨hgQ, isConj_iff.mpr ⟨g, rfl⟩⟩⟩
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hs1 : g * z * g⁻¹ ≠ 1 := fun he => hz1 ((MulAut.conj g).map_eq_one_iff.mp he)
  let f : Fin 3 → V := ![1, ⟨z, hzV⟩, ⟨g * z * g⁻¹, hsV⟩]
  have hf : Function.Injective f := by
    intro i j he
    have hv := congrArg (fun v : V => (v : G)) he
    fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm]
  have hlo : 3 ≤ Nat.card V := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have hd : Nat.card V ∣ 8 := d.card ▸ card_dvd_of_le (show V ≤ fusionCore z from inf_le_right)
  have hE : Nat.card (coreIntersection z g) = 8 :=
    NonnormalRecognition.coreIntersection_card h g hgQ hg
  have hn8 : Nat.card V ≠ 8 := by
    intro h8
    have hVE : V = coreIntersection z g := eq_of_le_of_card_ge inf_le_left
      (by rw [h8, hE])
    exact hne (eq_of_le_of_card_ge (hVE ▸ (show V ≤ fusionCore z from inf_le_right))
      (by rw [d.card, hE]))
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card V ∣ 2 ^ 3 from hd)
  change Nat.card V = 4
  interval_cases k
  · have h1 : Nat.card V = 1 := hcard
    omega
  · have h2 : Nat.card V = 2 := hcard
    omega
  · exact hcard
  · exact False.elim (hn8 hcard)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
