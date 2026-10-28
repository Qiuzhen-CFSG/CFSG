module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected.Geometry


/-!
# A fused involution in the conjugate core

Reciprocity puts z in Qᵍ, hence in Fᵍ because it is conjugate to itself.
The elementary subgroup Fᵍ therefore centralizes z. If E differs from F,
it also differs from Fᵍ, so an element of Fᵍ outside E is an involution
in H ∩ Qᵍ outside Q and is fused to z.

The remaining local actor calculation conjugates this involution inside H
to invert the original chosen Sylow three-subgroup. Conjugating the entire
configuration by that same element preserves its literal marked core.
This module proves the transport with that actor calculation still explicit.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.4 and 4.1(2).
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The conjugated fusion eight supplies the marked fused involution before arranging X. -/
public theorem exists_fused_involution_in_conjugate_core (h : Hypotheses z) (d : FusionEightData z)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hne : coreIntersection z g ≠ fusionCore z) :
    ∃ u : G, orderOf u = 2 ∧ u ∈ Centralizer z ∧ u ∈ conjugateCore z g ∧
      u ∉ coreInG z ∧ IsConj z u := by
  classical
  let Fg := (fusionCore z).map (MulAut.conj g).toMonoidHom
  have hzFg : z ∈ Fg := (mem_conjugate_fusion_iff d g z).mpr
    (Or.inr ⟨(NonnormalRecognition.involution_mem_coreIntersection h g hgQ hg).2, IsConj.refl z⟩)
  let : IsElementaryAbelian 2 (fusionCore z) := d.elementary
  let : IsElementaryAbelian 2 Fg := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hFgH : Fg ≤ Centralizer z := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun x : Fg => (x : G))
      (mul_comm' (⟨x, hx⟩ : Fg) ⟨z, hzFg⟩)
  have hFgQ : Fg ≤ conjugateCore z g := map_mono (fusionCore_le z)
  have hnle : ¬ Fg ≤ coreIntersection z g := by
    intro hle
    apply intersection_ne_conjugate_fusion h d g hgQ hg hne
    symm
    apply eq_of_le_of_card_ge hle
    rw [card_map_of_injective (MulAut.conj g).injective, d.card]
    exact (NonnormalRecognition.coreIntersection_card h g hgQ hg).le
  obtain ⟨u, hu, huE⟩ := Set.not_subset.mp hnle
  have hu1 : u ≠ 1 := fun he => huE (he ▸ (coreIntersection z g).one_mem)
  have hf : IsConj z u := ((mem_conjugate_fusion_iff d g u).mp hu).resolve_left hu1 |>.2
  have ho : orderOf u = 2 := by
    obtain ⟨a, rfl⟩ := isConj_iff.mp hf
    exact ((MulAut.conj a).orderOf_eq z).trans h.involution
  exact ⟨u, ho, hFgH hu, hFgQ hu, fun huQ => huE ⟨huQ, hFgQ hu⟩, hf⟩

/-- Align the fused involution with h.X, transporting the entire selected core by the same element. -/
public theorem arrange_inverter_of_outside_alignment
    (h : Hypotheses z) (d : FusionEightData z)
    (alignment : ∀ u : G, orderOf u = 2 → u ∈ Centralizer z → u ∉ coreInG z →
      IsConj z u → ∃ a : Centralizer z, ∀ x : h.X,
        ((a : G) * u * (a : G)⁻¹) * ((x : Centralizer z) : G) *
          ((a : G) * u * (a : G)⁻¹)⁻¹ = ((x : Centralizer z) : G)⁻¹)
    (g : G) (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hne : coreIntersection z g ≠ fusionCore z) :
    ∃ a : Centralizer z, Nonempty (InverterData h ((a : G) * g)) := by
  obtain ⟨u, hu2, huH, huQg, huQ, huf⟩ :=
    exists_fused_involution_in_conjugate_core h d g hgQ hg hne
  obtain ⟨a, ha⟩ := alignment u hu2 huH huQ huf
  refine ⟨a, ⟨{
    u := (a : G) * u * (a : G)⁻¹
    u_order := ((MulAut.conj (a : G)).orderOf_eq u).trans hu2
    u_centralizes := (Centralizer z).mul_mem
      ((Centralizer z).mul_mem a.property huH) ((Centralizer z).inv_mem a.property)
    u_conjugate_core := ?_
    u_not_core := ?_
    u_fused := huf.trans (isConj_iff.mpr ⟨a, rfl⟩)
    u_inverts_X := ha }⟩⟩
  · obtain ⟨q, hq, he⟩ := huQg
    refine ⟨q, hq, ?_⟩
    change (a : G) * g * q * ((a : G) * g)⁻¹ = (a : G) * u * (a : G)⁻¹
    change g * q * g⁻¹ = u at he
    rw [← he]
    group
  · intro he
    exact huQ ((mem_normalizer_iff.mp (h.normalizer_core.symm ▸ a.property) u).mpr he)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Selected
