module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PanelKernel

/-!
# The exact Cartan kernel of a source simple root

A Cartan element centralizing the simple root fixes the base point of
the actual endpoint panel and every other point `r nᵢ B`. The latter
uses both root centralization and normalization of H by the selected
reflection. The kernel of the panel action is the core of its entire
Borel. Combining this with the proved reverse containment gives
`C_H(Uᵢ) = H ∩ Kᵢ = C_H(Rᵢ)` on the same source quotient.

This is the exact Cartan/kernel identification used in Fong–Seitz I,
the proof of (6H)(a), p.51, and its independent-root centralizer argument.
It does not yet prove separation for two independent roots or the product
formula for H. The actual panel chart is reused, with no perfectness
or nonbinary hypothesis.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

include split in
/-- The missing point of the root chart is the original Borel coset. -/
theorem panelBase_eq_mk_one : panelBase Q i = (QuotientGroup.mk 1 : Panel Q i) := by
  by_contra hne
  let n := representative (Q.simple i)
  obtain ⟨r,hr⟩ := (simplePanelMap_bijective Q split i n (representative_spec _)).surjective
    ⟨QuotientGroup.mk 1,Ne.symm hne⟩
  have hrep : (simplePanelMap Q split i n (representative_spec _) r).val =
      QuotientGroup.mk (rootInEndpoint Q split i r * reflectionLift Q i) := by
    rw [simplePanelMap_apply]
    rfl
  have he := congrArg Subtype.val hr
  rw [hrep] at he
  have hm := QuotientGroup.eq.mp he.symm
  change (1 : X ⧸ Q.D)⁻¹ * ((r : X ⧸ Q.D)*n) ∈ Q.tits.B at hm
  simp only [inv_one,one_mul] at hm
  have hnB : (n : X ⧸ Q.D) ∈ Q.tits.B := by
    have hh := Q.tits.B.mul_mem (Q.tits.B.inv_mem (split.U_le r.property.1)) hm
    simpa only [inv_mul_cancel_left] using hh
  have hq := (QuotientGroup.eq_one_iff n).mpr
    (show n ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N from ⟨hnB,n.property⟩)
  exact (Q.tits.involutions _ (Q.simple_mem i)).1 ((representative_spec _).symm.trans hq)

/-- A Cartan element centralizing the simple root fixes the entire literal panel. -/
theorem cartan_centralizer_fixes_panel {h : X ⧸ Q.D} (hh : h ∈ Q.tits.B ⊓ Q.tits.N)
    (hc : h ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)))
    (c : Panel Q i) :
    (⟨h, Q.tits.B_le_standardParabolic _ hh.1⟩ : Endpoint Q i) • c = c := by
  let n := representative (Q.simple i)
  let hp : Endpoint Q i := ⟨h, Q.tits.B_le_standardParabolic _ hh.1⟩
  by_cases hb : c = panelBase Q i
  · subst c
    rw [panelBase_eq_mk_one Q split i]
    change QuotientGroup.mk (hp * 1) = (QuotientGroup.mk 1 : Panel Q i)
    apply QuotientGroup.eq.mpr
    change (h*1)⁻¹*1 ∈ Q.tits.B
    simpa only [mul_one] using Q.tits.B.inv_mem hh.1
  · obtain ⟨r,hr⟩ := (simplePanelMap_bijective Q split i n (representative_spec _)).surjective ⟨c,hb⟩
    have hrep : (simplePanelMap Q split i n (representative_spec _) r).val =
        QuotientGroup.mk (rootInEndpoint Q split i r * reflectionLift Q i) := by
      rw [simplePanelMap_apply]
      rfl
    have hce : c = QuotientGroup.mk (rootInEndpoint Q split i r * reflectionLift Q i) :=
      (congrArg Subtype.val hr).symm.trans hrep
    rw [hce]
    change QuotientGroup.mk (hp * (rootInEndpoint Q split i r * reflectionLift Q i)) =
      QuotientGroup.mk (rootInEndpoint Q split i r * reflectionLift Q i)
    apply QuotientGroup.eq.mpr
    have he : h * (r : X ⧸ Q.D) = (r : X ⧸ Q.D) * h :=
      ((mem_centralizer_iff.mp hc) r r.property).symm
    have hn : (n : X ⧸ Q.D)⁻¹*h⁻¹*(n : X ⧸ Q.D) ∈ Q.tits.B := by
      have ht := (mem_normalizer_iff.mp (torus_normalizes n⁻¹) h⁻¹).mp
        ((Q.tits.B ⊓ Q.tits.N).inv_mem hh)
      change (n : X ⧸ Q.D)⁻¹*h⁻¹*((n : X ⧸ Q.D)⁻¹)⁻¹ ∈ Q.tits.B ⊓ Q.tits.N at ht
      rw [inv_inv] at ht
      exact ht.1
    change (h*((r : X ⧸ Q.D)*n))⁻¹*((r : X ⧸ Q.D)*n) ∈ Q.tits.B
    have he' : h*((r : X ⧸ Q.D)*n) = ((r : X ⧸ Q.D)*h)*n := by
      rw [← mul_assoc,he]
    rw [he']
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hn

/-- The Cartan kernel of a simple-root action is precisely its actual panel kernel. -/
theorem cartan_centralizer_simpleRoot :
    (Q.tits.B ⊓ Q.tits.N) ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) =
      (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i := by
  apply le_antisymm
  · intro h hh
    refine ⟨hh.1,?_⟩
    let hp : Endpoint Q i := ⟨h,Q.tits.B_le_standardParabolic _ hh.1.1⟩
    have hk : hp ∈ panelKernel Q i := by
      rw [panelKernel, normalCore_eq_ker, MonoidHom.mem_ker]
      apply Equiv.ext
      exact cartan_centralizer_fixes_panel Q split i hh.1 hh.2
    exact ⟨hp,hk,rfl⟩
  · intro h hh
    exact ⟨hh.1,cartanKernel_centralizes_simpleRoot Q split i hh⟩

/-- The corresponding rank-one root group has the same Cartan centralizer. -/
theorem cartan_centralizer_rankOneRootGroup :
    (Q.tits.B ⊓ Q.tits.N) ⊓ centralizer (rankOneRootGroup Q split i : Set (X ⧸ Q.D)) =
      (Q.tits.B ⊓ Q.tits.N) ⊓ embeddedPanelKernel Q i := by
  apply le_antisymm
  · rw [← cartan_centralizer_simpleRoot Q split i]
    exact inf_le_inf_left _ (centralizer_le (show
      (simpleRoot Q split i : Set (X ⧸ Q.D)) ⊆ rankOneRootGroup Q split i from
      fun _ hx => (show simpleRoot Q split i ≤ rankOneRootGroup Q split i from le_sup_left) hx))
  · apply le_inf inf_le_left
    exact le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (rankOneRootGroup_commutator_cartanKernel Q split i))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
