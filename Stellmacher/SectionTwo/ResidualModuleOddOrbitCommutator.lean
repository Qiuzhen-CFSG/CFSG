module
public import Stellmacher.SectionTwo.OddConjugationOrbitCore
public import Stellmacher.PushingUp.SL2TwoCoreResidualCardFour
public import Stellmacher.SL2FrattiniUniqueMaximal

/-!
# A local residual module commutes with its odd conjugates

Let a finite local group satisfy Section Two's hypotheses, the exact
characteristic-Sylow obstruction (P), and the nested Frattini SL₂(2)
condition (A). Inject it into a finite ambient group, and let an odd-order
subgroup U normalize the image of the supplied Sylow subgroup T. Then the
image W of [O₂(G),O²(G)] commutes with each of its literal U-conjugates.
The injection, Sylow subgroup, and odd actor are retained throughout.

The local natural-data theorem gives the canonical SL₂(2) action quotient
and W₀=[V(T),G], hence W₀≤V(T). The initial core-centralizer equality makes
W₀ centralize O₂(G). The exact nested Frattini condition also gives unique
maximality above T, so the ambient conjugation form of (2.5) puts every
U-conjugate of W inside the injected local two-core. Transporting the
commutator identity under the injection proves the required commutation.
No fixed commutator line or containment in another ambient partner core is
assumed; those enter later in the source's cross-factor argument.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (4.6), p.26,
its application of (2.5); `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionTwo
universe u v

/-- The actual local core-residual module commutes with every conjugate
by the given odd-order subgroup normalizing its Sylow image. -/
public theorem local_residual_odd_conjugate_commutator_eq_bot
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (T : Sylow 2 G)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup G).subtype).Normal)
    (hA : IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G)))
    {H : Type v} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Injective f)
    (U : Subgroup H) (hU : Odd (Nat.card U))
    (hnorm : U ≤ Subgroup.normalizer (((T : Subgroup G).map f : Subgroup H) : Set H))
    (u : U) :
    let W := (⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆).map f
    ⁅W, W.conjBy (u : H)⁆ = ⊥ := by
  let _ : (vSubgroup T).Normal := Subgroup.normalClosure_normal
  let _ : (cSubgroup T).Normal := Subgroup.normal_centralizer
  obtain ⟨hbar, _, hWeq⟩ := PushingUp.sl2Two_coreResidual_card_four h T hP hA
  let W0 := ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆
  have hWV : W0 ≤ vSubgroup T := by
    rw [show W0 = ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ from rfl, hWeq]
    exact Subgroup.commutator_le_left _ _
  have hUK := isUniqueMaximalContaining_of_sl2Two_frattini T hA
  have hcore := (two_four_initial_reduction h T hP hUK).1
  have hQC : pCore 2 G ≤ Subgroup.centralizer (vSubgroup T : Set G) := by
    rw [hcore]
    exact inf_le_right
  have hWQ : ⁅W0, pCore 2 G⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hWV.trans (Subgroup.le_centralizer_iff.mp hQC))
  let q := QuotientGroup.mk' (cSubgroup T)
  have hq := QuotientGroup.mk'_surjective (cSubgroup T)
  have hker : q.ker = cSubgroup T := QuotientGroup.ker_mk' _
  have horbit := odd_conjugation_orbit_le_core h T hP hUK q hq hker hbar
    f hf U hU hnorm W0 hWV
  have hconj : (W0.map f).conjBy (u : H) ≤ (pCore 2 G).map f := by
    rintro y ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact horbit (Subgroup.subset_closure ⟨u, ⟨w, hw⟩, rfl⟩)
  have hmap : ⁅W0.map f, (pCore 2 G).map f⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, hWQ, Subgroup.map_bot]
  change ⁅W0.map f, (W0.map f).conjBy (u : H)⁆ = ⊥
  exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hconj).trans_eq hmap)

end Stellmacher.SectionTwo
