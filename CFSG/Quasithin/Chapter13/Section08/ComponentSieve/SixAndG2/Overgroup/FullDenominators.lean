module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Geometry
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Displacement
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Full denominators and the original transvection center in 13.8.27(3)

F.9.13 makes the full denominators centralize each other. The earlier
13.7.3(7) centralizer bound then puts [V,Uγ] in the original order-two line;
F.9.13(5) makes that commutator nontrivial. This proves equality with V₁,
containment V₁ ≤ Uγ, and genuine transvection formulas on Uγ itself.
The action is actual conjugation, and at least one actor is nonidentity.

For the final contradiction, a hypothetical Vγ ≤ Q_H makes [U_H,Vγ]
lie in both disjoint lines. Its centralization of V₃ and the original
13.5.4(4) bound then give [V,Vγ]=V₁. The final hyperplane/fusion argument
is not asserted here. Nor are the full denominators assumed as part of a
record claiming to prove 13.8.27: they remain visible premises, to be
obtained from case (1), the overgroup equality and proved 13.8.7.

Source: Aschbacher–Smith, F.9.13, F.9.16(1), 13.7.3(7), and 13.8.27(3),
printed pp.322–324,936,963 (PDF pp.339–341,953,980).
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open CriticalGeometry SourceCompletion
open CriticalGeometry.AsymmetricPair
open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The actual F.9.16 center before passing to any module coordinates. -/
theorem full_denominators_commutator
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    ⁅Source.UH H V₃, c.Ugamma V₃⁆ = ⊥ ∧ ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ := by
  have hg := local_earlierGeometry d hF9 c
  have hcomm : ⁅Source.UH H V₃, c.Ugamma V₃⁆ = ⊥ := by
    simpa only [hDH, hDg] using hg.cross_centralizes
  have hUgH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans hg.Vgamma_H
  have hUgHC : c.Ugamma V₃ ≤ Source.HC H V₃ := by
    refine le_inf hUgH (commutator_eq_bot_iff_le_centralizer.mp ?_)
    rwa [commutator_comm]
  have hbound : ⁅V, c.Ugamma V₃⁆ ≤ V₁ := by
    have hc := Section07.centralizer_UH_commutator (localNaturalSetup d) hF9
    rw [commutator_comm] at hc
    exact (commutator_mono (le_conjugateSpanBy V H) hUgHC).trans hc
  have hne : ⁅V, c.Ugamma V₃⁆ ≠ ⊥ := by
    intro he
    apply f9_commutator_not_le_Aone _ hF9 c hg.length
    rw [commutator_comm]
    exact he.le.trans bot_le
  have hdiv : Nat.card (⁅V, c.Ugamma V₃⁆ : Subgroup G) ∣ 2 := by
    simpa only [d.line_card] using card_dvd_of_le hbound
  have hcard : Nat.card (⁅V, c.Ugamma V₃⁆ : Subgroup G) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun h => hne (card_eq_one.mp h))
  have he : ⁅V, c.Ugamma V₃⁆ = V₁ := eq_of_le_of_card_ge hbound
    (by rw [hcard, d.line_card])
  have hn : V ≤ normalizer (c.Ugamma V₃ : Set G) :=
    ((le_conjugateSpanBy V H).trans hg.VH_endpoint).trans (c.normalizes_Ugamma V₃)
  exact ⟨hcomm, he, he.symm.le.trans (le_normalizer_iff_commutator_le_right.mp hn)⟩

/-- Conjugation on the original Uγ has common center V₁ and a nonidentity
actor. This is an action on Uγ itself, with no replacement carrier. -/
theorem full_denominators_transvections
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    let _ : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃))) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  obtain ⟨_, hc, hline⟩ := full_denominators_commutator d hF9 c hDH hDg
  have hg := local_earlierGeometry d hF9 c
  have hn : V ≤ normalizer (c.Ugamma V₃ : Set G) :=
    ((le_conjugateSpanBy V H).trans hg.VH_endpoint).trans (c.normalizes_Ugamma V₃)
  let action : V →* MulAut (c.Ugamma V₃) :=
    (c.Ugamma V₃).normalizerMonoidHom.comp (inclusion hn)
  have happ (v : V) (u : c.Ugamma V₃) :
      (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹ := rfl
  refine ⟨hc, hline, action, happ, ?_, ?_⟩
  · by_contra hnone
    have hall : ∀ v : V, action v = 1 := by simpa only [not_exists, not_not] using hnone
    have hz : ⁅V, c.Ugamma V₃⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro v hv u hu
      have he := happ ⟨v, hv⟩ ⟨u, hu⟩
      rw [hall] at he
      change u = v * u * v⁻¹ at he
      exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
    have hbot : V₁ = ⊥ := hc.symm.trans hz
    have hcard := d.line_card
    rw [hbot, Subgroup.card_bot] at hcard
    contradiction
  · intro v
    apply transvection_of_line (action v) (V₁.subgroupOf (c.Ugamma V₃))
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hline).toEquiv]; exact d.line_card)
    intro u
    change (u : G)⁻¹ * ((v : G) * (u : G) * (v : G)⁻¹) ∈ V₁
    rw [← hc, commutator_comm]
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      commutator_mem_commutator ((c.Ugamma V₃).inv_mem u.property) v.property

/-- The last assumed-containment branch in 13.8.27(3) centralizes the full
U_H. It retains the same critical pair and its literal conjugator. -/
theorem core_containment_centralizes
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcore : c.Vgamma ≤ Source.QH H) :
    ⁅Source.UH H V₃, c.Vgamma⁆ = ⊥ := by
  have hg := local_earlierGeometry d hF9 c
  have hcomm := (full_denominators_commutator d hF9 c hDH hDg).1
  have hfirst : ⁅Source.UH H V₃, c.Vgamma⁆ ≤ V₁ :=
    (commutator_mono le_rfl hcore).trans hF9.commutator_UH_QH_le_point
  have hsecond : ⁅Source.UH H V₃, c.Vgamma⁆ ≤ c.Aone V₁ := by
    let e := MulAut.conj (c.gb : G)
    have hc : ⁅(Source.HC H V₃).map e.toMonoidHom, c.Vgamma⁆ ≤ c.Aone V₁ := by
      have hh := map_mono (f := e.toMonoidHom)
        (Section07.centralizer_UH_commutator (localNaturalSetup d) hF9)
      rwa [map_commutator] at hh
    apply (commutator_mono ?_ le_rfl).trans hc
    have he : (Source.HC H V₃).map e.toMonoidHom =
        vertexGroup L (T : Subgroup G) H c.gamma ⊓ centralizer (c.Ugamma V₃ : Set G) := by
      rw [Source.HC, ← map_inf_centralizer_of_injective e.toMonoidHom e.injective,
        c.vertexGroup_gamma]
      rfl
    rw [he]
    exact le_inf ((conjugateSpanBy_mono d.seed_le le_rfl).trans hg.VH_endpoint)
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact le_bot_iff.mp ((le_inf hfirst hsecond).trans hg.lines_disjoint.le)

/-- Apply the genuine 13.5.4(4) ambient centralizer input in the final branch.
The fusion step must still exclude this common-line commutator. -/
theorem core_containment_seed_centralizer
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcore : c.Vgamma ≤ Source.QH H) :
    c.Vgamma ≤ centralizer (V₃ : Set G) ∧ ⁅V, c.Vgamma⁆ = V₁ := by
  have hc := core_containment_centralizes d hF9 c hDH hDg hcore
  have hVc : c.Vgamma ≤ centralizer (V₃ : Set G) := by
    apply le_trans _ (centralizer_le (le_conjugateSpanBy V₃ H))
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hbound : ⁅V, c.Vgamma⁆ ≤ V₁ :=
    (commutator_mono le_rfl hVc).trans
      (Section05.AmbientSource.source_seed_centralizer_displacement (localNaturalSetup d) hcentral)
  have hsmall := (full_denominators_commutator d hF9 c hDH hDg).2.1
  exact ⟨hVc, le_antisymm hbound (hsmall.symm.le.trans
    (commutator_mono le_rfl (map_mono (conjugateSpanBy_mono d.seed_le le_rfl))))⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
