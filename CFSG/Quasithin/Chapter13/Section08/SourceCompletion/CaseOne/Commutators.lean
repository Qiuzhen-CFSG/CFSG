module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Fusion
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Preliminary

/-!
# The endpoint center in the full-denominator branch

F.9 makes U_H and Uγ commute. The transported 13.7.3 centralizer bound
then puts [U_H,Vγ] in A₁, and the proved escape of Vγ from O₂(H) makes
this commutator nontrivial. Since A₁ has order two, it is the exact
commutator and lies in U_H. The same full-denominator relations show that
V intersects U_H in V₃. At critical distance three, the geometric placement
of A₁ in a conjugate of V therefore improves to a conjugate of V₃.

In particular a nonabelian U_L has this placement, by the earlier critical
distance theorem. This is the initial geometric reduction of 13.8.33;
full denominators are branch assumptions, not a claimed source conclusion.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, using F.9.13--14,
13.7.3(7), and 13.8.27(3).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.SixAndG2.Overgroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem endpoint_commutator
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G)) :
    ⁅Source.UH H V₃, c.Vgamma⁆ = c.Aone V₁ ∧ c.Aone V₁ ≤ Source.UH H V₃ := by
  have hg := local_earlierGeometry d hF9 c
  have hcomm := (full_denominators_commutator d hF9 c hDH hDg).1
  have hbound : ⁅Source.UH H V₃, c.Vgamma⁆ ≤ c.Aone V₁ := by
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
  have hne : ⁅Source.UH H V₃, c.Vgamma⁆ ≠ ⊥ := by
    intro he
    apply full_denominators_escape d hF9 c hDH hDg hcentral
    have hk := f9_commutatorPreimage_eq _ hF9 c.Vgamma hg.Vgamma_H
    have hle : c.Vgamma ≤ commutatorPreimage c.Vgamma (Source.UH H V₃) V₁ := by
      apply le_commutatorPreimage le_rfl
      rw [commutator_comm, he]
      exact bot_le
    exact (hle.trans hk.le).trans inf_le_right
  have hcard : Nat.card (c.Aone V₁) = 2 := by
    change Nat.card (V₁.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective, d.line_card]
  have hdiv : Nat.card (⁅Source.UH H V₃, c.Vgamma⁆ : Subgroup G) ∣ 2 := by
    simpa only [hcard] using card_dvd_of_le hbound
  have hsize : Nat.card (⁅Source.UH H V₃, c.Vgamma⁆ : Subgroup G) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun h => hne (card_eq_one.mp h))
  have he := eq_of_le_of_card_ge hbound (by rw [hcard, hsize])
  refine ⟨he, ?_⟩
  rw [← he]
  exact le_normalizer_iff_commutator_le_left.mp
    (hg.Vgamma_H.trans (le_normalizer_conjugateSpanBy V₃ H))

theorem seed_intersection
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    V ⊓ Source.UH H V₃ = V₃ := by
  obtain ⟨hc, hm, _⟩ := full_denominators_commutator d hF9 c hDH hDg
  apply (flag_intersection_of_index_two V V₃ (Source.UH H V₃)
    (le_inf d.seed_le (le_conjugateSpanBy V₃ H)) (Comparison.local_seed_index d) ?_).symm
  intro hV
  have he : V₁ = ⊥ := by
    rw [← hm]
    exact le_bot_iff.mp ((commutator_mono hV le_rfl).trans hc.le)
  have hs := d.line_card
  rw [he, card_bot] at hs
  contradiction

theorem seed_placement_of_length_three
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hb : c.path.length = 3) :
    ∃ h : H, c.Aone V₁ ≤ V₃.conjBy (h : G) := by
  obtain ⟨h, hh⟩ := f9_Aone_le_conjugate_of_length_three _ hF9 c hb
  refine ⟨h, ?_⟩
  rw [← seed_intersection d hF9 c hDH hDg, conjBy,
    Subgroup.map_inf _ _ _ (MulAut.conj (h : G)).injective]
  have hfix : (Source.UH H V₃).conjBy (h : G) = Source.UH H V₃ :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H h.property)
  refine le_inf hh ?_
  change c.Aone V₁ ≤ (Source.UH H V₃).conjBy (h : G)
  rw [hfix]
  exact (endpoint_commutator d hF9 c hDH hDg hcentral).2

theorem nonabelian_seed_placement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    c.path.length = 3 ∧ ∃ h : H, c.Aone V₁ ≤ V₃.conjBy (h : G) := by
  have hg := local_earlierGeometry d hF9 c
  have hb := f9_length_three_of_nonabelian_span _ hF9 c hg.length hn
  exact ⟨hb, seed_placement_of_length_three d hF9 c hDH hDg hcentral hb⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
