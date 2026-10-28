module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisFusion

/-!
# LocalAnalysisCentralizersThompsonSource at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersThompsonSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

include E

theorem pointCentralizers_of_central_points_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hc : ∀ z : V, z ≠ 1 → (z : G) ∈ centralizer (T : Set G) →
      (weight (E.coordinates z).toAdd.val = 2 ∨ weight (E.coordinates z).toAdd.val = 6) →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G))
    (v : V) (hv : v ≠ 1)
    (hw : weight (E.coordinates v).toAdd.val = 2 ∨ weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z,hz,l,hl⟩ := E.central_representative_at structural v hv
  have hweight := (E.component_conjugate_iff_weight_eq v z).mp ⟨l,hl⟩
  have hzw := hweight ▸ hw
  have hz1 : z ≠ 1 := E.ne_one_of_weight_ne_zero z (by rcases hzw with h | h <;> omega)
  exact E.centralizer_le_of_same_weight v z hweight (hc z hz1 hz hzw)

theorem exists_central_escape_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ∃ z : V, z ≠ 1 ∧ (z : G) ∈ centralizer (T : Set G) ∧
      ¬ centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨x,hx,hx1,hout⟩ := escape L V S.hypothesis S.chosen
  let v : V := ⟨x,hx⟩
  have hv : v ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨z,hz,l,hl⟩ := E.central_representative_at structural v hv
  have hz1 : z ≠ 1 := by
    intro h
    have he : V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ v = 1 := hl.trans h
    exact hv ((V.normalizerMonoidHom _).map_eq_one_iff.mp he)
  refine ⟨z,hz1,hz,fun hc => hout ?_⟩
  exact E.centralizer_le_of_same_weight v z
    ((E.component_conjugate_iff_weight_eq v z).mp ⟨l,hl⟩) hc

theorem hasMaximalOutside_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    Chapter3.HasMaximalOutside T (normalizer (L : Set G)) := by
  obtain ⟨z,hz1,hzc,hout⟩ := E.exists_central_escape_at structural escape
  have hz := (mem_omegaCenterIn_iff _ _).mp (mem_omegaCenter_of_central (S := S) z hzc)
  have ho : orderOf (z : G) = 2 := orderOf_eq_prime hz.2.2
    (fun h => hz1 (Subtype.ext h))
  have hp : IsPGroup 2 (zpowers (z : G)) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using ho)
  have hne : zpowers (z : G) ≠ ⊥ := by
    intro he
    exact hz1 (Subtype.ext (mem_bot.mp (he ▸ mem_zpowers (z : G))))
  have hc : centralizer ({(z : G)} : Set G) ≤ normalizer (zpowers (z : G) : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨H,hNH,hH⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (zpowers (z : G) : Set G)) from ⟨_,hne,hp,rfl⟩)
  have hTH : (T : Subgroup G) ≤ H := by
    apply le_trans ?_ (hc.trans hNH)
    intro t ht
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzc) t ht)
  have hTM := S.hypothesis.source_sylow_normalizes_at structural
  have hM := (S.hypothesis.toHypothesis1221.sylow_normalized_maximal_unique hTM
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  exact Chapter3.hasMaximalOutside_of_two_distinct hM hH hTM hTH
    (fun he => hout (hc.trans (hNH.trans_eq he)))

theorem omega_center_centralizer_le_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z,hz,hzc⟩ := E.central_representative_weight_at structural (Or.inr (Or.inr rfl))
  exact (centralizer_le (Set.singleton_subset_iff.mpr
    (mem_omegaCenter_of_central (S := S) z hzc))).trans (hsix z hzc hz)

theorem thompson_generation_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  apply Eq.symm
  apply Chapter3.Section02.source_component_thompson_generation
    S.hypothesis.simpleQTKE T L S.hypothesis.maximal_faithful.1
    S.hypothesis.maximal_faithful.2 S.hypothesis.quasisimple
    (S.hypothesis.source_sylow_normalizes_at structural) (E.hasMaximalOutside_at structural escape)
  exact E.omega_center_centralizer_le_of_weight_six_at structural hsix

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

