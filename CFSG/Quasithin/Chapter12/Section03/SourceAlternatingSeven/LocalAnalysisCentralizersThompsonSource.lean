module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisFusion
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import CFSG.Quasithin.Chapter3.Section02.SourceComponentThompson
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Central representatives and the first Thompson consequence in the A₇ case

The component orbits transport ambient centralizer containment to a central
representative of the same weight. The uniform escape assumption supplies a
maximal two-local outside N(L) containing T, without a Sylow-normalizer or
ambient fusion premise. Once the weight-six centralizer is controlled, its
central representative controls C_G(Ω₁Z(T)); the original 3.1.8 argument then
proves L=[L,J(T)]. The weight-six containment remains an explicit obligation.

Source: Aschbacher--Smith, 12.3.4, 12.3.6 and the first assertion of
12.3.7(1), printed pp.808--809, with 12.2.9(2), p.798.
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

/-- A component conjugator transports the entire ambient point centralizer. -/
theorem centralizer_le_of_same_weight (x y : V)
    (hw : weight (E.coordinates x).toAdd.val = weight (E.coordinates y).toAdd.val)
    (hy : centralizer ({(y : G)} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨l,hl⟩ := (E.component_conjugate_iff_weight_eq x y).mpr hw
  have he : (l : G) * (x : G) * (l : G)⁻¹ = y := congrArg Subtype.val hl
  intro a ha
  have hm := map_centralizer_le_centralizer_image ({(x : G)} : Set G)
    (MulAut.conj (l : G)).toMonoidHom (mem_map_of_mem _ ha)
  have hc : (l : G) * a * (l : G)⁻¹ ∈ centralizer ({(y : G)} : Set G) := by
    simpa only [Set.image_singleton, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, he] using hm
  have hn := L.le_normalizer l.property
  have h := (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem (inv_mem hn) (hy hc)) hn
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

/-- A nonzero weight guarantees a nonidentity point in the original V. -/
theorem ne_one_of_weight_ne_zero (v : V)
    (hv : weight (E.coordinates v).toAdd.val ≠ 0) : v ≠ 1 := by
  intro he
  apply hv
  rw [he,map_one]
  rfl

omit E in
include S in
/-- Central points of V are in the actual Sylow omega center. -/
theorem mem_omegaCenter_of_central (v : V)
    (hv : (v : G) ∈ centralizer (T : Set G)) :
    (v : G) ∈ omegaCenterIn (T : Subgroup G) := by
  let := S.chosen.elementary
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨S.chosen.le_sylow v.property,hv,elemPow_eq_one_of_isElementaryAbelian _ v.property⟩

/-- The requested input to `localAnalysis` needs only the central representatives.
No ambient fusion or Sylow-normalizer containment is used. -/
theorem pointCentralizers_of_central_points
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hc : ∀ z : V, z ≠ 1 → (z : G) ∈ centralizer (T : Set G) →
      (weight (E.coordinates z).toAdd.val = 2 ∨ weight (E.coordinates z).toAdd.val = 6) →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G))
    (v : V) (hv : v ≠ 1)
    (hw : weight (E.coordinates v).toAdd.val = 2 ∨ weight (E.coordinates v).toAdd.val = 6) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z,hz,l,hl⟩ := E.central_representative structural v hv
  have hweight := (E.component_conjugate_iff_weight_eq v z).mp ⟨l,hl⟩
  have hzw := hweight ▸ hw
  have hz1 : z ≠ 1 := E.ne_one_of_weight_ne_zero z (by rcases hzw with h | h <;> omega)
  exact E.centralizer_le_of_same_weight v z hweight (hc z hz1 hz hzw)

/-- The original escape has a representative centralizing the full Sylow group. -/
theorem exists_central_escape
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ∃ z : V, z ≠ 1 ∧ (z : G) ∈ centralizer (T : Set G) ∧
      ¬ centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨x,hx,hx1,hout⟩ := escape L V S.hypothesis S.chosen
  let v : V := ⟨x,hx⟩
  have hv : v ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨z,hz,l,hl⟩ := E.central_representative structural v hv
  have hz1 : z ≠ 1 := by
    intro h
    have he : V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ v = 1 := hl.trans h
    exact hv ((V.normalizerMonoidHom _).map_eq_one_iff.mp he)
  refine ⟨z,hz1,hz,fun hc => hout ?_⟩
  exact E.centralizer_le_of_same_weight v z
    ((E.component_conjugate_iff_weight_eq v z).mp ⟨l,hl⟩) hc

/-- Escape supplies the genuine standing guard needed for 3.1.8. -/
theorem hasMaximalOutside
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    Chapter3.HasMaximalOutside T (normalizer (L : Set G)) := by
  obtain ⟨z,hz1,hzc,hout⟩ := E.exists_central_escape structural escape
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
  have hTM := S.hypothesis.source_sylow_normalizes structural
  have hM := (S.hypothesis.toHypothesis1221.sylow_normalized_maximal_unique hTM
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  exact Chapter3.hasMaximalOutside_of_two_distinct hM hH hTM hTH
    (fun he => hout (hc.trans (hNH.trans_eq he)))

/-- A central weight-six point controls the centralizer of Ω₁Z(T). -/
theorem omega_center_centralizer_le_of_weight_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z,hz,hzc⟩ := E.central_representative_weight structural (Or.inr (Or.inr rfl))
  exact (centralizer_le (Set.singleton_subset_iff.mpr
    (mem_omegaCenter_of_central (S := S) z hzc))).trans (hsix z hzc hz)

/-- The first conclusion of 12.3.7, with only the weight-six branch still explicit. -/
theorem thompson_generation_of_weight_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    L = ⁅L,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  apply Eq.symm
  apply Chapter3.Section02.source_component_thompson_generation
    S.hypothesis.simpleQTKE T L S.hypothesis.maximal_faithful.1
    S.hypothesis.maximal_faithful.2 S.hypothesis.quasisimple
    (S.hypothesis.source_sylow_normalizes structural) (E.hasMaximalOutside structural escape)
  exact E.omega_center_centralizer_le_of_weight_six structural hsix

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
