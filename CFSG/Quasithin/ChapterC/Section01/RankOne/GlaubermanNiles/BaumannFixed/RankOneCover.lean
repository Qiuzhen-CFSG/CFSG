module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.NaturalAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.SmallFieldQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.Movement
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SemilinearImages
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# C.1.17 reduces to Campbell's marked rank-one class

The actual natural quotient supplies a faithful binary action of H*. For
field order greater than two its generalized Fitting subgroup is the normal
SL₂ layer. The semilinear Baumann image theorem, genuine Thompson movement,
and Baumann-fixedness put the Sylow image in that layer. Minimal-parabolic
normal generation therefore makes the layer all of H*. The two-element
field case is the separate S₃ argument. The original action kernel has
Frattini image modulo O₂(H), so every original marked local group satisfies
Campbell's RankOneCover, with no additional quotient or supplement premise.

The final consumer restricts the original marking to J(B); all resulting
Campbell embeddings share this one abstract Thompson group. This is a
reduction toward the uniform C.1.18 theorem, not the still-required
comparison and characteristic-pair selection theorem.

Source: Aschbacher–Smith C.1.17–18, p.126; Campbell, *Pushing up in Finite
Groups* (1979), Hypothesis (E), p.9, and marked quadruples, pp.13–14.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
  {F : Type} [Field F] [CharP F 2] [Finite F]

omit [Finite B] [Finite H] in
theorem derived_psl_eq_top_of_two_lt_card (hF : 2 < Nat.card F) : commutator PSL(2,F) = ⊤ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have ha : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra! hh
    have hsub : (Finset.univ : Finset F) ⊆ {0,1} := by
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      · simp [hh a ha]
    have hc := Finset.card_le_card hsub
    have h2 : Nat.card F ≤ 2 := by simpa [Nat.card_eq_fintype_card] using hc
    omega
  apply SL2Simple.PSL_commutator_eq_top
  obtain ⟨a,ha,ha1⟩ := ha
  refine ⟨a,ha,?_⟩
  intro he
  rcases sq_eq_one_iff.mp he with h | h
  · exact ha1 h
  · exact ha1 (by simpa only [CharTwo.neg_eq] using h)

omit [Finite B] in
theorem NaturalModel.exists_actor_equiv_sl (m : NaturalModel e F) (hF : 2 < Nat.card F) :
    ∃ E : generalizedFitting (LocalStar e) ≃* SL(2,F),
      ∀ a, E a = Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (m.actorIso a : PSL(2,F)) := by
  let E := ((m.actorIso.trans (MulEquiv.subgroupCongr (derived_psl_eq_top_of_two_lt_card hF))).trans
    Subgroup.topEquiv).trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  exact ⟨E,fun _ => rfl⟩

theorem InLocalClass.generalizedFitting_localStar_eq_top (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : 2 < Nat.card F) : generalizedFitting (LocalStar e) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let _ : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let _ : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  obtain ⟨T,he,hT⟩ := h.sylow
  obtain ⟨ρ,f,hfaith,hf,hcoords,hconj,hnat,hker⟩ := h.exists_faithful_natural_action m
  obtain ⟨E,hE⟩ := NaturalModel.exists_actor_equiv_sl m hF
  let q := QuotientGroup.mk' (localKernel e)
  have hq := QuotientGroup.mk'_surjective (localKernel e)
  have hqker : q.ker = centralizer (moved e : Set H) := by rw [QuotientGroup.ker_mk',hker]
  have hMT : moved e ≤ T := (h.moved_le_coreOmegaCenter.trans
    (fun x hx => ((mem_omegaOneCenterAmbient_iff (pCore 2 H) x).mp hx).1)).trans
    (pCore_isPGroup.le_sylow_of_normal T)
  have hnat' (a : generalizedFitting (LocalStar e)) (v : Fin 2 → F) :
      ρ a v = Matrix.mulVec (E a).val v := by rw [hE]; exact hnat a v
  have heq (a : LocalStar e) (v : Additive (moved e)) :
      f (NormalElementaryQuotient.representation (moved e) q hq hqker a v) = ρ a (f v) := by
    obtain ⟨g,rfl⟩ := hq a
    have hc : NormalElementaryQuotient.representation (moved e) q hq hqker (q g) v =
        Additive.ofMul (movedConjugate e g v.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply (moved e) q hq hqker g v
    rw [hc]
    exact hconj g v.toMul
  have hi := ChapterB.RankOneBaumann.thompson_baumann_images_of_semilinear_quotient
    T (moved e) q hq hqker hMT (h.thompson_moves_moved hB T he)
    (generalizedFitting (LocalStar e)) E ρ hfaith hnat' hF f hf heq
  have hBaum : ChapterB.baumann (T : Subgroup H) = T := by
    rw [← he]
    exact h.baumann_range_eq_self hB
  have hTL : (T : Subgroup H) ≤ actorLift e := by
    apply map_le_iff_le_comap.mp
    change (T : Subgroup H).map q ≤ generalizedFitting (LocalStar e)
    rw [← hBaum,hi.2]
    exact inf_le_right
  have hAt := T.normal_eq_top_of_uniqueMaximal hT.1
    ((ChapterB.isMinimalParabolicOver_top_iff T).mp hT).2 (actorLift e) hTL
  have hmap := congrArg (Subgroup.map q) hAt
  change ((generalizedFitting (LocalStar e)).comap q).map q = (⊤ : Subgroup H).map q at hmap
  calc
    generalizedFitting (LocalStar e) = ((generalizedFitting (LocalStar e)).comap q).map q :=
      (Subgroup.map_comap_eq_self_of_surjective hq _).symm
    _ = ⊤ := hmap.trans (Subgroup.map_top_of_surjective q hq)

theorem InLocalClass.localStar_equiv_psl_of_two_lt_card (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : 2 < Nat.card F) : Nonempty (LocalStar e ≃* PSL(2,F)) := by
  obtain ⟨E,_⟩ := NaturalModel.exists_actor_equiv_sl m hF
  let hL := InLocalClass.generalizedFitting_localStar_eq_top h hB m hF
  exact ⟨((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans E).trans
    Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩

theorem InLocalClass.rankOneCover_of_large_field (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    Campbell.RankOneCover H := by
  have hFl : 2 < Nat.card F := by rw [hF]; exact (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn)
  exact ⟨h.fitting,localKernel e,inferInstance,h.core_le_localKernel,
    h.kernel_noPartialComplement,n,by omega,F,inferInstance,inferInstance,hF,InLocalClass.localStar_equiv_psl_of_two_lt_card h hB m hFl⟩
/-- The whole source action quotient is PSL₂ over the original marked field. -/
theorem InLocalClass.localStar_equiv_psl (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) : Nonempty (LocalStar e ≃* PSL(2,F)) := by
  have htwo : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases htwo.eq_or_lt with h2 | h2
  · exact h.localStar_equiv_psl_of_field_card_two m h2.symm
  · exact h.localStar_equiv_psl_of_two_lt_card hB m h2

/-- Every original C.1.17 group over a Baumann-fixed base satisfies Campbell's
rank-one hypothesis, with its literal local action kernel as covering kernel. -/
theorem InLocalClass.rankOneCover (h : InLocalClass e) (hB : IsBaumannFixed B) :
    Campbell.RankOneCover H := by
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  exact ⟨h.fitting,localKernel e,inferInstance,h.core_le_localKernel,
    h.kernel_noPartialComplement,n,hn,F,inferInstance,inferInstance,hF,
    h.localStar_equiv_psl hB m⟩

/-- Restricting the original marking to J(B) gives the common Thompson-group
marking used in Campbell's comparison theorem. -/
theorem InLocalClass.exists_campbellEmbedding (h : InLocalClass e) (hB : IsBaumannFixed B) :
    ∃ d : Campbell.Embedding (elementaryAbelianMaxJ (⊤ : Subgroup B)) H,
      d.marking = e.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype ∧
      (d.sylow : Subgroup H) = e.range := by
  obtain ⟨T,he,hT⟩ := h.sylow
  let f := e.comp (elementaryAbelianMaxJ (⊤ : Subgroup B)).subtype
  have hf : f.range = Campbell.J (T : Subgroup H) := by
    rw [MonoidHom.range_comp,range_subtype,← elementaryAbelianMaxJ_map_injective e h.injective]
    have ht : (⊤ : Subgroup B).map e = e.range := by ext x; simp
    rw [ht,he]
    rfl
  exact ⟨⟨T,f,h.injective.comp Subtype.val_injective,hf,h.rankOneCover hB⟩,rfl,he.symm⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles
