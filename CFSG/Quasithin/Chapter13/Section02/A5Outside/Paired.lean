module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.CenterFree
public import CFSG.Quasithin.Chapter13.Section02.A5Local.ThompsonFixedPlane
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.ResidualModels

/-!
# The paired action of the center-free outside group

When Z(H)=1, the original E.2.3 action has exactly two natural factors. If
there were only one, its residual-fixed space would vanish and U_H would
have order four. The fixed plane C_V(J(T)), contained in Ω₁Z(J(T))≤U_H,
would then equal U_H, contradicting the original Thompson noncentrality.

The pair forces the concrete quotients H/O₂(H)≃S₃ wr C₂ and
O²(H)/O₂(O²(H))≃C₃². These conclusions are also applied to the contrary
core-free join H∨O²(N_L(T∩L)) in 13.2.12; its earlier [Z,L₁]=1,
Baumann-normalizer and solvability premises remain explicit.

Source: Aschbacher–Smith 13.2.11(3) and the opening of 13.2.12,
printed pp.881–882.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

theorem source_solvable_paired_factors
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let S := T.subtype hH.1.1.2
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∃ c : ChapterB.ThreeConjugates.SolvableFFStructure ρ,
      c.count = 2 ∧ ∀ i j, ∃ t : S,
        (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c, hc, _, ht, _, _, _⟩ := source_solvable_omega_action d hH hB hZ hs
  refine ⟨c, ?_, ht⟩
  rcases hc with hc | hc
  · exfalso
    let D := c.toSolvableFFFactors
    obtain ⟨_, _, hp, _, hj⟩ := e23_hypotheses
      d.hypothesis.qtke T d.normalizes_L hH hB hZ
    have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective
      U q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    have hne : q.ker ≠ ⊤ := by
      intro he
      apply hj
      rw [QuotientGroup.ker_mk'] at he
      exact le_top.trans he.ge
    have hpq := (ChapterB.minimalParabolic_reduced_image S hp q
      (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
    have hff : IsFFModule ρ := (isFFModule_iff_quadraticRatio_le_one ρ).mpr c.ratio_one.le
    have hr := (ChapterB.offender_generation (S.mapSurjective (QuotientGroup.mk'_surjective C))
      hpq ρ hff hU.quotient_pCore_eq_bot).1
    have hUT : U ≤ (S : Subgroup H) :=
      hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
    have hfixedR : fixedSpace ρ (pResidual 2 (H ⧸ C)) = ⊥ := by
      apply bot_unique
      intro v hv
      have hvc : (v.toMul : H) ∈ centralizer (pResidual 2 H : Set H) := by
        apply (NormalElementaryQuotient.mem_fixedSpace_image U q
          (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) (pResidual 2 H) v).mp
        rwa [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective C)]
      have hb : (v.toMul : H) ∈ (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H) :=
        ⟨hUT v.toMul.property, hvc⟩
      rw [sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot S hz] at hb
      exact Additive.toMul.injective (Subtype.ext (mem_bot.mp hb))
    have hfixed : fixedSpace ρ (offenderSubgroup ρ) = ⊥ :=
      (D.fixed_residual_eq hf hr).symm.trans hfixedR
    have hmove := (D.fixed_isCompl_moved hf hr).sup_eq_top
    rw [hfixed, bot_sup_eq] at hmove
    let coords := D.naturalMovedCoordinates.trans (D.singleSpaceCoordinates hc)
    have hdim : Module.finrank (ZMod 2) (Additive U) = 2 := by
      have hh := coords.finrank_eq
      rw [hmove, finrank_top] at hh
      simpa using hh
    have hcardU : Nat.card U = 4 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
      rw [Nat.card_zmod, hdim] at hh
      exact hh
    have hUH : omegaOrbit T H ≤ H := conjugateSpanBy_le
      (fun _ hx => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) H.le_normalizer
    have hcard : Nat.card (omegaOrbit T H) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv).symm.trans hcardU
    let F := V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
    let := d.elementary
    let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ V from inf_le_left)
    have hFE : F ≤ ChapterB.thompsonAlpha (T : Subgroup G) :=
      elementary_centralizer_maxJ_le_omegaCenter _ F
        (inf_le_left.trans d.chosen.le_sylow) inf_le_right
    have hFU : F ≤ omegaOrbit T H := hFE.trans
      ((source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz).le.trans inf_le_left)
    have hFUeq : F = omegaOrbit T H := eq_of_le_of_card_ge hFU (by
      rw [hcard]
      exact d.four_le_card_thompson_fixed)
    apply thompson_moves_omegaOrbit d.hypothesis.qtke T hH hB hZ
    rw [← hFUeq]
    exact le_centralizer_iff.mp inf_le_right
  · exact hc

theorem source_centerfree_residual_core_quotient_models
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        Multiplicative (Fin 2 → ZMod 3)) := by
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c, hc, _⟩ := source_solvable_paired_factors d hH hB hZ hs hz
  have hC : C = pCore 2 H := source_omega_centralizer_eq_twoCore d hH hB hZ hs
  rcases source_residual_core_quotient_models d hH hB hZ hs with ⟨⟨e⟩, _⟩ | hw
  · exfalso
    obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    have hS : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_congr eS.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    let eQ := (QuotientGroup.quotientMulEquivOfEq hC).trans e
    have hQ : Nat.card (H ⧸ C) = 6 := (Nat.card_congr eQ.toEquiv).trans hS
    have hO : Nat.card (offenderSubgroup ρ) = 36 := by
      rw [Nat.card_congr c.toSolvableFFFactors.naturalActorCoordinates.toEquiv,
        Nat.card_fun, Nat.card_fin, hS]
      rw [hc]
      norm_num
    have hle := (offenderSubgroup ρ).card_le_card_group
    rw [hQ, hO] at hle
    omega
  · exact hw

theorem source_coreFree_borel_join_paired_models
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        Multiplicative (Fin 2 → ZMod 3)) :=
  source_centerfree_residual_core_quotient_models d hH hB hZ hs
    (source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside
