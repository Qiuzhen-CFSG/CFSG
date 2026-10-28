module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRelocation
public import CFSG.Quasithin.Chapter6.Section02.NaturalHyperplanes
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# Excluding the natural module after Cartan centralization

A nonzero elementary subgroup normalized by T meets its central omega.
The original escaping cubic lies in L and centralizes omega, so it fixes a
nonzero vector in that intersection. In a genuine natural SL₂ module,
a cubic fixes only zero. Thus neither the original reduced subgroup nor
its whole moved layer can be natural, in any field degree. The coordinate
argument also excludes repeated natural modules, including the doubled row
of 5.1.3, without assuming that T preserves either individual summand.

This is the natural-row exclusion in the last paragraph of 5.1.13.
It assumes no invariance of an independently chosen constituent. The
remaining module alternatives and their minus-torus construction are
still needed to deduce degree two from the universal source hypotheses.
Source: Aschbacher–Smith, 5.1.3 and 5.1.13, printed pp.630–631,638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- A cubic fixing the Sylow omega-center excludes every nontrivial
Sylow-invariant natural module in the Sylow subgroup. -/
theorem not_natural_of_cubic_centralizes_omega
    {T : Sylow 2 G} {L U D : Subgroup G} {m : ℕ}
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hDL : D ≤ L) (hDc : Nat.card D = 3) (hDC : D ≤ omegaCentralizer T) :
    ¬ IsNaturalModule L U m := by
  intro hn
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzU : (z : G) ∈ U := z.property.1
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hU
    exact ⟨hUT hzU,elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzU,
      z.property.2.2⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hDc])
  have hc : (a : G) * (z : G) = (z : G) * (a : G) :=
    ((hDC a.property) z hzZ).symm
  have hz := hn.cubic_fixed_eq_one (hDL a.property)
    ((orderOf_injective D.subtype D.subtype_injective a).trans ha) hzU
    (by rw [hc,mul_inv_cancel_right])
  exact hz1 (Subtype.ext hz)

/-- Centralization excludes the natural branch for the original module and
its whole moved layer, without any invariance assumption on a chosen constituent. -/
theorem localCartan_not_natural
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) :
    (¬ IsNaturalModule L W m) ∧ (¬ IsNaturalModule L (layer L W) m) := by
  have hc := (d.cubic_le.trans inf_le_right).trans (localCartan_centralizes h hH hgen c hY d)
  have hDL := (d.cubic_le.trans inf_le_left).trans (c.left_le.trans inf_le_left)
  have hW : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  exact ⟨not_natural_of_cubic_centralizes_omega h.reduced.2.1 h.reduced_le_sylow
    (le_sup_right.trans (reduced_normalizes h.reduced)) hW hDL d.cubic_card hc,
    not_natural_of_cubic_centralizes_omega h.commutator_reduced.2.1
      h.commutator_input.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.commutator_reduced))
      h.noncentral hDL d.cubic_card hc⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- Cubic fixation also excludes any number of natural summands. -/
theorem not_repeated_natural_of_cubic_centralizes_omega
    {T : Sylow 2 G} {L U D : Subgroup G}
    (hU : IsElementaryAbelian 2 U) (hUT : U ≤ (T : Subgroup G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (hU0 : U ≠ ⊥)
    (hDL : D ≤ L) (hDc : Nat.card D = 3) (hDC : D ≤ omegaCentralizer T)
    (F : BinaryField) (k : ℕ) :
    ¬ IsConjugationModel L U (repeated (linearNatural F 2) k) := by
  rintro ⟨e,f,hf⟩
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hU0 hUT hTU)
  have hzU : (z : G) ∈ U := z.property.1
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    let := hU
    exact ⟨hUT hzU,elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzU,
      z.property.2.2⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hDc])
  let aL : L := ⟨a,hDL a.property⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hao : orderOf aL = 3 :=
    (Subgroup.orderOf_coe aL).symm.trans
      ((orderOf_injective D.subtype D.subtype_injective a).trans ha)
  have hqne : q aL ≠ 1 := by
    intro he
    have haQ : aL ∈ pCore 2 L := (QuotientGroup.eq_one_iff _).mp
      (e.injective (he.trans e.map_one.symm))
    have hh := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨aL,haQ⟩ : pCore 2 L)
    rw [Subgroup.orderOf_mk,hao] at hh
    norm_num at hh
  have hqo : orderOf (q aL) = 3 := orderOf_eq_prime
    (by rw [←map_pow,←hao,pow_orderOf_eq_one,map_one]) hqne
  let zU : U := ⟨z,hzU⟩
  have hc : (a : G) * (z : G) = (z : G) * (a : G) :=
    ((hDC a.property) z hzZ).symm
  have hfix : repeated (linearNatural F 2) k (q aL) (f zU).toAdd = (f zU).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply U.subtype_injective
    change (f.symm (Multiplicative.ofAdd
      (repeated (linearNatural F 2) k (q aL) (f zU).toAdd)) : G) = (f.symm (f zU) : G)
    rw [f.symm_apply_apply]
    exact (hf aL zU).trans (by change (a:G)*(z:G)*(a:G)⁻¹=(z:G); rw [hc,mul_inv_cancel_right])
  have hz : (f zU).toAdd = 0 := by
    funext i
    exact Matrix.SL2.cubic_fixed_eq_zero (q aL) hqo ((f zU).toAdd i)
      (congrFun hfix i)
  have hzU1 : zU = 1 := f.injective (hz.trans f.map_one.symm)
  exact hz1 (Subtype.ext (congrArg (fun u : U => (u : G)) hzU1))

/-- In particular the doubled-natural source row is impossible on the full
original reduced subgroup or on its whole moved layer. -/
theorem localCartan_not_repeated_natural
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (F : BinaryField) (k : ℕ) :
    (¬ IsConjugationModel L W (repeated (linearNatural F 2) k)) ∧
      (¬ IsConjugationModel L (layer L W) (repeated (linearNatural F 2) k)) := by
  have hc := (d.cubic_le.trans inf_le_right).trans (localCartan_centralizes h hH hgen c hY d)
  have hDL := (d.cubic_le.trans inf_le_left).trans (c.left_le.trans inf_le_left)
  have hW : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  exact ⟨not_repeated_natural_of_cubic_centralizes_omega h.reduced.2.1 h.reduced_le_sylow
    (le_sup_right.trans (reduced_normalizes h.reduced)) hW hDL d.cubic_card hc F k,
    not_repeated_natural_of_cubic_centralizes_omega h.commutator_reduced.2.1
      h.commutator_input.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.commutator_reduced))
      h.noncentral hDL d.cubic_card hc F k⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
