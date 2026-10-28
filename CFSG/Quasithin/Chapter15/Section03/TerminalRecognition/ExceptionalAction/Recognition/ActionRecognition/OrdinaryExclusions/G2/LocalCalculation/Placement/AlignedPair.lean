module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.MarkedFactor
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Quotient
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.BorelOvergroups
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Levi

/-!
# Aligning the source local pair in the binary G₂ quotient

The common Sylow image is conjugate to the standard positive-root subgroup.
Each local image has symmetric-three quotient over its two-core, so its order
is three times the Sylow order, namely 192. Binary Borel-overgroup coverage and
the equal parabolic orders identify it with one of the standard parabolics.
Generation of the full model forces the two choices to be different.

This retains both possible orientations. The strict residual-core inequality
alone cannot decide between them; the source configuration must supply the
remaining orientation argument. This reduction uses no action classification.

Source: Aschbacher–Smith, 15.3.66–68 and the final proof of 15.3.1, printed
pp.1152–1155. The Borel-overgroup argument and concrete model are inherited
from the licensed ATLAS port through the imports.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.BinaryParabolicPair
open scoped Pointwise
open Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement

private lemma sylow_index_three {A : Type*} [Group A] [Finite A] (S : Sylow 2 A)
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : (S : Subgroup A).index = 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 A
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let R := S.mapSurjective hf
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hR : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (2 * 3) 2) = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hi := (R : Subgroup (Equiv.Perm (Fin 3))).index_mul_card
  rw [hc, hR] at hi
  have hi3 : (R : Subgroup (Equiv.Perm (Fin 3))).index = 3 := by omega
  change ((S : Subgroup A).map f).index = 3 at hi3
  rwa [Subgroup.index_map_eq _ hf (by rw [hk]; exact pCore_isPGroup.le_sylow_of_normal S)] at hi3

private theorem local_card (P : Subgroup (Model (ZMod 2))) (hU : unipotent ≤ P)
    (he : Nonempty (P ⧸ pCore 2 P ≃* Equiv.Perm (Fin 3))) : Nat.card P = 192 := by
  let S : Sylow 2 P := commonSylow.subtype hU
  have hi := sylow_index_three S he.some
  have hc := (S : Subgroup P).card_mul_index
  have hS : Nat.card S = 64 := by
    change Nat.card (unipotent.subgroupOf P) = 64
    rw [Nat.card_congr (subgroupOfEquivOfLe hU).toEquiv, card_unipotent_binary]
  rw [hi, hS] at hc
  omega

private theorem local_parabolics (P : Subgroup (Model (ZMod 2))) (hU : unipotent ≤ P)
    (he : Nonempty (P ⧸ pCore 2 P ≃* Equiv.Perm (Fin 3))) :
    P = firstParabolic ∨ P = BinaryCore.secondParabolic := by
  have hc := local_card P hU he
  have hP : P < ⊤ := lt_top_iff_ne_top.mpr (by
    intro ht
    have ht' := (card_eq_iff_eq_top P).mpr ht
    rw [hc, OrderChecks.binary_order] at ht'
    contradiction)
  have hB : Atlas.G2.borel (K := ZMod 2) ≤ P := LieParabolicSetup.borel_binary.symm ▸ hU
  rcases EvenLocal.BorelOvergroups.le_parabolic P hB hP with h | h
  · left
    rw [LieParabolicSetup.parabolic₁_binary] at h
    exact eq_of_le_of_card_ge h (by rw [hc, card_firstParabolic])
  · right
    exact eq_of_le_of_card_ge h (by rw [hc, BinaryCore.secondParabolic_card])

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  (d : SourceInput V)

/-- Align the common Sylow in the actual core quotient. The two local images
are exactly the two standard parabolics, with their order still undecided. -/
theorem aligned_source_pair (e0 : coreQuotient H ≃* (Model (ZMod 2))) :
    ∃ e : coreQuotient H ≃* (Model (ZMod 2)),
      ((d.T : Subgroup H).map coreProjection).map e.toMonoidHom = unipotent ∧
      ((((d.G1.map coreProjection).map e.toMonoidHom = firstParabolic) ∧
          ((d.G2.map coreProjection).map e.toMonoidHom = BinaryCore.secondParabolic)) ∨
        (((d.G1.map coreProjection).map e.toMonoidHom = BinaryCore.secondParabolic) ∧
          ((d.G2.map coreProjection).map e.toMonoidHom = firstParabolic))) := by
  let q : H →* (Model (ZMod 2)) := e0.toMonoidHom.comp coreProjection
  have hq : Function.Surjective q := e0.surjective.comp (QuotientGroup.mk'_surjective _)
  let S : Sylow 2 (Model (ZMod 2)) := d.T.mapSurjective hq
  let : MulAction (Model (ZMod 2)) (Sylow 2 (Model (ZMod 2))) := Sylow.mulAction
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model (ZMod 2)) S commonSylow
  let e := e0.trans (MulAut.conj g)
  have hem : e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e0.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  have hT : ((d.T : Subgroup H).map coreProjection).map e.toMonoidHom = unipotent := by
    have hh := congrArg (fun S : Sylow 2 (Model (ZMod 2)) => (S : Subgroup (Model (ZMod 2)))) hg
    change ((d.T : Subgroup H).map q).map (MulAut.conj g).toMonoidHom = unipotent at hh
    simpa only [q, map_map, hem, MonoidHom.comp_assoc] using hh
  have hgold := d.goldschmidt.quotient_twoCore.map_of_two_kernel e.toMonoidHom e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective) (by
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
      exact bot_le)
  change CFSG.Quasithin.ChapterF.IsGoldschmidtTriple
    ((d.G1.map coreProjection).map e.toMonoidHom)
    ((d.G2.map coreProjection).map e.toMonoidHom) at hgold
  have hU₁ : unipotent ≤ (d.G1.map coreProjection).map e.toMonoidHom := by
    rw [← hT]
    apply map_mono (map_mono ?_)
    rw [d.first_local]
    exact le_sup_right
  have hU₂ : unipotent ≤ (d.G2.map coreProjection).map e.toMonoidHom := by
    rw [← hT]
    apply map_mono (map_mono ?_)
    rw [d.second_local]
    exact le_sup_right
  have h₁ := local_parabolics _ hU₁ hgold.quotient_left
  have h₂ := local_parabolics _ hU₂ hgold.quotient_right
  refine ⟨e,hT,?_⟩
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have ht := hgold.generated
    rw [h₁,h₂,sup_idem] at ht
    have hc := (card_eq_iff_eq_top firstParabolic).mpr ht
    rw [card_firstParabolic, OrderChecks.binary_order] at hc
    contradiction
  · exact Or.inl ⟨h₁,h₂⟩
  · exact Or.inr ⟨h₁,h₂⟩
  · have ht := hgold.generated
    rw [h₁,h₂,sup_idem] at ht
    have hc := (card_eq_iff_eq_top BinaryCore.secondParabolic).mpr ht
    rw [BinaryCore.secondParabolic_card, OrderChecks.binary_order] at hc
    contradiction

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement
