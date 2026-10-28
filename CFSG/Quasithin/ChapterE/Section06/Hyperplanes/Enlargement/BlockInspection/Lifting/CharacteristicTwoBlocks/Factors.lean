module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.Contracts
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Five
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# Recovering the actual nonsolvable factor

A.3.8(3) is applied in the quotient by the two-core. Its conjugating
Sylow element lifts to the original Sylow subgroup, and injectivity of
C-component transport through a solvable kernel lifts the equality of
components. Thus the result concerns the original subgroups.

The nonsolvable chi-zero types are genuine C-components. The actual
core quotient distinguishes them from A₃; the natural-module data is
preserved under every isomorphism used below. In particular the A₅ deleted
permutation module and the L₂(4) natural module remain different alternatives.
The private module-transport construction is adapted from the sibling
`BlockInspection/Transport.lean`, preserving its conjugation identity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.3(4),
A.3.8(3), C.1.7 and C.1.12, printed pp.42, 45, 123–124; E.6.23, p.254.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
universe u
variable {D : Type u} [Group D] [Finite D] {κ : GroupClass.{u}}

theorem cComponent_conjugate_of_generated (earlier : SylowOrbitSource κ) (hsq : IsSQTK κ D)
    (S : Sylow 2 D) {X B : Subgroup D} (hX : X.IsCComponent)
    (hgen : X ⊔ S = ⊤) (hB : B.IsCComponent) :
    ∃ s : S, B = X.map (MulAut.conj (s : D)).toMonoidHom := by
  let N := pCore 2 D
  let q := QuotientGroup.mk' N
  let : Group.IsNilpotent N := pCore_isNilpotent
  have hsq' : IsSQTK κ (D ⧸ N) := by
    refine ⟨?_, hsq.isKGroup.quotient N⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho N pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective N)
  have hgen' : X.map q ⊔ (S' : Subgroup (D ⧸ N)) = ⊤ := by
    rw [Sylow.coe_mapSurjective, ← Subgroup.map_sup, hgen,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  obtain ⟨s', hs'⟩ := earlier (D ⧸ N) hsq' (pCore_quotient_pCore_eq_bot 2)
    S' (X.map q) (hX.map_quotient N) hgen' (B.map q) (hB.map_quotient N)
  obtain ⟨s, hs, he⟩ := mem_map.mp s'.property
  refine ⟨⟨s, hs⟩, hB.eq_of_map_quotient_eq (hX.map_equiv (MulAut.conj s)) N ?_⟩
  have hqconj : q.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (q s)).toMonoidHom.comp q := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv]
  rw [map_map, hqconj, ← map_map, he]
  exact hs'
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks

variable {D : Type*} [Group D]

theorem three_solvable (h : ChapterC.IsAlternatingBlock D 3) : Group.IsSolvable D := by
  let : Finite D := h.2.1.finite
  obtain ⟨e⟩ := h.2.2.quotient_iso
  have hc : Nat.card (D ⧸ pCore 2 D) = 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hp : IsPGroup 3 (D ⧸ pCore 2 D) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  let : Group.IsNilpotent (D ⧸ pCore 2 D) := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent
  exact Group.isSolvable_of_ker_le_range (pCore 2 D).subtype (QuotientGroup.mk' (pCore 2 D))
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem quotient_quasisimple_of_not_three (h : ChapterC.IsChiZeroBlock D)
    (h3 : ¬ ChapterC.IsAlternatingBlock D 3) : IsQuasisimple (D ⧸ pCore 2 D) := by
  rcases h with ⟨n, hn, hs, F, _, _, hc, _, hm⟩ | h | h
  · rcases hs.quotient with hq | hq
    · exact hq
    · obtain ⟨e⟩ := hm.quotient_iso
      have hle := Nat.card_le_card_of_injective
        (Matrix.SpecialLinearGroup.upperUnipotentHom F)
        (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)
      change Nat.card F ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) at hle
      rw [← Nat.card_congr e.toEquiv, hq, hc] at hle
      have hfour : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      omega
  · exact (h3 h).elim
  · exact alternating_five_quotient_quasisimple h

variable {G : Type*} [Group G] [Finite G]

theorem factor_cComponent {H B : Subgroup G} (hle : B ≤ H)
    (h : ChapterC.IsChiZeroBlock B) (hsub : (B.subgroupOf H).IsSubnormal)
    (h3 : ¬ ChapterC.IsAlternatingBlock B 3) : (B.subgroupOf H).IsCComponent := by
  let e := (subgroupOfEquivOfLe hle).symm
  let : IsQuasisimple (B ⧸ pCore 2 B) := quotient_quasisimple_of_not_three h h3
  let : IsQuasisimple ((B.subgroupOf H) ⧸ pCore 2 (B.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hsub
    (h.chi.short.twoPerfect.of_surjective e.toMonoidHom e.surjective)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open ChapterC
variable {A B : Type*} [Group A] [Group B]

private theorem transport_blockU (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private def blockUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (transport_blockU e))

private theorem transport_blockFixed (e : A ≃* B) :
    (blockFixed A).map (blockUEquiv e).toMonoidHom = blockFixed B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨(blockUEquiv e).symm x,
      (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      (blockUEquiv e).apply_symm_apply x⟩

private def coreQuotientEquiv (e : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def blockModuleEquiv (e : A ≃* B) : BlockModule A ≃* BlockModule B :=
  QuotientGroup.congr _ _ (blockUEquiv e) (transport_blockFixed e)

private theorem blockUEquiv_conjugate (e : A ≃* B) (a : A) (u : blockU A) :
    blockUEquiv e (blockConjugate A a u) =
      blockConjugate B (e a) (blockUEquiv e u) := by
  apply Subtype.ext
  change e (a * (u : A) * a⁻¹) = e a * e (u : A) * (e a)⁻¹
  simp only [map_mul, map_inv]

/-- Pull back the actual core quotient and conjugation module along an isomorphism. -/
private def pullbackModel {X V : Type*} [Group X] [Group V]
    {rho : X →* MulAut V} (model : BlockModuleModel A rho) (e : B ≃* A) :
    BlockModuleModel B rho where
  quotientIso := (coreQuotientEquiv e).trans model.quotientIso
  moduleIso := (blockModuleEquiv e).trans model.moduleIso
  intertwining b u := by
    change model.moduleIso (QuotientGroup.mk' (blockFixed A)
      (blockUEquiv e (blockConjugate B b u))) =
      rho (model.quotientIso (QuotientGroup.mk' (pCore 2 A) (e b)))
        (model.moduleIso (QuotientGroup.mk' (blockFixed A) (blockUEquiv e u)))
    rw [blockUEquiv_conjugate]
    exact model.intertwining (e b) (blockUEquiv e u)

/-- The full equivariant linear model is invariant under group isomorphism. -/
private theorem linearModel_of_equiv {X V k : Type*} [Group X]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k X V} (h : IsLinearBlockModel A pi) (e : A ≃* B) :
    IsLinearBlockModel B pi := by
  obtain ⟨rho, ⟨model⟩, hpi⟩ := h
  exact ⟨rho, ⟨pullbackModel model e.symm⟩, hpi⟩

private theorem alternating_of_equiv {m : ℕ} (h : IsAlternatingBlock A m)
    (e : A ≃* B) : IsAlternatingBlock B m :=
  ⟨h.1, h.2.1.of_mulEquiv e, linearModel_of_equiv h.2.2 e⟩


/-- Every chi-zero type transports its actual core quotient and module. -/
theorem chiZero_of_mulEquiv (h : IsChiZeroBlock A) (e : A ≃* B) : IsChiZeroBlock B := by
  rcases h with ⟨n, hn, hs, F, _, _, hF, hPSL, hm⟩ | h | h
  · exact Or.inl ⟨n, hn, hs.of_mulEquiv e, F, inferInstance, inferInstance,
      hF, hPSL.of_mulEquiv (coreQuotientEquiv e).symm, linearModel_of_equiv hm e⟩
  · exact Or.inr (Or.inl (alternating_of_equiv h e))
  · exact Or.inr (Or.inr (alternating_of_equiv h e))
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
