module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.Representation.Rudvalis.DirectDisplacement
public import Theory.Representation.BinaryOffender.MaximalCentralizerSaturation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.Triality.InnerDisplacement.CoverReduction
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Maximality
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
public import Theory.GroupTheory.GeneralizedFitting.InnerAutomorphisms
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupAction.AutomorphismNormalizer

/-!
# Direct exclusion of Rudvalis source actions

The arbitrary faithful binary action has involution displacements at least
fourteen in class 2B and twelve in class 2A. An elementary actor of ratio at
most two must saturate the intrinsic rank-six bound. Its involutions then
share a fixed space, so maximality of their centralizers places the actor
inside a double centralizer of order at most two.

The source application retains three independently owned group inputs:
the two-primary covering-center bound, intrinsic two-rank at most six,
and invariance of the point-stabilizer class under automorphisms. The last
input makes all automorphisms inner and hence F*(G)=G. Covering-center
elimination and the resulting actual group equivalence transport the original
source actor. No module recognition, matrix marking, degree-28 assumption,
or degree-completeness theorem is used.

Source: Aschbacher--Smith K.4, printed p.457; Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 5.1 (Ru). The independent
group producers are qt-i01-multiplier-ru, qt-k04-ru28-intrinsic-two-rank,
and qt-1-03-outer-rudvalis-stabilizer.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisDirect
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.RudvalisDirectDisplacement
open scoped ENNReal
universe u v

private theorem model_twoCore_eq_bot [IsSimpleGroup Rudvalis.Model] :
    pCore 2 Rudvalis.Model = ⊥ := by
  rcases (inferInstance : (pCore 2 Rudvalis.Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 Rudvalis.Model := by
      have hh := pCore_isPGroup (p := 2) (G := Rudvalis.Model)
      rw [h] at hh
      exact hh.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hd : 29 ∣ 2 ^ n := by
      rw [← hn, ← Rudvalis.DirectDisplacementWords.oddWord_order]
      exact orderOf_dvd_natCard _
    have hf : 29 ∣ 2 := (show Nat.Prime 29 by decide).dvd_of_dvd_pow hd
    norm_num at hf

/-- The existing native local-group calculation applies to every source
action; no comparison with the chosen degree-28 matrices is necessary. -/
theorem low_centralizers [IsSimpleGroup Rudvalis.Model]
    (t : Rudvalis.Model) (ht : IsConj t (Rudvalis.b ^ 2)) :
    IsCoatom (centralizer ({t} : Set Rudvalis.Model)) ∧
      Nat.card (centralizer (centralizer ({t} : Set Rudvalis.Model) : Set Rudvalis.Model)) ≤ 2 := by
  have hmax : IsCoatom Rudvalis.SylowOvergroups.max6 :=
    Rudvalis.LowCentralizers.max6_isCoatom_of_twoCore model_twoCore_eq_bot
      Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
  obtain ⟨g, hg⟩ := isConj_iff.mp ht.symm
  let e : Rudvalis.Model ≃* Rudvalis.Model :=
    (MulAut.conj Rudvalis.LowCentralizers.squareConjugator).trans (MulAut.conj g)
  have he : e Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.centralInvolution = t := by
    change g * (MulAut.conj Rudvalis.LowCentralizers.squareConjugator _) * g⁻¹ = t
    rw [Rudvalis.LowCentralizers.squareConjugator_alignment]
    exact hg
  constructor
  · rw [← he, isCoatom_centralizer_equiv_iff, ← Rudvalis.LowCentralizers.max6_eq_centralizer]
    exact hmax
  · rw [← he, card_doubleCentralizer_equiv, ← Rudvalis.LowCentralizers.max6_eq_centralizer]
    exact Rudvalis.LowCentralizers.max6_doubleCentralizer_card_le_two

/-- Intrinsic rank six excludes every elementary actor of ratio at most two
in the actual arbitrary faithful irreducible binary representation. -/
theorem not_small_actor [IsSimpleGroup Rudvalis.Model]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (hr : primeRank 2 Rudvalis.Model ≤ 6)
    (A : Subgroup Rudvalis.Model) (hA : IsElementaryTwo A) :
    ¬ fixedCodim σ A ≤ 2 * rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  apply not_small_actor_of_maximal_centralizers σ hi hA
    (n := 2) (r := 6) (by decide) (by decide)
    (rank_le_of_primeRank_le hA hr) (by have := finrank_ge_twentyEight σ hf; omega)
  · intro t ht ht1
    exact (involution_displacement σ hf t ht1
      (elemPow_eq_one_of_isElementaryAbelian t ht)).1
  · intro t ht ht1 hd
    exact low_centralizers t ((involution_displacement σ hf t ht1
      (elemPow_eq_one_of_isElementaryAbelian t ht)).2 hd)

/-- Source exclusion from the three genuine remaining group producers.
All representation-theoretic premises of the earlier recognition route have
been removed. The proof even dispenses with the source upper degree bound. -/
theorem sourceExclusion_ru_of_groupFacts
    (hcenter : ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
      Nonempty (L ⧸ center L ≃* Rudvalis.Model) → IsPGroup 2 (center L))
    (hrank : IsSimpleGroup Rudvalis.Model → Group.IsPerfect Rudvalis.Model →
      primeRank 2 Rudvalis.Model ≤ 6)
    (hstable : IsSimpleGroup Rudvalis.Model → Group.IsPerfect Rudvalis.Model →
      ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
        (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
          MulAction.stabilizer Rudvalis.Model y) : SourceExclusion.{u,v} .ru := by
  intro G V _ _ _ _ _ ρ h he
  let := h.quasisimple
  let L := generalizedFitting G
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨q⟩ := he
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := q.symm.isSimpleGroup
  let : Group.IsPerfect Rudvalis.Model :=
    Group.IsPerfect.ofSurjective (f := q.toMonoidHom) q.surjective
  have hc : center L = ⊥ :=
    Triality.InnerDisplacement.center_eq_bot_of_twoGroup
      (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) (hcenter ⟨q⟩)
  let c : L ≃* Rudvalis.Model :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans q
  let : MulAction.IsPretransitive Rudvalis.modelSubgroup (Fin 4060) :=
    Rudvalis.model_isPretransitive
  have hinner := Subgroup.conj_surjective_of_stabilizers_of_normalizer
    Rudvalis.modelSubgroup 0 (hstable inferInstance inferInstance)
    Rudvalis.outer_permutation_normalizer_eq
  have hL : L = ⊤ := generalizedFitting_eq_top_of_inner_centralQuotient q hinner
  let d : L ≃* G := (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
  let e : G ≃* Rudvalis.Model := d.symm.trans c
  have hsurj : Function.Surjective L.subtype := by
    intro g
    exact ⟨⟨g, by rw [hL]; exact mem_top g⟩, rfl⟩
  have hir : ρ.IsIrreducible :=
    (irreducible_comp_surjective_iff L.subtype hsurj ρ).mp h.irreducible
  let σ : Representation (ZMod 2) Rudvalis.Model V := ρ.comp e.symm.toMonoidHom
  have hσf : Function.Injective σ := h.faithful.comp e.symm.injective
  have hσi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hir
  obtain ⟨A, hA, _, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo (A.map e.toMonoidHom) :=
    ⟨fun hb => hA.1 ((A.map_eq_bot_iff_of_injective e.injective).mp hb),
      IsElementaryAbelian.map e.toMonoidHom⟩
  apply not_small_actor σ hσf hσi (hrank inferInstance inferInstance)
    (A.map e.toMonoidHom) hB
  have hact : ∀ g v, (LinearEquiv.refl (ZMod 2) V) (ρ g v) =
      σ (e.toMonoidHom g) ((LinearEquiv.refl (ZMod 2) V) v) := by
    intro g v
    change ρ g v = ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]
  rw [← fixedCodim_map_equivariant ρ σ e.toMonoidHom (LinearEquiv.refl _ _) hact,
    rank_map_injective e.toMonoidHom e.injective]
  exact hd

/-- The literal degree-window consumer used by the existing K.4 assembly.
The complete displacement argument uses no small-module recognition input. -/
theorem boundedSourceExclusion_ru_of_groupFacts
    (hcenter : ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
      Nonempty (L ⧸ center L ≃* Rudvalis.Model) → IsPGroup 2 (center L))
    (hrank : IsSimpleGroup Rudvalis.Model → Group.IsPerfect Rudvalis.Model →
      primeRank 2 Rudvalis.Model ≤ 6)
    (hstable : IsSimpleGroup Rudvalis.Model → Group.IsPerfect Rudvalis.Model →
      ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
        (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
          MulAction.stabilizer Rudvalis.Model y) : BoundedSourceExclusion.{u,v} .ru 36 := by
  intro G V _ _ _ _ _ ρ h he _
  exact sourceExclusion_ru_of_groupFacts hcenter hrank hstable ρ h he

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisDirect
