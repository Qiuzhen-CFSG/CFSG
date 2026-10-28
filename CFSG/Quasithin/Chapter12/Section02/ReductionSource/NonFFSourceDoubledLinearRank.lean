module
public import Theory.Representation.IrreduciblePairCentralizer
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Representation.GeneralLinearNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearCoordinates
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearCoordinates
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# The actual two-rank bound of the linear-three doubled automizer

The original inequivalent simple pair has no centralizing involution.
Every elementary two-subgroup of its full linear normalizer therefore
embeds in Aut(SL3), and perfectness embeds this in Aut(PSL3). The actual
ambient automizer embeds in that normalizer because its component image
is normal. This proves the 2n bound on the unchanged source orbit,
including nontrivial scalar centers and all field automorphisms.
The internal imports reuse the original characteristic-kernel and seed
coordinate implementation without changing its public interface.
The weak-closure and globalR bounds of 7.5.2 remain separate source duties.
Source: Aschbacher--Smith Table7.2.1 and 7.5.2, printed pp.698,700.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource

private theorem rank_of_marked_pair
    {H J P U X Y : Type*} [Group H] [Finite H] [Group J] [Group P]
    [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (σ : Representation (ZMod 2) P X) (τ : Representation (ZMod 2) P Y)
    [IsIrreducible σ] [IsIrreducible τ]
    (hσ : Function.Injective σ) (hne : ¬ Nonempty (σ.Equiv τ))
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal] (q : J →* P) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] (X × Y))
    (hE : ∀ j v, E (ρ (i j) v) = (σ.prod τ) (q j) (E v)) :
    primeRank 2 H ≤ primeRank 2 (MulAut P) := by
  let μ := σ.prod τ
  let γ : Representation (ZMod 2) H (X × Y) := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : γ (i j) = μ (q j) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [←he]
    exact hE j v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      exact ⟨q j,Units.ext (hres j).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨j,rfl⟩ := hq p
      exact ⟨i j,⟨j,rfl⟩,Units.ext (hres j)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [←himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  let : Finite (X × Y) := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) (X × Y)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (X × Y) =>
      (f : (X × Y) → (X × Y))) DFunLike.coe_injective
  have hmi : Function.Injective (actionHom μ) := by
    intro g h hgh
    apply hσ
    apply LinearMap.ext
    intro x
    exact congrArg (fun z : actionImage μ => (z.val.val (x,0)).1) hgh
  let a := MulEquiv.ofBijective (actionHom μ) ⟨hmi,μ.asGroupHom.rangeRestrict_surjective⟩
  let : Finite P := Finite.of_injective (actionHom μ) hmi
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
    (irreducible_pair_normalizer_rank_le σ τ hne)
  rwa [←primeRank_equiv 2 (MulAut.congr a)] at hr

private theorem linear_three_aut_rank (F : BinaryField) :
    primeRank 2 (MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)) ≤ 2*F.degree := by
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    Atlas.sl_perfect 3 (by decide)
  have hh := Theory.GroupTheory.primeRank_le_of_injective 2
    (quotientAut (center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)))
    MulAut.quotient_center_injective
  exact hh.trans (Matrix.PSL3Even.automorphism_two_rank_eq
    F.Carrier F.degree_pos F.card_eq).le

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem original_twisted_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier),
      ∃ q : L →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier, Function.Surjective q ∧
      (¬ Nonempty ((linearNatural F 3).Equiv
        ((linearNatural F 3).comp a.toMonoidHom))) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2]
        ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)),
      ∀ l v, E (doubledSeedAction L D.sourceOrbit
        D.sourceOrbit_component_normalizes l v) =
        ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom)) (q l) (E v) := by
  let := D.elementary
  obtain ⟨q,hq,hker,e,he⟩ :=
    @seed_linear_three_marking G _ _ T L V D D.elementary h F hmodel.some
  let : q.ker.Characteristic := hker
  obtain ⟨t,ht,hnt,hne,c,hmul,hc⟩ :=
    @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  let α := doubledTwist L t (D.sylow_normalizes_component ht)
  obtain ⟨a,ha⟩ := descend_twist q hq α
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  have hne' : ¬ Nonempty (σ.Equiv τ) := by
    rintro ⟨b⟩
    apply hne
    refine ⟨Representation.Equiv.mk ((e.trans b.toLinearEquiv).trans e.symm) ?_⟩
    intro l
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (e.symm (b (e (doubledSeedAction L V D.normalizes l v)))) =
      e (doubledSeedAction L V D.normalizes (α l) (e.symm (b (e v))))
    rw [e.apply_symm_apply,he,he,e.apply_symm_apply,←ha]
    exact LinearMap.congr_fun (b.isIntertwining' (q l)) (e v)
  let E := c.symm.trans (e.prodCongr e)
  have hE : ∀ l v, E (doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l v) = (σ.prod τ) (q l) (E v) := by
    intro l v
    obtain ⟨w,rfl⟩ := c.surjective v
    rw [←hc]
    simp only [E,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,LinearEquiv.prodCongr_apply]
    change (e (doubledSeedAction L V D.normalizes l w.1),
      e (doubledSeedAction L V D.normalizes (α l) w.2)) =
      (σ (q l) (e w.1),σ (a (q l)) (e w.2))
    rw [he,he,ha]
  exact ⟨a,q,hq,hne',E,hE⟩

/-- The original full doubled automizer has two-rank at most twice the actual field degree. -/
theorem sourceOrbit_linear_automizer_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) ≤ 2*F.degree := by
  obtain ⟨a,q,hq,hne,E,hE⟩ := D.original_twisted_coordinates h hd F hmodel
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  have hσ : Function.Injective σ := by
    intro g k hgk
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun hgk v
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  let i : L →* ChapterE.Automizer W := qN.comp (inclusion D.sourceOrbit_component_normalizes)
  have hi : i.range = (L.subgroupOf N).map qN := by
    ext z
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  let : i.range.Normal := hi ▸ Normal.map inferInstance qN
    W.normalizerMonoidHom.rangeRestrict_surjective
  exact (rank_of_marked_pair σ τ hσ hne
    (ChapterE.automizerRepresentation W) (ChapterE.automizerRepresentation_injective W)
    i q hq E hE).trans (linear_three_aut_rank F)

/-- Every involutory operator commuting with the original linear-three pair is trivial. -/
theorem sourceOrbit_linear_involution_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (f : Additive D.sourceOrbit ≃ₗ[ZMod 2] Additive D.sourceOrbit)
    (hsq : ∀ v, f (f v) = v)
    (hf : ∀ l v, f (doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l v) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l (f v)) :
    f = LinearEquiv.refl _ _ := by
  obtain ⟨a,q,hq,hne,E,hE⟩ := D.original_twisted_coordinates h hd F hmodel
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  let c := (E.symm.trans f).trans E
  have hcsq (v) : c (c v) = v := by
    simp only [c,LinearEquiv.trans_apply,E.symm_apply_apply,hsq,E.apply_symm_apply]
  have hc (g) (v) : c ((σ.prod τ) g v) = (σ.prod τ) g (c v) := by
    obtain ⟨l,rfl⟩ := hq g
    have hh := hE l (E.symm v)
    rw [E.apply_symm_apply] at hh
    change E (f (E.symm ((σ.prod τ) (q l) v))) =
      (σ.prod τ) (q l) (E (f (E.symm v)))
    rw [←hh,E.symm_apply_apply,hf,hE]
  have hid := irreducible_pair_centralizing_involution σ τ hne c hcsq hc
  apply LinearEquiv.ext
  intro v
  apply E.injective
  have hh := LinearEquiv.congr_fun hid (E v)
  simpa only [c,LinearEquiv.trans_apply,E.symm_apply_apply,LinearEquiv.refl_apply] using hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
