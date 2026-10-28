module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.ComponentInputs
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.BinaryFourMarked.Classification
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Ambient
public import Theory.SpecificGroups.Symmetric.InnerAutomorphisms
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# Marked B.4 inputs for the original orthogonal quotient

The fixed-marking L₄ classification gives the natural, dual and literal
exterior-square actions. The checked exterior-coordinate comparison and
Aut(A₈) = S₈ identify the last action with the deleted permutation module
for the specified ambient marking.

For S₈, the original quadratic actor embeds in the full normalizer of the
irreducible A₈ action. The multiple-support displacement estimate forces a
singleton highest support, including actors outside A₈. Degree four is
excluded by the faithful ambient group order. Middle support gives the
exterior module, whose computed normalizer extends it to the actual S₈
action. Innerness of Aut(S₈) restores the specified ambient marking.

These are the two universal representation inputs consumed by the literal
middle-node quotient in OriginalSource.Source. No module catalogue, degree
bound, or changed final marking is assumed.

Source: Aschbacher–Smith B.4.2(9–10), B.4.5, printed pp.86–87,
and 13.8.25, printed pp.959–960/PDF pp.976–977. The imported exterior
comparison retains its ATLAS attribution and license in OrthogonalSix.Comparison.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open Representation Representation.BinaryOffender BinaryPermutation
open ChapterB.SmallRecognition.BinaryFourMarked
open ChapterK.Linear.OrthogonalSix
open BinaryLinear.OuterCyclic
open OrthogonalQuotient OrthogonalQuotient.B4Extraction FourStructure.ChiefFactors
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
open ChapterK.Linear.Recognition.BinaryCubicSieve
universe v
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem alternating_marking
    (σ : Representation (ZMod 2) H U)
    (a b : H ≃* alternatingGroup (Fin 8))
    (e : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (he : ∀ g v, e (σ g v) = alternatingNaturalRepresentation (Fin 8) (a g) (e v)) :
    ∃ f : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
      ∀ g v, f (σ g v) = alternatingNaturalRepresentation (Fin 8) (b g) (f v) := by
  let α : MulAut (alternatingGroup (Fin 8)) := a.symm.trans b
  obtain ⟨p, hp⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide)
      (by decide)).surjective α
  let τ := naturalRepresentation (Fin 8)
  let l : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ (τ.asGroupHom p)
  refine ⟨e.trans l, fun g v => ?_⟩
  have hconj := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) =>
    (f (a g) : Equiv.Perm (Fin 8))) hp
  change p * (a g : Equiv.Perm (Fin 8)) * p⁻¹ = (b (a.symm (a g)) : Equiv.Perm (Fin 8)) at hconj
  rw [a.symm_apply_apply] at hconj
  have hmul : p * (a g : Equiv.Perm (Fin 8)) = (b g : Equiv.Perm (Fin 8)) * p := by
    rw [← hconj]
    group
  change τ p (e (σ g v)) = τ (b g) (τ p (e v))
  rw [he]
  change τ p (τ (a g) (e v)) = _
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]

/-- B.4 on the component, preserving both the prescribed GL₄ marking and
the prescribed ambient S₈ marking. -/
theorem component_b4 (K : Subgroup H) (eH : H ≃* Equiv.Perm (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) :
    ComponentB4.{v} K eH eK := by
  let : Finite H := Finite.of_injective eH eH.injective
  intro E _ _ _ σ hf hi A hA hq hb
  have hratio : quadraticRatio σ ≤ 2 :=
    (quadraticRatio_le_two_iff σ).mpr ⟨A, hA, hq, hb⟩
  rcases marked_alternatives σ eK hf hi hratio with hn | ⟨e, he⟩
  · exact Or.inl hn
  · right
    let a : K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
      eK.trans (slEquivLinear 4).symm
    let b : K ≃* alternatingGroup (Fin 8) :=
      (eH.subgroupMap K).trans (MulEquiv.subgroupCongr hK)
    let c := BinaryFourExteriorCoordinates.equiv
    let f := e.trans (c.trans exteriorEquivNatural)
    have hinter (k : K) (w : E) : f (σ k w) =
        alternatingNaturalRepresentation (Fin 8) (sl4EquivAlternating (a k)) (f w) := by
      have hmark : natural eK k = (a k).val.toLin' := by
        apply LinearMap.ext
        intro x
        change eK k x = slEquivLinear 4 (a k) x
        change eK k x = slEquivLinear 4 ((slEquivLinear 4).symm (eK k)) x
        rw [MulEquiv.apply_symm_apply]
      change exteriorEquivNatural (c (e (σ k w))) = _
      rw [he]
      change exteriorEquivNatural (c (exteriorPower.map 2 (natural eK k) (e w))) = _
      rw [hmark, BinaryFourExteriorCoordinates.equiv_map, exteriorEquivNatural_intertwines]
      rfl
    obtain ⟨g, hg⟩ := alternating_marking σ (a.trans sl4EquivAlternating) b f hinter
    exact ⟨g, hg⟩

private theorem symmetric_marking
    (σ : Representation (ZMod 2) H U) (a b : H ≃* Equiv.Perm (Fin 8))
    (e : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (he : ∀ g v, e (σ g v) = naturalRepresentation (Fin 8) (a g) (e v)) :
    IsEightNatural σ b := by
  let α : MulAut (Equiv.Perm (Fin 8)) := a.symm.trans b
  obtain ⟨p, hp⟩ := (Equiv.Perm.conj_surjective_of_degree (by decide : 5 ≤ 8)
    (by decide)) α
  let τ := naturalRepresentation (Fin 8)
  let l : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ (τ.asGroupHom p)
  refine ⟨e.trans l, fun g v => ?_⟩
  have hconj := congrArg (fun f : MulAut (Equiv.Perm (Fin 8)) => f (a g)) hp
  change p * a g * p⁻¹ = b (a.symm (a g)) at hconj
  rw [a.symm_apply_apply] at hconj
  have hmul : p * a g = b g * p := by
    rw [← hconj]
    group
  change τ p (e (σ g v)) = τ (b g) (τ p (e v))
  rw [he, ← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]

/-- B.4 on the ambient S₈, retaining irreducibility on its marked A₈ and
the original quadratic actor, which may lie outside that component. -/
theorem symmetric_b4 (K : Subgroup H) (eH : H ≃* Equiv.Perm (Fin 8))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) :
    SymmetricB4.{v} K eH := by
  let : Finite H := Finite.of_injective eH eH.injective
  have hn : (K.map eH.toMonoidHom).Normal := hK ▸ inferInstance
  let : K.Normal := MulEquiv.normal_map_iff.mp hn
  let eK : K ≃* alternatingGroup (Fin 8) :=
    (eH.subgroupMap K).trans (MulEquiv.subgroupCongr hK)
  let e : K ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    eK.trans sl4EquivAlternating.symm
  intro E _ _ _ σ hf hi A hA hquad hbound
  let : IsIrreducible (σ.comp K.subtype) := hi
  let τ := modelAction σ e
  let : IsIrreducible τ := modelAction_irreducible σ hi e
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial τ
  have hτ := modelAction_injective σ hf e
  have hrH : primeRank 2 H ≤ 4 := by
    have hr := CharacteristicTwoIrreducible.primeRank_le_automorphisms σ K hf
    rw [Theory.GroupTheory.primeRank_equiv 2
      (MulAut.congr (e.trans Atlas.Order20160A8.sl4TwoEquivPSL))] at hr
    exact hr.trans BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  have hr : rank A ≤ 4 := by
    have hc := (primeRank_le_iff_elementary_card_le H).mp hrH A hA.2
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  let f := ambientToNormalizer σ e
  have hfi := ambientToNormalizer_injective σ hf e
  obtain ⟨he, hc, hb⟩ := ChapterK.Exceptional.cubic_actor_map_equivariant σ
    (normalizerRepresentation τ) f hfi (LinearEquiv.refl _ _)
    (fun _ _ => rfl) hA (isCubic_of_isQuadratic hquad) hbound
  have hr' : rank (A.map f) ≤ 4 := by rwa [rank_map_injective f hfi]
  obtain ⟨J, v, hv, hJ⟩ := exists_localHighestVector τ
  have hpos := Finset.card_pos.mpr (hJ.nonempty_of_faithful hτ hv)
  have hone : J.card = 1 := by
    by_contra hn
    exact (not_lt_of_ge hb) ((FourDisplacement.multiple_support_displacement τ hτ inferInstance)
      J v hv hJ (by omega) (A.map f) he hc hr')
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
  have no_endpoint (hend : i = 0 ∨ i = 2) : False := by
    have hd : Module.finrank (ZMod 2) E = 4 :=
      le_antisymm (hJ.finrank_le_four_of_endpoint hv hend) (four_le_finrank_of_faithful τ hτ)
    let : Finite E := Module.finite_of_finite (ZMod 2)
    let : Finite (BinaryLinear.GL E) :=
      Finite.of_injective (fun g : BinaryLinear.GL E => (g : E → E)) DFunLike.coe_injective
    let g : H →* BinaryLinear.GL E :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E).toMonoidHom.comp σ.asGroupHom
    have hg : Function.Injective g := by
      intro x y h
      apply hf
      exact congrArg LinearEquiv.toLinearMap h
    have hcard := Nat.card_le_card_of_injective g hg
    rw [Nat.card_congr eH.toEquiv, BinaryLinear.card_GL_of_finrank hd] at hcard
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial,
      BinaryLinear.order, Fin.prod_univ_succ] at hcard
  have hi : i = 1 := by
    fin_cases i
    · exact (no_endpoint (Or.inl rfl)).elim
    · rfl
    · exact (no_endpoint (Or.inr rfl)).elim
  subst i
  let c := hJ.middleRootExteriorEquiv hv
  let l := c.toLinearEquiv.symm.trans exteriorEquivNatural
  have hl (k : K) (w : E) : l (σ k w) =
      alternatingNaturalRepresentation (Fin 8) (sl4EquivAlternating (e k)) (l w) := by
    have hk : τ (e k) w = σ k w := by
      change σ (e.symm (e k) : K) w = σ k w
      rw [e.symm_apply_apply]
    have hm := LinearMap.congr_fun (c.symm.isIntertwining' (e k)) w
    change c.toLinearEquiv.symm (τ (e k) w) =
      Atlas.Order20160A8.Bivectors.exteriorMap (e k).val (c.toLinearEquiv.symm w) at hm
    change exteriorEquivNatural (c.toLinearEquiv.symm (σ k w)) = _
    rw [← hk, hm, exteriorEquivNatural_intertwines]
    rfl
  let q : ChapterB.QuasisimpleSource.ActionEquiv (σ.comp K.subtype)
      (alternatingNaturalRepresentation (Fin 8)) := {
    groupEquiv := e.trans sl4EquivAlternating
    linearEquiv := l
    intertwines := hl }
  obtain ⟨g, hgi, _, hgv⟩ := faithful_extension σ K hf q
  have hgs : Function.Surjective g := by
    have hh := Finite.surjective_of_injective (hgi.comp eH.symm.injective)
    intro p
    obtain ⟨r, hr⟩ := hh p
    exact ⟨eH.symm r, hr⟩
  let a : H ≃* Equiv.Perm (Fin 8) := MulEquiv.ofBijective g ⟨hgi, hgs⟩
  exact symmetric_marking σ a eH l hgv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
