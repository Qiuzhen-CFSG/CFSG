module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryAutomizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoordinates

/-!
# The full automizer of the original binary doubled orbit

The component marking gives a faithful homomorphism from Aut_G(W) into
Aut(SL₃(2)). The original conjugator moves the seed, so its induced operator
is outer. Since the component already supplies all inner automorphisms,
the homomorphism is onto. The same coordinates identify seed preservation
with inner action and retain the second axis as the actual conjugate seed.

This discharges the full-automizer identification used throughout 7.6–7.7.
It does not supply the global r > 2 bound or centralizer-core construction;
those remain with qt-d-1222-nonff-doubled. The companion
`NonFFSourceDoubledBinaryFixed` applies this marking to actual centralizers.
Source: Aschbacher–Smith H.4.1 and 7.6–7.7, printed pp.380,701–709.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open BinaryLinearThree
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original chosen orbit has the full binary natural–dual automizer.
The same conjugator and both seed axes are retained, and preservation of the
original seed is exactly membership in the inner automorphism subgroup. -/
theorem sourceOrbit_binary_automizer_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* Group, Function.Surjective q ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
      ∃ a : ChapterE.Automizer D.sourceOrbit ≃* MulAut Group,
        (∀ l v, E (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l v) = NaturalDual.action (q l) (E v)) ∧
        (∀ l, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) = MulAut.conj (q l)) ∧
        (∀ n : normalizer (D.sourceOrbit : Set G),
          a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict n) ∈
            MulAut.innerSubgroup Group ↔ (n : G) ∈ normalizer (V : Set G)) ∧
        (∀ b g v, E (ChapterE.automizerRepresentation D.sourceOrbit b
          (E.symm (NaturalDual.action g (E v)))) =
          NaturalDual.action (a b g) (E (ChapterE.automizerRepresentation D.sourceOrbit b v))) ∧
        (∀ v, (E v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (E v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨t,ht,hnt,q,hq,E,hE,hV,hVt⟩ := D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  let i : L →* ChapterE.Automizer W :=
    qN.comp (inclusion D.sourceOrbit_component_normalizes)
  have hi : i.range = (L.subgroupOf N).map qN := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  let : i.range.Normal := hi ▸ Normal.map inferInstance qN
    W.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨f,hfi,hfL,hfc⟩ := doubledBinary_marked_automorphisms
    (ChapterE.automizerRepresentation W) (ChapterE.automizerRepresentation_injective W)
    i q hq E hE
  have hVW : V ≤ W := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  have hinner := doubledBinary_inner_iff_seed_normalizer V W hVW E hV f hfc
  let tN : N := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  have hout : f (qN tN) ∉ MulAut.innerSubgroup Group := by
    intro hh
    exact hnt ((hinner tN).mp hh)
  let a := MulEquiv.ofBijective f
    ⟨hfi,doubledBinary_onto_of_outer f i q hq hfL (qN tN) hout⟩
  exact ⟨t,ht,hnt,q,hq,E,a,hE,hfL,hinner,hfc,hV,hVt⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
