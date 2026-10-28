module
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.Representation.BinaryAlternatingSixModels.CatalogueSource

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition
public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover.LocalStructure
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace
public import Theory.Representation.BinaryPermutation.EightNormalizer
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric

/-!
# Excluding whole alternating components on the strict marked module

The genuine small-degree catalogues exclude A6 and identify the A7 and A8
modules with their actual natural actions. The ambient normalizers retain
these coordinates. The A7 action has no rank-two type-a2 involution; the A8
moved-plane stabilizer is transitive, contradicting the strict marking.

`StrictWholePair` applies these exclusions to the original strict quotient.
Source: Aschbacher--Smith G.9.3(4),(9),(12), G.11.7 and 6.2.19,
printed pp.354,366--367,691.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholeAlternating
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {C : GroupClass}

/-- The full binary A6 degree catalogue excludes every whole A6 action in
the source degree range; no assumption on the location of the involution is needed. -/
theorem not_six
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V) (e : L ≃* alternatingGroup (Fin 6)) : False := by
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hs := BinaryAlternatingSix.alternating_degrees σ
  rcases hs with hs | hs | hs <;> omega

variable {B : LinearMap.BilinForm (ZMod 2) V} {v : V}
  {W : Submodule (ZMod 2) V} {X₀ : Subgroup X}
open BinaryPermutation

set_option backward.isDefEq.respectTransparency false in
/-- The G9 degree bound forces the actual A7 six-space. Its ambient natural
extension contains no type-a2 involution. -/
theorem not_seven
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V) (e : L ≃* alternatingGroup (Fin 7))
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (htype : ∀ u, B u (ρ a u)=0) : False := by
  let := h9.normal_H
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hb := Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hs := ChapterK.Alternating.sevenSmallDegreeSpectrum σ hf inferInstance (by omega)
  have hdim : finrank (ZMod 2) V = 6 := by rcases hs with hs | hs | hs <;> omega
  obtain ⟨f⟩ := ChapterK.Alternating.SevenSixSpace.of_point_fixed_or_dual σ hdim
    (ChapterK.Alternating.SevenSixSpace.fixed_or_dual
      ChapterK.Alternating.SevenSixSpace.pointSimpleDegrees _ hdim)
  let c := coreEquivNatural (Fin 7) (by decide)
  let E := f.toLinearEquiv.trans c.symm
  apply RankTwo.Symmetric.seven_extension_not_type_a2 L ρ h.faithful e E
    (fun l u => ?_) B h.alternating h.nondegenerate h.preserves a ha hr htype
  apply c.injective
  change c (c.symm (f (ρ l u))) =
    c (alternatingCoreRepresentation (Fin 7) (e l) (c.symm (f u)))
  rw [c.apply_symm_apply]
  have he := coreEquivNatural_equivariant (Fin 7) (by decide) (e l).val (c.symm (f u))
  change c (alternatingCoreRepresentation (Fin 7) (e l) (c.symm (f u))) =
    alternatingNaturalRepresentation (Fin 7) (e l) (c (c.symm (f u))) at he
  rw [he,c.apply_symm_apply]
  have hh := IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) u
  change f (ρ (e.symm (e l)) u) = alternatingNaturalRepresentation (Fin 7) (e l) (f u) at hh
  rw [e.symm_apply_apply] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- The whole A8 row has the actual deleted six-space action. Its rank-two
type-a2 moved plane is transitive, contradicting the original strict marking. -/
theorem not_eight
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hd : 6 ≤ finrank (ZMod 2) V) (e : L ≃* alternatingGroup (Fin 8))
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (htype : ∀ u, B u (ρ a u)=0)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) : False := by
  let := h9.normal_H
  obtain hsmall | ⟨hnat,_,_⟩ := Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternatives
    h9 (e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  · have := hsmall.2.1
    omega
  obtain ⟨e,f,hf⟩ := hnat
  let E := f.trans RankTwo.Symmetric.splitNaturalEquiv
  have hE (l : L) (u : V) : E (ρ l u) =
      alternatingNaturalRepresentation (Fin 8) (e l) (E u) := by
    change RankTwo.Symmetric.splitNaturalEquiv (f (ρ l u)) = _
    have hfl := hf l u
    change f (ρ l u) = BinaryLinearRecognition.orthogonalEightAction (e l) (f u) at hfl
    rw [hfl]
    exact RankTwo.Symmetric.symmetricOrthogonalEquiv_action (e l).val (f u)
  obtain ⟨q,hq,hact,hker⟩ := EightNormalizer.exists_ambient_hom ρ L e.toMonoidHom e.surjective E hE
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    (hker.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr h.faithful))
  let eqG := MonoidHom.ofInjective hqi
  have hA : alternatingGroup (Fin 8) ≤ q.range := by
    intro b hb
    obtain ⟨l,hl⟩ := e.surjective ⟨b,hb⟩
    exact ⟨l,(hq l).trans (congrArg Subtype.val hl)⟩
  have hind : q.range.index ≤ 2 := by
    have hi := Subgroup.index_antitone hA
    simpa only [alternatingGroup.index_eq_two] using hi
  have he (g : G) (u : V) : E (ρ g u) =
      ((naturalRepresentation (Fin 8)).comp q.range.subtype) (eqG g) (E u) := hact g u
  have hb := RankTwo.Symmetric.smallConjugateProducts_of_type_a2
    B ρ h.alternating h.nondegenerate h.faithful h.preserves a ha hr htype
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, RankTwo.movedSpace, map_one, sub_self, LinearMap.range_zero, finrank_bot] at hr
    omega
  apply hnt
  apply RankTwo.stabilizerTransitive_transport ρ _ eqG E he a
  apply RankTwo.Symmetric.eight_stabilizerTransitive q.range hind (eqG a)
  · exact fun h1 => ha1 (eqG.injective (h1.trans eqG.map_one.symm))
  · rw [←map_pow,ha,map_one]
  · exact hb.map eqG
  · exact (RankTwo.finrank_movedSpace_transport ρ _ eqG E he a).symm.trans hr

end CFSG.Quasithin.ChapterG.Section11.WholeAlternating
