module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingGeometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.SwappingSplit
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.ResidualCentralizer

/-!
# Split geometry on the original swapping sixteen at the original G,T

Sylow conjugacy aligns the proved split model with the original T∩L.
The generated elementary sixteen A = ⟨s,[U,s]⟩ is therefore Jₑ(T∩L), and
the original T normalizes A. The model parabolic actions are transported
to this literal A and marked by the original flag point V₁.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
      q.right.map F.U.subtype)

include d setup structural alternatives hne hZ hcard g hgP hgH q hsX hs hout hswap

/-- Align the concrete split block with the original Sylow intersection,
rather than replacing T by a new choice. -/
theorem source_split_embedding_of_swapping :
    ∃ i : Matrix.PSL3Two.SplitParabolic.Block →* G,
      Function.Injective i ∧ i.range = L ∧
      Matrix.PSL3Two.SplitParabolic.standardSylow.map i = (T : Subgroup G) ⊓ L := by
  obtain ⟨e⟩ := source_split_model_of_swapping d setup structural alternatives F hne hZ hcard
    g hgP hgH q s hsX hs hout hswap
  have hLc : Nat.card L = 1344 := by
    rw [Nat.card_congr e.toEquiv, SemidirectProduct.card,
      Matrix.PSL3Two.SplitParabolic.card_E3, Matrix.PSL3Two.card_SL]
  let P : Sylow 2 L := Sylow.ofCard (((T : Subgroup G) ⊓ L).subgroupOf L) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right)).toEquiv]
    rw [(source_sylow_index d setup structural
      alternatives F hne hZ hcard).1, hLc]
    decide +kernel)
  let Q : Sylow 2 L := Matrix.PSL3Two.SplitParabolic.naturalSylow.mapSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨l,hl⟩ := MulAction.exists_smul_eq L Q P
  let i := L.subtype.comp ((MulAut.conj l).toMonoidHom.comp e.symm.toMonoidHom)
  have hmap : ((Matrix.PSL3Two.SplitParabolic.standardSylow.map e.symm.toMonoidHom).map
      (MulAut.conj l).toMonoidHom) = ((T : Subgroup G) ⊓ L).subgroupOf L := by
    change (↑(l • Q) : Subgroup L) = _
    rw [hl]
    rfl
  refine ⟨i, L.subtype_injective.comp ((MulAut.conj l).injective.comp e.symm.injective), ?_, ?_⟩
  · dsimp only [i]
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.symm.surjective, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (MulAut.conj l).surjective, ← MonoidHom.range_eq_map,L.range_subtype]
  · change (Matrix.PSL3Two.SplitParabolic.standardSylow.map
      (L.subtype.comp ((MulAut.conj l).toMonoidHom.comp e.symm.toMonoidHom))) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, hmap,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right)]

/-- The actual swapping sixteen is the elementary Thompson subgroup of the
original T∩L; consequently the original T normalizes it. -/
theorem source_swapping_thompson :
    Stellmacher.elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) =
      zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ ∧
    (T : Subgroup G) ≤ normalizer
      ((zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G) : Set G) := by
  let := setup.chosen.elementary
  let H := setup
  obtain ⟨i,hi,_,hSi⟩ := source_split_embedding_of_swapping d setup structural alternatives F
    hne hZ hcard g hgP hgH q s hsX hs hout hswap
  let f := i.comp Matrix.PSL3Two.SplitParabolic.sylowMap
  have hf : Function.Injective f := hi.comp Matrix.PSL3Two.SplitParabolic.sylowMap_injective
  have hrange : f.range = (T : Subgroup G) ⊓ L := by
    dsimp only [f]
    rw [MonoidHom.range_comp,Matrix.PSL3Two.SplitParabolic.sylowMap_range,hSi]
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  obtain ⟨_,he,hc⟩ := q.elementary_sixteen_of_swap F.U s (congrArg Subtype.val hs) hout hswap
  let : IsElementaryAbelian 2 A := he
  have hTL := (source_involution_sylow d setup structural
    alternatives F hne hZ hcard g s hgP hgH hsX
    (congrArg Subtype.val hs) hout).1
  have hAS : A ≤ (T : Subgroup G) ⊓ L := by
    rw [hTL]
    exact sup_le (zpowers_le.mpr (mem_sup_right (mem_zpowers (s : G))))
      (Subgroup.commutator_le_sup F.U (zpowers (s : G)))
  have hAR : A ≤ f.range := hrange.symm ▸ hAS
  let : IsElementaryAbelian 2 (A.comap f) := IsElementaryAbelian.comap_of_injective f hf A
  have hmap : (A.comap f).map f = A := map_comap_eq_self hAR
  have hc' : Nat.card (A.comap f) = 16 := by
    rw [← card_map_of_injective hf, hmap]
    exact hc
  have hle := Matrix.PSL3Two.SplitParabolic.Unitriangular.large_elementary_le (A.comap f)
    hc'.ge
  have hAe : A = Matrix.PSL3Two.SplitParabolic.Unitriangular.A.map f := by
    apply eq_of_le_of_card_ge
    · rw [← hmap]; exact map_mono hle
    · rw [card_map_of_injective hf,Matrix.PSL3Two.SplitParabolic.Unitriangular.card_A]
      exact hc.ge
  have hJ : Stellmacher.elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) = A := by
    rw [← hrange,DimensionFour.SplitImage.SplitParabolic.thompson_eq f hf]
    exact hAe.symm
  refine ⟨hJ,?_⟩
  change (T : Subgroup G) ≤ normalizer (A : Set G)
  rw [← hJ]
  have hN : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer (H.sylow_normalizes_at structural)).trans
      inf_normalizer_le_normalizer_inf
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq]
  change (Stellmacher.elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L)).map
    (MulAut.conj t).toMonoidHom = _
  rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj t)]
  exact congrArg Stellmacher.elementaryAbelianMaxJ
    (mem_normalizer_iff_map_conj_eq.mp (hN ht))

/-- The natural split block can be marked at the original ambient T∩L. -/
theorem source_aligned_natural_data_of_swapping [(V.subgroupOf L).Normal] :
    ∃ data : Matrix.PSL3Two.SplitParabolic.SplitNaturalData (V.subgroupOf L),
    ∃ i : L →* G, Function.Injective i ∧ i.range = L ∧
      DimensionFour.SplitImage.SplitParabolic.Natural.TL data i = (T : Subgroup G) ⊓ L := by
  obtain ⟨data⟩ := source_split_natural_data_of_swapping d setup structural alternatives F
    hne hZ hcard g hgP hgH q s hsX hs hout hswap
  have hLc : Nat.card L = 1344 := by
    rw [Nat.card_congr data.blockEquiv.toEquiv, SemidirectProduct.card,
      Matrix.PSL3Two.SplitParabolic.card_E3, Matrix.PSL3Two.card_SL]
  let P : Sylow 2 L := Sylow.ofCard (((T : Subgroup G) ⊓ L).subgroupOf L) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show (T : Subgroup G) ⊓ L ≤ L from inf_le_right)).toEquiv,
      (source_sylow_index d setup structural
        alternatives F hne hZ hcard).1,hLc]
    decide +kernel)
  obtain ⟨l,hl⟩ := MulAction.exists_smul_eq L
    (DimensionFour.SplitImage.SplitParabolic.Natural.sylow data) P
  let i := L.subtype.comp (MulAut.conj l).toMonoidHom
  refine ⟨data,i,L.subtype_injective.comp (MulAut.conj l).injective,?_,?_⟩
  · dsimp only [i]
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (MulAut.conj l).surjective,
      ← MonoidHom.range_eq_map,L.range_subtype]
  · change (data.markedPreimage Matrix.PSL3Two.borelSL).map
      (L.subtype.comp (MulAut.conj l).toMonoidHom) = _
    rw [← Subgroup.map_map,
      ← DimensionFour.SplitImage.SplitParabolic.Natural.sylow_coe]
    change (↑(l • DimensionFour.SplitImage.SplitParabolic.Natural.sylow data) : Subgroup L).map
      L.subtype = _
    rw [hl]
    exact map_subgroupOf_eq_of_le inf_le_right

omit d setup structural alternatives hne hZ hcard g hgP hgH q hsX hs hout hswap in
private def transportSourceParabolic {B C P S R : Subgroup G}
    (hBC : B=C) (hSR : S=R) (z : B) (w : C) (hz : (z : G)=(w : G))
    (p : ParabolicGenerators C P R w) : ParabolicGenerators B P S z := by
  subst C R
  have he : z=w := Subtype.ext hz
  subst w
  exact p

/-- The split parabolic actions are constructed on the literal generated
sixteen, marked by the original flag point. -/
theorem source_parabolic_generators_of_swapping :
    ∃ (P : Subgroup G) (z : (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G)),
      F.Vi 1 = zpowers (z : G) ∧
      Nonempty (ParabolicGenerators (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆)
        P ((T : Subgroup G) ⊓ L) z) := by
  let := setup.chosen.elementary
  have hV := (source_block_core d setup structural
    alternatives F hne hZ hcard).1
  let : (V.subgroupOf L).Normal := by
    rw [hV]
    change (Subgroup.comap L.subtype ((pCore 2 L).map L.subtype)).Normal
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    infer_instance
  obtain ⟨data,i,hi,_,hTL⟩ := source_aligned_natural_data_of_swapping d setup
    structural alternatives F hne hZ hcard g hgP hgH q s hsX hs hout hswap
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzTL : z ∈ DimensionFour.SplitImage.SplitParabolic.Natural.TL data i := by
    rw [hTL]
    have hzV : z ∈ V := F.le_seed 1 (hpoint ▸ mem_zpowers z)
    exact ⟨setup.chosen.le_sylow hzV,(hV.le.trans (L.pCoreIn_le 2)) hzV⟩
  have hzC : ∀ t ∈ DimensionFour.SplitImage.SplitParabolic.Natural.TL data i, z*t=t*z := by
    intro t ht
    rw [hTL] at ht
    have htH : t ∈ F.H := F.invariant 1 ht.1
    rw [F.H_eq_centralizer (by decide) z hpoint] at htH
    exact htH z (Set.mem_singleton z)
  let w := DimensionFour.SplitImage.SplitParabolic.Natural.sourcePoint data i hi z hzTL hz hzC
  have hA : Stellmacher.elementaryAbelianMaxJ
      (DimensionFour.SplitImage.SplitParabolic.Natural.TL data i) =
        zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ := by
    rw [hTL]
    exact (source_swapping_thompson d setup structural alternatives F hne hZ hcard
      g hgP hgH q s hsX hs hout hswap).1
  let zA : (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G) := ⟨z,hA ▸ w.property⟩
  refine ⟨DimensionFour.SplitImage.SplitParabolic.Natural.secondParabolic data i,zA,hpoint,?_⟩
  exact ⟨transportSourceParabolic hA.symm hTL.symm zA w rfl
    (DimensionFour.SplitImage.SplitParabolic.Natural.sourceGenerators data i hi z hzTL hz hzC)⟩
/-- The original marked split actions contradict the point-centralizer
prime restriction once the residual normalizer has its source index three.
The remaining index is an ambient lifting obligation of this source owner. -/
theorem source_swapping_outer_index_ne_three (hgL : g ∈ L) :
    (F.H.pCoreIn 2).relIndex
      ((pResidual 2 F.H).map F.H.subtype ⊓
        normalizer ((zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) : Set G)) ≠ 3 := by
  intro hthree
  obtain ⟨P,z,hpoint,⟨parabolic⟩⟩ := source_parabolic_generators_of_swapping
    d setup structural alternatives F hne hZ hcard g hgP hgH q s hsX hs hout hswap
  obtain ⟨quaternion⟩ := source_quaternion_generators_of_outer_index
    d setup structural alternatives F hne hZ hcard q g s hgL hgP hgH hsX
    (congrArg Subtype.val hs) hout hswap hthree
  exact source_no_markedLocalActions d setup structural alternatives F hne hZ hcard
    _ _ _ z hpoint (markedLocalActions_of_generators parabolic quaternion)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
