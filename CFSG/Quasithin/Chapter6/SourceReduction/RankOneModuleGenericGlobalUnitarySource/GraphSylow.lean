module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourGraphSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors

/-!
# A common graph-fixed Sylow for the prepared source parabolics

The fixed whole-overlap centralizer can be saturated inside the original
sourceS. Its symplectic model has Sylow order 2q⁴, the same as both fixed
parabolics. Subgroup inclusions and equality of these orders therefore
promote the very same C_sourceS(f) to a Sylow subgroup in both original
source-parabolic centralizers. Every map is the literal subgroup inclusion.
The graph involution remains in sourceS ≤ T and outside both original
residuals, and both fixed-amalgam squares retain the marked graph generator.
Both comparison orientations and q=4 are preserved, with m>1 and n=2m.

Source: Aschbacher–Smith F.4.37, printed p.293 of `refs/quasithin.pdf`.
This establishes the local fixed Sylow inputs. The source normalizer
argument promoting C_T(f) to Sylow in C_G(f), full-normalizer realization,
outer transfer and F.4.42–43 remain further obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

namespace UnitarySource
private def centralizerAmbientEquiv (P : Subgroup G) (x : P) :
    centralizer ({x} : Set P) ≃* (P ⊓ centralizer ({x.val} : Set G) : Subgroup G) :=
  ((centralizer ({x} : Set P)).equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_subtype_centralizer_singleton P x))

omit [Finite G] in
private theorem image_fixed (B S : Subgroup G) (U : Subgroup B)
    (hU : U.map B.subtype = S) (f : B) :
    (U ⊓ centralizer ({f} : Set B)).map B.subtype =
      S ⊓ centralizer ({f.val} : Set G) := by
  ext x
  constructor
  · rintro ⟨x,⟨hx,hc⟩,rfl⟩
    exact ⟨hU.le (mem_map_of_mem B.subtype hx),mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩
  · rintro ⟨hx,hc⟩
    obtain ⟨y,hy,he⟩ := hU.ge hx
    subst x
    exact ⟨y,⟨hy,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hc))⟩,rfl⟩

private theorem exists_local_sylow (S P : Subgroup G) (hp : IsPGroup 2 S) (hSP : S ≤ P)
    (hcard : ∀ Q : Sylow 2 P, Nat.card Q = Nat.card S) :
    ∃ Q : Sylow 2 P, (Q : Subgroup P).map P.subtype = S := by
  obtain ⟨Q,hQ⟩ := (hp.comap_subtype (K := P)).exists_le_sylow
  refine ⟨Q,?_⟩
  apply le_antisymm
  · exact (eq_of_le_of_card_ge (show S ≤ (Q : Subgroup P).map P.subtype by
      rw [←map_subgroupOf_eq_of_le hSP]
      exact map_mono hQ) (by rw [card_map_of_injective P.subtype_injective,hcard Q])).ge
  · rw [←map_subgroupOf_eq_of_le hSP]
    exact map_mono hQ
private theorem fixed_local_sylows (P : Fin 2 → Subgroup G) (S : Subgroup G)
    (U : Sylow 2 (P 0 ⊓ P 1 : Subgroup G))
    (hU : (U : Subgroup _).map (P 0 ⊓ P 1).subtype = S)
    (f : (P 0 ⊓ P 1 : Subgroup G)) (a : ℕ)
    (hs : ∃ Q : Sylow 2 (centralizer ({f} : Set (P 0 ⊓ P 1 : Subgroup G))),
      (Q : Subgroup _).map (centralizer ({f} : Set (P 0 ⊓ P 1 : Subgroup G))).subtype =
        (U : Subgroup _) ⊓ centralizer ({f} : Set (P 0 ⊓ P 1 : Subgroup G)))
    (hb : ∀ Q : Sylow 2 (centralizer ({f} : Set (P 0 ⊓ P 1 : Subgroup G))), Nat.card Q = a)
    (hl : ∀ Q : Sylow 2 (centralizer ({(inclusion inf_le_left f)} : Set (P 0))), Nat.card Q = a)
    (hr : ∀ Q : Sylow 2 (centralizer ({(inclusion inf_le_right f)} : Set (P 1))), Nat.card Q = a) :
    Nat.card (S ⊓ centralizer ({f.val} : Set G) : Subgroup G) = a ∧
    (∀ i : Fin 2, ∃ Q : Sylow 2 (P i ⊓ centralizer ({f.val} : Set G) : Subgroup G),
      (Q : Subgroup _).map (P i ⊓ centralizer ({f.val} : Set G)).subtype =
        S ⊓ centralizer ({f.val} : Set G)) := by
  let B := P 0 ⊓ P 1
  have himage := image_fixed B S (U : Subgroup B) hU f
  have hcard : Nat.card (S ⊓ centralizer ({f.val} : Set G) : Subgroup G) = a := by
    obtain ⟨Q,hQ⟩ := hs
    rw [←himage,card_map_of_injective B.subtype_injective,←hQ,
      card_map_of_injective (centralizer ({f} : Set B)).subtype_injective]
    exact hb Q
  have hSB : S ≤ B := hU ▸ map_subtype_le _
  have hS : IsPGroup 2 S := hU ▸ U.isPGroup'.map B.subtype
  refine ⟨hcard,?_⟩
  intro i
  have hi : B ≤ P i := by fin_cases i; exact inf_le_left; exact inf_le_right
  have hf : f.val ∈ P i := hi f.property
  apply exists_local_sylow _ _ (hS.to_le inf_le_left) (inf_le_inf_right _ (hSB.trans hi))
  intro Q
  let e := centralizerAmbientEquiv (P i) ⟨f.val,hf⟩
  let R := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have he : Nat.card R = a := by
    fin_cases i
    · exact hl R
    · exact hr R
  change Nat.card ((Q : Subgroup _).map e.symm.toMonoidHom) = _ at he
  rw [card_map_of_injective e.symm.injective] at he
  exact he.trans hcard.symm

end UnitarySource

/-- The prepared degree-two row supplies a graph involution whose centralizer
in the original sourceS is Sylow in both source-parabolic centralizers, of
order 2q⁴. Its full fixed diagram retains the marked central graph factor. -/
theorem Preparation.unitary_graph_local_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        f.val ∈ sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        Nat.card (sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) = 2*(2^m)^4 ∧
        (∀ i : Fin 2, ∃ Q : Sylow 2
          (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
            centralizer ({f.val} : Set G) : Subgroup G),
          (Q : Subgroup _).map
            (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
              centralizer ({f.val} : Set G)).subtype =
                sourceS L H ⊓ centralizer ({f.val} : Set G)) ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) = (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) = (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator))) := by
  have hm' := d.unitaryExtension_local_structure h hH.1.1.2 hp m hm hc
  refine ⟨hm'.1,hm'.2.1,?_⟩
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let B := P 0 ⊓ P 1
  let α := sourceParabolicAmalgam ![L,residual H] (sourceS L H)
  have hs : ∃ U : Sylow 2 B, (U : Subgroup B).map B.subtype = sourceS L H := by
    change ∃ U : Sylow 2 (P 0 ⊓ P 1 : Subgroup G),
      (U : Subgroup (P 0 ⊓ P 1 : Subgroup G)).map (P 0 ⊓ P 1).subtype = sourceS L H
    have hf := d.hypothesisF11 h hH.1.1.2
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  refine hs.elim fun U hU => ?_
  have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i) = solvableResidual (P i) := by
    rw [←d.parabolic_residuals h hH.1.1.2 hp i]
    exact comap_map_eq_self_of_injective (P i).subtype_injective _
  refine (ChapterF.UnitarySource.FourGraph.comparison_graph_saturated m hm α U hc).elim fun f hf => ?_
  have hfU := hf.1
  have hf2 := hf.2.1
  have hfl := hf.2.2.1
  have hfr := hf.2.2.2.1
  have hfs := hf.2.2.2.2.1
  have hfe := hf.2.2.2.2.2
  have hfS : f.val ∈ sourceS L H := hU.le (mem_map_of_mem B.subtype hfU)
  have hcounts := ChapterF.UnitarySource.FourGraph.fixed_diagram_sylow_card_marked m hm α f hfe
  have hdata := UnitarySource.fixed_local_sylows P (sourceS L H) U hU f (2*(2^m)^4)
    hfs hcounts.2.1 hcounts.1 hcounts.2.2
  refine ⟨f,hfS,sourceS_le_sylow h.sylow_normalizes hH.1.1.2 hfS,
    (Subgroup.orderOf_coe f).trans hf2,?_,?_,hdata.1,hdata.2,hfe⟩
  · intro hfL
    exact hfl ((hres 0) ▸ hfL)
  · intro hfR
    exact hfr ((hres 1) ▸ hfR)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
