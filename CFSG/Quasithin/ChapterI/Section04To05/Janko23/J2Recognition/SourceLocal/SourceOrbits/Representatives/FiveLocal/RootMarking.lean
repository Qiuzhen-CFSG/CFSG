module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.Placement
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.InternalPairs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.RootMarking.Preparation

/-!
# Compatible marked normalizers for the five-local A₄ pair

The pair root is literally `(D.X ⊔ Y.val).pCoreIn 2`. The preparation
identifies it with a conjugate of the 47.1 root and puts both source cubic
endpoints in the first factor of its transported normalizer. Equality of
orders then identifies that factor with the actual join. Replacing its
abstract A₄ coordinates by this inclusion gives the required marking
`j ↦ (j, 1)`. The second factor is the intrinsic layer and contains a
conjugate of the distinguished involution.

`rootPairCoordinates_nonempty` assumes only the selected 47.1 geometry,
the placed 47.2 component, five-family separation from 47.2, and the marked
Sylow-three conclusion of 47.3. `internalPairs_with_root` applies it to
the actual internal edge. The existing `RootFixer` results then identify
the pair fixer and its involution fusion. The independent full component
normalizer and final `FiveLocalPairs` assembly remain with their owners.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1–47.3 and the second
paragraph of 47.5, printed pp.259–263.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
open InvolutionGeometry PrimeNormalizers.ThreeLocal
namespace RootMarking
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- Transport the actual 47.1 normalizer, then use 47.3 to mark its first factor
by the literal pair join. -/
theorem coordinates_of_conjugate_root (S : SelectedGeometry D)
    (hSyl : ∀ Q : Sylow 3 G, Nonempty (SylowThreeStructure D Q))
    (Y : D.Vertex) (eJ : pairJoin D Y ≃* A4)
    (g : G) (hg : (rootCore S.t).map (MulAut.conj g).toMonoidHom = pairRoot D Y) :
    Nonempty (RootPairCoordinates D Y) := by
  let N := rootNormalizer D Y
  let a := MulAut.conj g
  let N₀ := normalizer (rootCore S.t : Set G)
  have hN : N₀.map a.toMonoidHom = N := by
    rw [map_equiv_normalizer_eq, hg]
  let ne : N₀ ≃* N := (a.subgroupMap N₀).trans (MulEquiv.subgroupCongr hN)
  let e : N ≃* (A4 × A5) := ne.symm.trans S.normalizerEquiv
  let f : A4 × A5 →* G := N.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.symm.injective
  have hz : ∃ z : A5, IsConj D.z (f (1,z)) := by
    have hm := S.z_mem_component
    rw [← S.normalizer_component] at hm
    obtain ⟨b, hb, hbz⟩ := hm
    refine ⟨b.2, isConj_iff.mpr ⟨g, ?_⟩⟩
    have hb1 : b.1 = 1 := hb.1
    have hbe : ((1,b.2) : A4 × A5) = b := Prod.ext hb1.symm rfl
    change a D.z = f (1,b.2)
    rw [hbe, ← hbz]
    rfl
  have hNr : N ≤ f.range := by
    intro x hx
    exact ⟨e ⟨x,hx⟩, by simp [f]⟩
  have hJN : pairJoin D Y ≤ N := join_le_rootNormalizer D Y
  have hfirst : pairJoin D Y = ((⊤ : Subgroup A4).prod (⊥ : Subgroup A5)).map f := by
    apply eq_of_le_of_card_ge
    · exact sup_le
        (vertex_le_firstFactor hSyl f hf hz D.base ((le_sup_left.trans hJN).trans hNr))
        (vertex_le_firstFactor hSyl f hf hz Y ((le_sup_right.trans hJN).trans hNr))
    · rw [card_map_of_injective hf, Nat.card_congr (prodEquiv _ _).toEquiv,
        Nat.card_prod, card_top, card_bot, mul_one, Nat.card_congr eJ.toEquiv]
  let jToA : pairJoin D Y →* A4 :=
    (MonoidHom.fst A4 A5).comp (e.toMonoidHom.comp (inclusion hJN))
  have hsecond (j : pairJoin D Y) : (e (inclusion hJN j)).2 = 1 := by
    obtain ⟨b, hb, hj⟩ := hfirst.le j.property
    have he : e (inclusion hJN j) = b := by
      apply e.symm.injective
      apply Subtype.ext
      rw [e.symm_apply_apply]
      exact hj.symm
    rw [he]
    exact hb.2
  have hcoord (j : pairJoin D Y) : e (inclusion hJN j) = (jToA j,1) :=
    Prod.ext rfl (hsecond j)
  have hji : Function.Injective jToA := by
    intro x y he
    have hh : inclusion hJN x = inclusion hJN y := e.injective (by
      rw [hcoord, hcoord, he])
    exact Subtype.ext (congrArg (fun n : N => (n : G)) hh)
  have hjs : Function.Surjective jToA := by
    intro b
    let j : pairJoin D Y := ⟨f (b,1), hfirst.ge (mem_map.mpr
      ⟨(b,1), ⟨mem_top _, rfl⟩, rfl⟩)⟩
    refine ⟨j, ?_⟩
    change (e (inclusion hJN j)).1 = b
    have hi : inclusion hJN j = e.symm (b,1) := rfl
    rw [hi, e.apply_symm_apply]
  let eFirst : pairJoin D Y ≃* A4 := MulEquiv.ofBijective jToA ⟨hji,hjs⟩
  let E : N ≃* (pairJoin D Y × A5) :=
    e.trans (eFirst.symm.prodCongr (MulEquiv.refl A5))
  have hE (j : pairJoin D Y) : E (inclusion hJN j) = (j,1) := by
    change (eFirst.symm (e (inclusion hJN j)).1, (e (inclusion hJN j)).2) = (j,1)
    rw [hcoord]
    change (eFirst.symm (eFirst j),1) = (j,1)
    rw [eFirst.symm_apply_apply]
  have hEmbed (b : A5) :
      (N.subtype.comp E.symm.toMonoidHom) (1,b) = f (1,b) := by
    change (e.symm (eFirst 1,b) : G) = f (1,b)
    rw [map_one]
    rfl
  have hFactors :
      ((⊥ : Subgroup (pairJoin D Y)).prod (⊤ : Subgroup A5)).map
        (N.subtype.comp E.symm.toMonoidHom) =
      ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map f := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      have hb1 : b.1 = 1 := hb.1
      have he : b = (1,b.2) := Prod.ext hb1 rfl
      rw [he, hEmbed]
      exact mem_map.mpr ⟨(1,b.2), ⟨rfl,mem_top _⟩, rfl⟩
    · rintro ⟨b,hb,rfl⟩
      have hb1 : b.1 = 1 := hb.1
      have he : b = (1,b.2) := Prod.ext hb1 rfl
      rw [he]
      exact mem_map.mpr ⟨(1,b.2), ⟨rfl,mem_top _⟩, hEmbed b.2⟩
  have hLayer : ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map f =
      Representatives.rootComponent D Y := by
    change _ = (componentLayer N).map N.subtype
    rw [← layer_in_coordinates e, map_map]
  refine ⟨{
    joinEquiv := eJ
    normalizerEquiv := E
    normalizer_on_join := hE
    component_marking := hFactors.trans hLayer
    component_meets_z_class := ?_ }⟩
  obtain ⟨z,hz⟩ := hz
  exact ⟨f (1,z), hLayer ▸ mem_map.mpr ⟨(1,z), ⟨rfl,mem_top _⟩, rfl⟩, hz⟩

end RootMarking
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- Mark the literal root of any A₄ pair in the placed five-local component.
The only extra source inputs are the separated five-families of 47.2 and the
marked Sylow-three structure of 47.3. -/
theorem rootPairCoordinates_nonempty (S : SelectedGeometry D)
    (P : EarlierFive.PlacedComponent D S.t)
    (hsep : PrimeNormalizers.FiveLocal.TwoCentralFiveFamily D S.t)
    (hSyl : ∀ Q : Sylow 3 G, Nonempty (SylowThreeStructure D Q))
    (Y : D.Vertex) (hY : Y.val ≤ PrimeNormalizers.FiveLocal.fiveComponent P.F)
    (eJ : pairJoin D Y ≃* A4) : Nonempty (RootPairCoordinates D Y) := by
  obtain ⟨g,hg⟩ := RootMarking.core_is_conjugate S P hsep Y hY eJ
  exact RootMarking.coordinates_of_conjugate_root S hSyl Y eJ g hg

/-- Apply root marking to the actual edge built in the internal A₅ geometry.
The five-local assembly uses this edge and these coordinates in
`ComponentCoordinates.pairs` once its independent normalizer is supplied. -/
theorem internalPairs_with_root (S : SelectedGeometry D)
    (P : EarlierFive.PlacedComponent D S.t)
    (hsep : PrimeNormalizers.FiveLocal.TwoCentralFiveFamily D S.t)
    (hSyl : ∀ Q : Sylow 3 G, Nonempty (SylowThreeStructure D Q)) :
    ∃ I : InternalPairs D (PrimeNormalizers.FiveLocal.fiveComponent P.F),
      Nonempty (RootPairCoordinates D I.edge) := by
  obtain ⟨I⟩ := internalPairs_nonempty D _ (EarlierFive.componentEquiv P.witness) P.X_le
  exact ⟨I, rootPairCoordinates_nonempty S P hsep hSyl I.edge I.edge_le I.edge_join⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
