module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.NormalizerGrowth
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourGraphRoots

/-!
# The characteristic plane of the actual prepared graph centralizer

The marked fixed diagram and its literal source Sylow identify C_sourceS(f)
with the symplectic unipotent group times the central graph factor. Its
center–derived intersection has order q² and exponent two. The cyclic
field action places that entire characteristic plane inside T∩L. Its
ambient normalizer preserves the plane, and the original graph involution
is outside it.

This is the fixed-Sylow geometry of F.4.37 for the same graph actor in the
original degree-two comparison, in either orientation and including q=4.
The full C_T(f) can be larger; no equality with this source centralizer,
nor with a maximizing outer centralizer, is asserted.

Source: Aschbacher–Smith F.4.37, printed p.293 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable {G : Type*} [Group G] [Finite G]
namespace UnitarySource
private def centralizerAmbientEquiv (A : Subgroup G) (f : A) :
    centralizer ({f} : Set A) ≃* (A ⊓ centralizer ({f.val} : Set G) : Subgroup G) :=
  ((centralizer ({f} : Set A)).equivMapOfInjective A.subtype A.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_subtype_centralizer_singleton A f))

private def fixedSylowEquiv {K : Type*} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hK : Nat.card K=2^m) (hm : 1≤m)
    (A S : Subgroup G) (f : A)
    (hs : Chapter1.IsSylowIn 2 S (A ⊓ centralizer ({f.val} : Set G)))
    (D : Subgroup (SymplecticFour.Sp K)) (hD : SymplecticFour.unipotent ≤ D)
    (e : centralizer ({f} : Set A) ≃* (D × UnitaryFourOuter.C2)) :
    S ≃* ((SymplecticFour.unipotent (F := K)) × UnitaryFourOuter.C2) := by
  let Q := Classical.choose hs
  have hQ := Classical.choose_spec hs
  let a := (centralizerAmbientEquiv A f).symm.trans e
  let R := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : Q ≃* S := ((Q : Subgroup _).equivMapOfInjective
    (A ⊓ centralizer ({f.val} : Set G)).subtype
    (A ⊓ centralizer ({f.val} : Set G)).subtype_injective).trans (MulEquiv.subgroupCongr hQ)
  let c : Q ≃* R := (Q : Subgroup _).equivMapOfInjective a.toMonoidHom a.injective
  exact b.symm.trans (c.trans (fixed_overgroup_sylow_equiv hK hm D hD R))

end UnitarySource
variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
include d h hH hp hm hc

/-- The same graph actor has a nontrivial characteristic root plane of order
q² in its original source centralizer. The complete fixed diagram and its
central graph marking are retained alongside the intrinsic calculation. -/
theorem Preparation.unitaryFour_graph_characteristic_plane :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        f.val ∈ sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        (∀ i : Fin 2, Chapter1.IsSylowIn 2
          (sourceS L H ⊓ centralizer ({f.val} : Set G))
          (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
            centralizer ({f.val} : Set G))) ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) = (1,UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) = (1,UnitaryFourOuter.generator))) ∧
        let P := sourceS L H ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Nonempty (P ≃* ((SymplecticFour.unipotent (F := PointLocal.FixedField m)) ×
          UnitaryFourOuter.C2)) ∧
        Nat.card Z = (2^m)^2 ∧ Z ≠ ⊥ ∧
        (∀ z ∈ Z, z^2=1) ∧
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
        normalizer (P : Set G) ≤ normalizer (Z : Set G) ∧ f.val ∉ Z := by
  obtain ⟨hm',hn,f,hfS,hfT,hf,ho,hor,_,hlocal,hdiagram⟩ :=
    d.unitary_graph_local_sylow h hH hp m hm hc
  let P := sourceS L H ⊓ centralizer ({f.val} : Set G)
  let Z := (center P ⊓ _root_.commutator P).map P.subtype
  have he : Nonempty (P ≃* ((SymplecticFour.unipotent (F := PointLocal.FixedField m)) ×
      UnitaryFourOuter.C2)) := by
    rcases hdiagram with ⟨e,_⟩ | ⟨e,_⟩
    · exact ⟨UnitarySource.fixedSylowEquiv (PointLocal.fixedField_card m hm) hm _ P
        (inclusion inf_le_left f) (hlocal 0) _
        (SymplecticFour.unipotent_le_borel.trans inf_le_left) e.left⟩
    · exact ⟨UnitarySource.fixedSylowEquiv (PointLocal.fixedField_card m hm) hm _ P
        (inclusion inf_le_left f) (hlocal 0) _
        (SymplecticFour.unipotent_le_borel.trans inf_le_right) e.left⟩
  obtain ⟨e⟩ := he
  have hcard : Nat.card Z = (2^m)^2 := by
    rw [card_map_of_injective P.subtype_injective,
      Nat.card_congr (centerDerivedEquiv e).toEquiv]
    exact fixed_product_center_derived_card (PointLocal.fixedField_card m hm) hm'
  have hsq : ∀ z ∈ Z, z^2=1 := by
    rintro _ ⟨z,hz,rfl⟩
    have hh := fixed_product_center_derived_square
      (PointLocal.fixedField_card m hm) hm' (e z) (centerDerivedEquiv e ⟨z,hz⟩).property
    have hz2 : z^2=1 := e.injective (by simpa only [map_pow,map_one] using hh)
    exact congrArg Subtype.val hz2
  have hPT : P ≤ (T : Subgroup G) :=
    inf_le_left.trans (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
  have hder : (_root_.commutator P).map P.subtype ≤ (T : Subgroup G) ⊓ L := by
    rw [map_subtype_commutator]
    have ht := d.unitaryFour_sylow_commutator_le_inner h hH hp m hm (.inr hc)
    rw [map_subtype_commutator] at ht
    exact (commutator_mono hPT hPT).trans ht
  have hZL : Z ≤ (T : Subgroup G) ⊓ L := (map_mono inf_le_right).trans hder
  refine ⟨hm',hn,f,hfS,hfT,hf,ho,hor,hlocal,hdiagram,⟨e⟩,hcard,?_,hsq,
    le_inf hZL ((map_subtype_le _).trans inf_le_right),
    normalizer_le_normalizer_characteristic_image P (center P ⊓ _root_.commutator P),
    fun hfZ => ho (hZL hfZ).2⟩
  intro hh
  have hzcard : Nat.card Z=1 := card_eq_one.mpr hh
  have hq : 1<2^m := Nat.one_lt_pow (by omega) (by decide)
  have hq2 : 1<(2^m)^2 := Nat.one_lt_pow (by decide) hq
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
