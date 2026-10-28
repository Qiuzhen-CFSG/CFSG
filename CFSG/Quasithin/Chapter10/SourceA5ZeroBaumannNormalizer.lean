module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannCoordinateImages
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerPair
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalizers for the two zero-center Baumann centralizers

The original paired quotient normalizes the original A₅ block.  The chosen
Sylow conjugator preserves the Baumann subgroup, so transporting that
normalizer statement gives the corresponding assertion for the conjugate
block.  These are the normalizer premises needed by the quotient-pair
commutator and direct-product assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false in
theorem source_a5_zero_baumann_pair_normalizers
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    let A := L.subgroupOf H
    let R := ChapterB.baumann (S : Subgroup H)
    ∃ t : S, A ≠ A.map (MulAut.conj (t : H)).toMonoidHom ∧
      R ≤ normalizer (A : Set H) ∧
      R ≤ normalizer
        (A.map (MulAut.conj (t : H)).toMonoidHom : Set H) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  let R := ChapterB.baumann (S : Subgroup H)
  obtain ⟨d,c,a,b,hR,haxis⟩ := source_a5_zero_baumann_coordinate_images D e hn hout hz
  obtain ⟨d',c',hex,hN,haxes⟩ := source_a5_zero_original_centralizer_axes D e hn hout hz
  have hFY :
      ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
        (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)) ≤ Y := by
    rintro _ ⟨v,hv,rfl⟩
    exact (c.action.groupEquiv.symm v).property
  have hRY : R ≤ Y.comap q := by
    change ChapterB.baumann (S : Subgroup H) ≤ Y.comap q
    rw [hR]
    exact comap_mono hFY
  have hRA : R ≤ normalizer (A : Set H) := hRY.trans hN
  obtain ⟨t,ht,hne,_,_,_,_,_,_⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  let tS : S := ⟨t,ht⟩
  have hnormalizer : (tS : H) ∈ normalizer (R : Set H) := by
    apply (normalizer_le_normalizer_baumann (S : Subgroup H))
    exact (S : Subgroup H).le_normalizer tS.property
  have hRmap : R.map (MulAut.conj (tS : H)).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp hnormalizer
  have hRB : R ≤ normalizer
      (A.map (MulAut.conj (tS : H)).toMonoidHom : Set H) := by
    have hm := Subgroup.map_mono (f := (MulAut.conj (tS : H)).toMonoidHom) hRA
    rw [map_equiv_normalizer_eq A (MulAut.conj (tS : H)), hRmap] at hm
    exact hm
  exact ⟨tS, by simpa [tS] using hne, hRA, hRB⟩

end CFSG.Quasithin.Chapter10
