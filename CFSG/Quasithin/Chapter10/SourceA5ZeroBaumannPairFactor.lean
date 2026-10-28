module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannFactor
public import Theory.GroupTheory.SubgroupSectionConjugation

/-!
# Both original Baumann factor centralizers are dihedral squares

The first original factor centralizer is recognized directly from the
natural-kernel source. The prescribed Sylow conjugator normalizes the
Baumann subgroup and carries the first block to the second, so conjugation
transports that dihedral-square equivalence to the second factor. The
quotient marking and the chosen original conjugator remain unchanged.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_zero_baumann_pair_factor_dihedral_square
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    ∃ t : S, (L.subgroupOf H).map (MulAut.conj (t : H)).toMonoidHom ≠ L.subgroupOf H ∧
      Nonempty (((ChapterB.baumann (S : Subgroup H) ⊓ centralizer
        ((L.subgroupOf H).map (MulAut.conj (t : H)).toMonoidHom : Set H) : Subgroup H) ≃*
          (DihedralGroup 4 × DihedralGroup 4))) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let R := ChapterB.baumann (S : Subgroup H)
  let A := L.subgroupOf H
  obtain ⟨eA⟩ := source_a5_zero_baumann_factor_dihedral_square D e hn hout hz
  obtain ⟨t,ht,hne,hcomm,_,_,_,_,_⟩ := source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  let tS : S := ⟨t,ht⟩
  have hnormalizer : (tS : H) ∈ normalizer (R : Set H) := by
    apply (normalizer_le_normalizer_baumann (S : Subgroup H))
    exact (S : Subgroup H).le_normalizer tS.property
  have hR : R.map (MulAut.conj (tS : H)).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp hnormalizer
  let B := A.map (MulAut.conj (tS : H)).toMonoidHom
  have hmap : (R ⊓ centralizer (A : Set H)).map
      (MulAut.conj (tS : H)).toMonoidHom = R ⊓ centralizer (B : Set H) :=
    inf_centralizer_conjugate_of_map_eq R A (tS : H) hR
  refine ⟨tS,?_,?_⟩
  simpa [tS] using hne.symm
  exact ⟨(MulEquiv.subgroupCongr hmap.symm).trans
    (((MulAut.conj (tS : H)).subgroupMap (R ⊓ centralizer (A : Set H))).symm.trans eA)⟩

end CFSG.Quasithin.Chapter10
