module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannPairFactor

/-!
# The Baumann factor for a prescribed Sylow conjugator

The source recognition of the first centralizer as a dihedral square
transports to every prescribed Sylow conjugate. This retains the conjugator
chosen by the direct-product assembly, avoiding a second existential choice.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_zero_baumann_conjugate_factor_dihedral_square
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥)
    (t : localJoin T L) (ht : (t : G) ∈ (T : Subgroup G)) :
    let H := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
    Nonempty (((ChapterB.baumann (S : Subgroup H) ⊓ centralizer
      ((L.subgroupOf H).map (MulAut.conj t).toMonoidHom : Set H) : Subgroup H) ≃*
        (DihedralGroup 4 × DihedralGroup 4))) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let R := ChapterB.baumann (S : Subgroup H)
  let A := L.subgroupOf H
  obtain ⟨eA⟩ := source_a5_zero_baumann_factor_dihedral_square D e hn hout hz
  have hnormalizer : t ∈ normalizer (R : Set H) := by
    apply (normalizer_le_normalizer_baumann (S : Subgroup H))
    exact (S : Subgroup H).le_normalizer ht
  have hR : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp hnormalizer
  let B := A.map (MulAut.conj t).toMonoidHom
  have hmap : (R ⊓ centralizer (A : Set H)).map
      (MulAut.conj t).toMonoidHom = R ⊓ centralizer (B : Set H) :=
    inf_centralizer_conjugate_of_map_eq R A t hR
  exact ⟨(MulEquiv.subgroupCongr hmap.symm).trans
    (((MulAut.conj t).subgroupMap (R ⊓ centralizer (A : Set H))).symm.trans eA)⟩

end CFSG.Quasithin.Chapter10
