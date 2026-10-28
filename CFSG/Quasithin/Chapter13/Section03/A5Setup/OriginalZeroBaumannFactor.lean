module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannPairFactor
public import CFSG.Quasithin.Chapter10.SourceA5ZeroPairKernelSplit
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCoreCommutatorSplit

/-!
# The original Baumann centralizer factor is a dihedral square

Under the original 13.3.1 hypotheses and the zero-center branch, the
literal Baumann centralizer of the original A₅ block is the preimage of a
transposition four-group and hence is a product of two dihedral groups.
Source: Aschbacher–Smith10.2.1 and13.3.2(2), pp.743 and884–885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem zero_baumann_factor_dihedral_square
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      let _ := D
      ∃ t : T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
        (L.subgroupOf (localJoin T L)).map (MulAut.conj (t : localJoin T L)).toMonoidHom ≠
          L.subgroupOf (localJoin T L) ∧
        Nonempty (((ChapterB.baumann (T.subtype
          (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) :
            Subgroup (localJoin T L)) ⊓ centralizer
          ((L.subgroupOf (localJoin T L)).map (MulAut.conj (t : localJoin T L)).toMonoidHom :
            Set (localJoin T L)) : Subgroup (localJoin T L)) ≃*
          (DihedralGroup 4 × DihedralGroup 4))) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  obtain ⟨t,hne,he⟩ :=
    Chapter10.source_a5_zero_baumann_pair_factor_dihedral_square D e hn hout hz
  exact ⟨D,t,hne,he⟩
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
