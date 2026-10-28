module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.FullCore
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreGeneration
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.OriginalSylow
/-!
# The original block core and commutator Sylow

For the actual conjugate pair from the Fundamental Setup, whole-core
residual generation identifies O₂(L) with the intrinsic U-layer. The
original natural-block Sylow calculation consequently needs no separate
core-equality hypothesis. Every subgroup and conjugation is the original
one in G; the comparison subgroup H retains its genuine H* and nonzero
omega-center commutator hypotheses.

Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

theorem source_original_block_core_eq_blockU
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    pCore 2 L = blockU L := by
  let X := localJoin T L
  let A := L.subgroupOf X
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tX : X := ⟨t,(show (T : Subgroup G) ≤ X from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tX).toMonoidHom
  have hbB : IsBlock B := hb.map_equiv (MulAut.conj tX)
  have hmapA : A.map X.subtype = L := map_subgroupOf_eq_of_le hLX
  have hmapB : B.map X.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tX).toMonoidHom from rfl,map_map]
    rw [show X.subtype.comp (MulAut.conj tX).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map X.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLX).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLX).symm))
  have hc := hb.commutator_eq_bot_of_quasisimple_quotient hbB hqA hne
  have hmapPair : (A ⊔ B).map X.subtype = localOrbit T L := by
    rw [Subgroup.map_sup,hmapA,hmapB,hpair]
  have hR : pResidual 2 X = A ⊔ B := by
    apply map_injective X.subtype_injective
    exact (source_join_residual D).trans hmapPair.symm
  let a : A ≃* L := subgroupOfEquivOfLe hLX
  let b : A ≃* B := (MulAut.conj tX).subgroupMap A
  let f : B ≃* L := b.symm.trans a
  have hZB : center B = ⊥ := by
    apply bot_unique
    intro z hzB
    have hzL : f z ∈ center L := (centerCongr f ⟨z,hzB⟩).property
    rw [source_original_block_center_eq_bot D hn hb hz,mem_bot] at hzL
    exact mem_bot.mpr (f.injective (hzL.trans f.map_one.symm))
  have hmov : pCore 2 X = ⁅pCore 2 X,A ⊔ B⁆ := by
    rw [←hR]
    exact source_original_full_core_moved D e hn hb hz hH hZH
  have hcore := hb.core_eq_blockU_of_pair_core_generated hbB hc hZB hmov
  have hm := congrArg (map a.toMonoidHom) hcore
  rw [pCore_map_iso,RankOne.Solvable.blockU_map_equiv] at hm
  exact hm

/-- The original source hypotheses discharge the core input of the literal Sylow calculation. -/
theorem source_original_natural_commutator_sylow_of_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (A : Subgroup G) (hL : IsL2EvenBlock L 2)
    (hS : Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (localOrbit T L ⊔ ChapterB.baumann (T : Subgroup G)))
    (hAL : A ≤ L) (hA : Nat.card A = 3)
    (hAS : A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (hSL : ChapterB.baumann (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ⁅ChapterB.baumann (T : Subgroup G),A⁆ = ChapterB.baumann (T : Subgroup G) ⊓ L ∧
      Chapter1.IsSylowIn 2 ⁅ChapterB.baumann (T : Subgroup G),A⁆ L := by
  exact source_original_natural_commutator_sylow D A hL
    (source_original_block_core_eq_blockU D e hn hb hz hH hZH) hS hAL hA hAS hSL

end CFSG.Quasithin.Chapter10
