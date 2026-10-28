module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticConstrained
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.Partition
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.PairedCentralizer

/-!
# Excluding the prime-five A₇ row on its original moving support

The source partition preimage lies in M ∩ L, including its literal two-core
kernel. Its prime-to-three residual centralizes V because the marked
module-centralizer quotient is a {2,5}-group. The image of this residual
contains the paired A₄. Its full-cover automorphism fixer has order at
most four, contradicting the original moving action of order sixteen.

The consumer in Decomposable keeps the same component, Z₁ and source prime.
The partition premise is original 15.1.22(1), printed p.1098, before the
15.1.23 exclusion on p.1100. No exchanged-source or later index result is
used to obtain that premise or the contradiction.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterD ChapterD.UniqueFactor AlternatingSeven.ThreeResidualLocals
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem paired_le_partition_cubic_residual
    (p : Partition 7 4 ![2,2,2,1]) (c : Perm7)
    (hc : p.stabilizer = (centralizer ({pairing} : Set Perm7)).map
      (MulAut.conj c).toMonoidHom) :
    pairedFour.map (MulAut.conj c).toMonoidHom ≤
      (primeToResidual 3 (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup Perm7)).map
        (alternatingGroup (Fin 7) ⊓ p.stabilizer).subtype := by
  let Q := alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7)
  have hbase : pairedFour ≤ (primeToResidual 3 Q).map Q.subtype := by
    change pairedFour ≤ (primeToResidual 3
      (alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7) : Subgroup Perm7)).map _
    dsimp only [Q]
    rw [←pairedFour_normalizer_eq]
    apply (pairedFour_le_paired_threeResidual (alternatingGroup (Fin 7)) le_rfl).trans
    apply map_mono
    rw [primePowerGenerated_le_iff]
    intro x n hx
    exact mem_primeToResidual_of_pow hx
  have hA : (alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom =
      alternatingGroup (Fin 7) := Normal.map_conj_eq _ c
  have hQ : Q.map (MulAut.conj c).toMonoidHom = alternatingGroup (Fin 7) ⊓ p.stabilizer := by
    rw [show Q = alternatingGroup (Fin 7) ⊓ centralizer ({pairing} : Set Perm7) from rfl,
      Subgroup.map_inf _ _ _ (MulAut.conj c).injective,hA,←hc]
  have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hbase
  rw [map_embedded_primeToResidual 3 Q (MulAut.conj c),hQ] at hh
  exact hh

/-- The same prime-five source cannot have an A₇ partition alternative
when its original moving action has order sixteen. -/
theorem PreExclusionSource.not_alternatingSeven_of_image_sixteen (s : d.PreExclusionSource h.normalized 5)
    (hTM : (T : Subgroup G) ≤ M)
    {B : Subgroup G} (hBV : B ≤ V) (hn : B ≤ normalizer (d.L : Set G))
    (hcard : Nat.card (internalActionImage B d.L hn) = 16) :
    ¬ d.ConstrainedA7Alternative := by
  intro a
  obtain ⟨q,p,_,hp⟩ := a.partition
  let f := (alternatingGroup (Fin 7)).subtype.comp
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
  let P := p.stabilizer.comap f
  let R := (primeToResidual 3 P).map P.subtype
  have hk : f.ker = pCore 2 d.L := by
    rw [MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin 7)).subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ q.injective,QuotientGroup.ker_mk']
  have hkM : f.ker ≤ (M ⊓ d.L).subgroupOf d.L := by
    rw [hk]
    obtain ⟨S,hS⟩ := s.component_sylow
    have hcore : d.L.pCoreIn 2 ≤ d.SL := hS ▸ pCoreIn_le_sylow d.L S
    intro l hl
    exact ⟨hTM (d.S_le_T (d.SL_le_S (hcore (mem_map_of_mem d.L.subtype hl)))),l.property⟩
  have hP : P.map d.L.subtype ≤ M ⊓ d.L := by
    rintro g ⟨l,hl,rfl⟩
    have hh : f l ∈ ((M ⊓ d.L).subgroupOf d.L).map f :=
      hp ⟨(q (QuotientGroup.mk' _ l)).property,hl⟩
    have hmem : l ∈ (((M ⊓ d.L).subgroupOf d.L).map f).comap f := hh
    rw [Subgroup.comap_map_eq,sup_eq_left.mpr hkM] at hmem
    exact hmem
  have hRV : R.map d.L.subtype ≤ centralizer (V : Set G) := by
    rw [show R = (primeToResidual 3 P).map P.subtype from rfl,
      map_embedded_primeToResidual_of_hom]
    exact (embedded_primeToResidual_mono 3 hP).trans
      (s.cubic_residual_centralizes_of_prime_five (h := h))
  have hf : f.range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro g ⟨l,rfl⟩
      exact (q (QuotientGroup.mk' _ l)).property
    · intro g hg
      obtain ⟨l,hl⟩ := q.surjective.comp (QuotientGroup.mk'_surjective _) ⟨g,hg⟩
      exact ⟨l,congrArg Subtype.val hl⟩
  have hPf : P.map f = alternatingGroup (Fin 7) ⊓ p.stabilizer := by
    rw [show P = p.stabilizer.comap f from rfl,map_comap_eq,hf,inf_comm]
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have hi : pairedFour.map (MulAut.conj c).toMonoidHom ≤ R.map f := by
    rw [show R = (primeToResidual 3 P).map P.subtype from rfl,
      map_embedded_primeToResidual_of_hom,hPf]
    exact paired_le_partition_cubic_residual p c hc
  have hbound := a.block.seven_paired_residual_fixer_card_le_four q R c hi
    (internalActionImage B d.L hn) (by
      rintro α ⟨b,rfl⟩ r hr
      apply Subtype.ext
      change (b : G) * (r : G) * (b : G)⁻¹ = r
      have hh := hRV (mem_map_of_mem d.L.subtype hr) b (hBV b.property)
      change (b : G) * (r : G) = (r : G) * (b : G) at hh
      rw [hh,mul_inv_cancel_right])
  rw [hcard] at hbound
  omega

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
