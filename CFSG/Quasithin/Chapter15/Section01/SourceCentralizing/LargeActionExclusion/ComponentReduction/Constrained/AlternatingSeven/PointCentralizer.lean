module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.FixedModule
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.ModuleCentralizer
public import Theory.Representation.BinaryPermutation.PairedResidual.PointFixer

/-!
# The actual A₇ fixed-plane centralizer is a point-stabilizer preimage

The fixed plane centralizes U(L). Full-cover cohomology expresses each
of its elements as a module element times a centralizer of L. Centralizing
the same partition residual restricts that module element to the single
six-support line. The already proved fixed-plane noncentrality selects the
nonzero element, identifying C_L(V₁) with the point-stabilizer preimage
under the literal two-core quotient.

Source: Aschbacher--Smith 15.1.25(5), printed p.1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC BinaryPermutation BinaryPermutation.SevenMarkedAction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem a7_inner_element_fixed_by_residual
    {d : CaseIComponentData T M Mc V}
    (q : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7))
    (E : blockU d.L ≃* Multiplicative (core (Fin 7)))
    (hE : ∀ (l : d.L) (u : blockU d.L), E (blockConjugate d.L l u) =
      coreAction (q (QuotientGroup.mk' (pCore 2 d.L) l)).val (E u))
    (R : Subgroup d.L) (c : Perm7)
    (hi : R.map ((alternatingGroup (Fin 7)).subtype.comp
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))) =
        pairedFour.map (MulAut.conj c).toMonoidHom)
    (u : blockU d.L)
    (hu : ((u : d.L) : G) ∈ centralizer ((R.map d.L.subtype) : Set G)) :
    (E u).toAdd = 0 ∨ (E u).toAdd = coreRepresentation (Fin 7) c
      SevenParabolic.Ordinary.firstSix := by
  apply conjugate_pairedFour_fixed
  intro g hg
  rw [←hi] at hg
  obtain ⟨l,hl,rfl⟩ := hg
  have he : blockConjugate d.L l u = u := by
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * ((u : d.L) : G) * (l : G)⁻¹ = u
    rw [hu l (mem_map_of_mem d.L.subtype hl),mul_inv_cancel_right]
  have hh := hE l u
  rw [he] at hh
  exact (congrArg Multiplicative.toAdd hh).symm

/-- A single six-support vector controls the full-cover action of the fixed
plane. The quotient marking is the actual partition's marking. -/
theorem ExchangedSource.constrained_a7_point_factorization
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (a : d.ConstrainedA7Alternative) :
    ∃ q : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
    ∃ E : blockU d.L ≃* Multiplicative (core (Fin 7)),
    ∃ c : Perm7,
      (∀ (l : d.L) (u : blockU d.L), E (blockConjugate d.L l u) =
        coreAction (q (QuotientGroup.mk' (pCore 2 d.L) l)).val (E u)) ∧
      let z : blockU d.L := E.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix))
      ∀ v ∈ d.nineFixedPlane,
        v ∈ centralizer (d.L : Set G) ∨
          ((z : d.L) : G) * v ∈ centralizer (d.L : Set G) := by
  obtain ⟨q,p,_,hp⟩ := a.partition
  obtain ⟨E,hE⟩ := a.block.seven_module_coordinates_at q
  let f := (alternatingGroup (Fin 7)).subtype.comp
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
  let P := p.stabilizer.comap f
  let R := (pResidual 2 P).map P.subtype
  have hP := s.a7_partition_preimage_le hTM q p f rfl hp
  have hfix := a7_partition_residual_fixed d P hP
  obtain ⟨c,hc⟩ := p.three_pairs_stabilizer
  have hi : R.map f = pairedFour.map (MulAut.conj c).toMonoidHom := by
    have hh := a7_partition_residual_image d q p
    change R.map f = _ at hh
    rw [conjugate_partition_twoResidual p.stabilizer c hc] at hh
    exact hh
  refine ⟨q,E,c,hE,?_⟩
  dsimp only
  intro v hv
  have hn := s.constrained_a7_normalizes hG h a
  have hvn := hn ((d.fixedPlane_le_sylow_cubicCentralizer hTM h hv).1)
  obtain ⟨u,hu⟩ := a.block.seven_module_fixer_factorization hvn
    (s.constrained_a7_fixed_module hG hTM h a hv)
  have huR : ((u : d.L) : G) ∈ centralizer ((R.map d.L.subtype) : Set G) := by
    have hR : R.map d.L.subtype ≤ d.L := map_subtype_le _
    exact (mul_mem_cancel_right (hfix hv)).mp ((centralizer_le hR) hu)
  rcases a7_inner_element_fixed_by_residual q E hE R c hi u huR with he | he
  · have hu1 : u = 1 := E.injective (Multiplicative.toAdd.injective (he.trans (by simp)))
    left
    simpa only [hu1,coe_one,one_mul] using hu
  · right
    have huE : u = E.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix)) := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact Multiplicative.toAdd.injective he
    simpa only [huE] using hu

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup ChapterC BinaryPermutation BinaryPermutation.SevenMarkedAction
open AlternatingSeven.ThreeResidualLocals
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The fixed plane has the literal point-stabilizer preimage as its centralizer
inside L; the noncentrality proved in 15.1.25(3) selects the six-support line. -/
theorem ExchangedSource.constrained_a7_point_centralizer
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (a : d.ConstrainedA7Alternative) :
    ∃ q : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7), ∃ i : Fin 7,
      (centralizer (d.nineFixedPlane : Set G)).subgroupOf d.L =
        (MulAction.stabilizer (alternatingGroup (Fin 7)) i).comap
          (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))) := by
  obtain ⟨q,E,c,hE,hfac⟩ := s.constrained_a7_point_factorization hG hTM h a
  let z : blockU d.L := E.symm (Multiplicative.ofAdd
    (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix))
  have hnc := (s.constrained_a7_residual_and_movement hG h a.block).2.2
  obtain ⟨v,hv,hvnc⟩ : ∃ v ∈ d.nineFixedPlane, v ∉ centralizer (d.L : Set G) := by
    by_contra! hh
    exact hnc hh
  have hzv : ((z : d.L) : G) * v ∈ centralizer (d.L : Set G) :=
    (hfac v hv).resolve_left hvnc
  have hpoint (l : d.L) :
      l * (z : d.L) = (z : d.L) * l ↔
        (q (QuotientGroup.mk' (pCore 2 d.L) l)).val (c 6) = c 6 := by
    rw [←conjugate_six_fixed_iff c]
    have hzE : E z = Multiplicative.ofAdd
        (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix) := E.apply_symm_apply _
    have he : coreAction (q (QuotientGroup.mk' (pCore 2 d.L) l)).val (E z) = E z ↔
        blockConjugate d.L l z = z := by rw [←hE,E.injective.eq_iff]
    have hev : coreRepresentation (Fin 7)
        (q (QuotientGroup.mk' (pCore 2 d.L) l)).val
        (coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix) =
        coreRepresentation (Fin 7) c SevenParabolic.Ordinary.firstSix ↔
          blockConjugate d.L l z = z := by
      rw [←he,hzE]
      exact Multiplicative.toAdd.injective.eq_iff.symm
    rw [hev]
    have hz : blockConjugate d.L l z = z ↔ l * (z : d.L) * l⁻¹ = z := Subtype.ext_iff
    rw [hz]
    change l * (z : d.L) = (z : d.L) * l ↔ l * (z : d.L) * l⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.symm
  refine ⟨q,c 6,?_⟩
  ext l
  change (l : G) ∈ centralizer (d.nineFixedPlane : Set G) ↔
    (q (QuotientGroup.mk' (pCore 2 d.L) l)).val (c 6) = c 6
  rw [←hpoint]
  constructor
  · intro hl
    apply Subtype.ext
    have hvcomm := hl v hv
    have hzcomm := hzv l l.property
    change (l : G) * ((z : d.L) : G) = ((z : d.L) : G) * l
    apply mul_right_cancel (b := v)
    calc
      (l : G) * ((z : d.L) : G) * v = l * (((z : d.L) : G) * v) := mul_assoc _ _ _
      _ = (((z : d.L) : G) * v) * l := hzcomm
      _ = ((z : d.L) : G) * (v * l) := mul_assoc _ _ _
      _ = ((z : d.L) : G) * (l * v) := by rw [hvcomm]
      _ = (((z : d.L) : G) * l) * v := (mul_assoc _ _ _).symm
  · intro hl v hv
    rcases hfac v hv with hc | hc
    · exact (hc l l.property).symm
    · have hzcomm := congrArg Subtype.val hl
      change (l : G) * ((z : d.L) : G) = ((z : d.L) : G) * l at hzcomm
      have hcomm := hc l l.property
      apply mul_left_cancel (a := ((z : d.L) : G))
      calc
        ((z : d.L) : G) * (v * l) = (((z : d.L) : G)*v) * l := (mul_assoc _ _ _).symm
        _ = l * (((z : d.L) : G)*v) := hcomm.symm
        _ = ((l : G) * ((z : d.L) : G)) * v := (mul_assoc _ _ _).symm
        _ = (((z : d.L) : G) * l) * v := by rw [hzcomm]
        _ = ((z : d.L) : G) * (l*v) := mul_assoc _ _ _

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
