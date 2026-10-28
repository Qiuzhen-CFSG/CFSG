module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointCubicSymmetric

/-!
# The remaining actual seven-point action quotients

Apply the proved point-motion and cubic-cover exclusions to every corrected
F.6.18 alternative. The surviving faithful action quotient is actually
isomorphic to A₇ or S₇. The covering seven-point alternatives use their
proved exact cubic kernels; the ordinary seven-point groups retain faithful
solvable-kernel comparison maps. This is recognition from the source rows,
not from group orders.

The universal SourceAssembly/PointCubicSymmetric consumer supplies all the
exclusions after each original rechoice. Seven-point motion itself remains
the next source obligation.
Source: Aschbacher--Smith 13.2.12, printed p.882; F.6.18(3)--(13).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

private theorem simple_source_injective {D E : Type*} [Group D] [Group E] [Finite D]
    [IsSimpleGroup D] [IsQuasisimple (generalizedFitting D)]
    (g : D →* E) [Group.IsSolvable g.ker] : Function.Injective g := by
  let : IsSimpleGroup (generalizedFitting D ⧸ center (generalizedFitting D)) :=
    IsQuasisimple.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  have ht : generalizedFitting D = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (generalizedFitting D) inferInstance).resolve_left
      ((nontrivial_iff_ne_bot _).mp inferInstance)
  let : IsSimpleGroup (generalizedFitting D) :=
    ((MulEquiv.subgroupCongr ht).trans topEquiv).isSimpleGroup
  exact injective_of_simple_fitting_of_solvable_kernel g

private theorem symmetric_source_injective {D E : Type*} [Group D] [Group E]
    (g : D →* E) [Group.IsSolvable g.ker] {n : ℕ} (hn : 5 ≤ n)
    (e : D ≃* Equiv.Perm (Fin n)) : Function.Injective g := by
  let N := g.ker.map e.toMonoidHom
  let : N.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (f := (e.subgroupMap g.ker).toMonoidHom) (e.subgroupMap g.ker).surjective
  have hN : N = ⊥ := by
    by_contra hne
    let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hne
    have hle : alternatingGroup (Fin n) ≤ N :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance
    let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    let : Group.IsPerfect (alternatingGroup (Fin n)) :=
      ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin n))
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hle))
  apply (MonoidHom.ker_eq_bot_iff g).mp
  exact (map_eq_bot_iff_of_injective g.ker e.injective).mp hN


universe u v w
variable {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}

/-- The surviving point action is an actual A₇ or S₇ carrier. All source
rows, including both orientations and corrected unnumbered alternatives,
are accounted for using the literal comparison map. -/
theorem point_action_seven_of_source_exclusions
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (c : PointQuotientComparison ρ g) (s : PointSimpleComparison ρ g)
    (d : PointDegreeThreeComparison ρ g) (t : PointCubicComparison g)
    (hg : Function.Surjective g) {A B : Subgroup D} {S : Sylow 2 D}
    (hncyc : ¬ Nonempty (S ≃* FSource.C 2))
    (rows : FSource.SourceAlternative A B S)
    (hsmall : ¬ (Nonempty (E ≃* SL(3,ZMod 2)) ∨
      Nonempty (E ≃* alternatingGroup (Fin 6)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 6))))
    (hg2 : ¬ Nonempty (E ≃* Atlas.G2.Model (ZMod 2)))
    (hA : ¬ FSource.TripleAlternating D 6)
    (hS : ¬ Nonempty (FSource.TripleSymmetric D 6)) :
    Nonempty (E ≃* alternatingGroup (Fin 7)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 7)) := by
  have symmetric {n : ℕ} (hn : 5 ≤ n) (e : D ≃* Equiv.Perm (Fin n)) :
      E ≃* Equiv.Perm (Fin n) :=
    (MulEquiv.ofBijective g ⟨symmetric_source_injective g hn e,hg⟩).symm.trans e
  have hfield (r : FSource.FieldExtensionRow (D := D))
      (hs : Nonempty (S ≃* (FSource.C 2 × DihedralGroup 4))) : False := by
    obtain ⟨_,_,⟨e⟩⟩ := s.field_extension S r hs
    exact hsmall (Or.inr (Or.inr ⟨symmetric (by decide) e⟩))
  have hdihedral (r : FSource.DihedralPSL2Row S) : False := by
    rcases c.dihedral_source_models r with he | he
    · obtain ⟨e⟩ := he
      let : IsSimpleGroup PSL(3,ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
      let : IsSimpleGroup D := e.isSimpleGroup
      let a := (MulEquiv.ofBijective g ⟨simple_source_injective g,hg⟩).symm.trans e
      exact hsmall (Or.inl ⟨a.trans Matrix.PSL3Two.equiv.symm⟩)
    · obtain ⟨e⟩ := he
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
      let : IsSimpleGroup D := e.isSimpleGroup
      exact hsmall (Or.inr (Or.inl
        ⟨(MulEquiv.ofBijective g ⟨simple_source_injective g,hg⟩).symm.trans e⟩))
  rcases rows with (rows | hr) | hr
  · cases rows with
    | one hs _ _ _ => exact (hncyc hs).elim
    | two hm => exact (ComponentRows.OffenderReduction.not_row_two inferInstance hm).elim
    | three r _ _ _ => exact (ComponentRows.OffenderReduction.not_productRow inferInstance r).elim
    | four F hn hm e _ _ hs _ _ => exact (c.not_prime_linear_row hs F hn hm e).elim
    | five F hn hm _ e _ hs _ _ => exact (c.not_prime_projective_row hs F hn hm e).elim
    | six hm ht hq hs _ _ =>
      rcases hm with h | ⟨F,hn,hm,⟨e⟩⟩
      · exact (hA h).elim
      · exact (hdihedral ⟨F,hn,hm,e,ht,hq,hs⟩).elim
    | seven hm _ _ _ _ =>
      rcases hm with he | h
      · obtain ⟨e⟩ := he
        let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
        let : IsSimpleGroup D := e.isSimpleGroup
        exact Or.inl ⟨(MulEquiv.ofBijective g ⟨simple_source_injective g,hg⟩).symm.trans e⟩
      · exact Or.inl ⟨(t.alternating_seven h).2.choose⟩
    | eight hm _ hs _ _ =>
      rcases hm with hh | hr
      · exact (hS hh).elim
      · exact (hfield hr.some hs).elim
    | nine hm _ _ _ _ =>
      rcases hm with he | hh
      · exact Or.inr ⟨symmetric (by decide) he.some⟩
      · exact Or.inr ⟨(t.symmetric_seven hh.some).2.choose⟩
    | ten p hp hm h ht _ _ _ _ => exact (d.not_ambient p hp hm h ht).elim
    | eleven r _ _ _ _ =>
      obtain ⟨_,hi,⟨e⟩⟩ := d.graph_extension r
      exact (hg2 ⟨(MulEquiv.ofBijective g ⟨hi,hg⟩).symm.trans e⟩).elim
    | twelve e _ _ _ _ => exact (s.not_mathieu ⟨e⟩).elim
    | thirteen _ e _ _ _ _ => exact (s.not_mathieu_component ⟨e⟩).elim
  · exact (hdihedral hr.some).elim
  · obtain ⟨_,_,⟨e⟩⟩ := s.square_field S hr.some
    exact (hsmall (Or.inr (Or.inr ⟨symmetric (by decide) e⟩))).elim
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
