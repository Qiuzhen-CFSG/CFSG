module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointCubicComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.Source
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.OffenderReduction

/-!
# The surviving B.5 sections on the original point action

Intersect all corrected F.6.18 rows with the checked solvable-kernel quotient
comparisons. The actual action quotient has order 168, 360, 720, 1080, 2160,
2520, 5040 or 12096. The six-point cubic covers remain intact whenever the
comparison is faithful; only a proved kernel identity permits descent to
an alternating or symmetric quotient.

The normal offender subgroup has two-group quotient. Its odd divisors and
its order therefore exclude the bounded rank-one actors, SL₃(4), SL₄(2)
and S₈. This proves the small-actor premise of the existing module extraction
on the literal B.5 moved section. All six source clauses are retained, and
the cubic-six output uses the corrected two-dimensional projective line.
The local point-motion exclusions are still required; an outside-Sylow
fixed-space hypothesis from Chapter 15 is not assumed here.

SourceAssembly/PointSourceSections applies the result after every original
rechoice. Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and
F.6.18, printed pp.99 and 309--310; K.1.3, printed p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section03.TerminalRecognition.Intersection
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch

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

private theorem alternating_card {D : Type*} [Group D] {n : ℕ}
    [Nontrivial (Fin n)] (e : D ≃* alternatingGroup (Fin n)) : Nat.card D = n.factorial / 2 := by
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]

private theorem symmetric_card {D : Type*} [Group D] {n : ℕ}
    (e : D ≃* Equiv.Perm (Fin n)) : Nat.card D = n.factorial := by
  rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]

private theorem cubic_alternating_card {D : Type*} [Group D] {n : ℕ}
    [Nontrivial (Fin n)] (h : FSource.TripleAlternating D n) : Nat.card D = (n.factorial / 2) * 3 := by
  rw [card_eq_card_quotient_mul_card_subgroup (center D),
    alternating_card h.quotient.some,Nat.card_congr h.center.some.toEquiv]
  simp [FSource.C]

private theorem cubic_symmetric_card {D : Type*} [Group D] {n : ℕ}
    (h : FSource.TripleSymmetric D n) : Nat.card D = n.factorial * 3 := by
  let := h.normal
  rw [card_eq_card_quotient_mul_card_subgroup h.kernel,
    symmetric_card h.quotientEquiv,Nat.card_congr h.kernelEquiv.toEquiv]
  simp [FSource.C]

universe u v w
variable {D : Type u} {E : Type v} [Group D] [Group E] [Finite D] [Finite E]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}

private theorem quotient_card_of_dihedral
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (c : PointQuotientComparison ρ g) (hg : Function.Surjective g)
    {S : Sylow 2 D} (r : FSource.DihedralPSL2Row S) :
    Nat.card E = 168 ∨ Nat.card E = 360 := by
  rcases c.dihedral_source_models r with he | he
  · obtain ⟨e⟩ := he
    let : IsSimpleGroup PSL(3,ZMod 2) := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup D := e.isSimpleGroup
    rw [←Nat.card_congr (MulEquiv.ofBijective g ⟨simple_source_injective g,hg⟩).toEquiv,
      Nat.card_congr e.toEquiv]
    left
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 3
    norm_num [Fin.prod_univ_succ] at h ⊢
    exact h
  · obtain ⟨e⟩ := he
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
    let : IsSimpleGroup D := e.isSimpleGroup
    rw [←Nat.card_congr (MulEquiv.ofBijective g ⟨simple_source_injective g,hg⟩).toEquiv,
      alternating_card e]
    norm_num [Nat.factorial]

/-- The possible orders of the faithful action quotient, including the full
six-point cubic covers. This is a numerical consequence, not recognition by order. -/
@[expose] def PointActionOrder (E : Type*) : Prop :=
  Nat.card E = 168 ∨ Nat.card E = 360 ∨ Nat.card E = 720 ∨
  Nat.card E = 1080 ∨ Nat.card E = 2160 ∨ Nat.card E = 2520 ∨
  Nat.card E = 5040 ∨ Nat.card E = 12096

/-- Intersect every corrected F.6 row with the actual quotient comparisons.
The two original quotients are never identified without proved injectivity. -/
theorem point_action_order
    [IsQuasisimple (generalizedFitting D)] [Group.IsSolvable g.ker]
    (c : PointQuotientComparison ρ g) (s : PointSimpleComparison ρ g)
    (d : PointDegreeThreeComparison ρ g) (t : PointCubicComparison g)
    (hg : Function.Surjective g) {A B : Subgroup D} {S : Sylow 2 D}
    (hncyc : ¬ Nonempty (S ≃* FSource.C 2))
    (rows : FSource.SourceAlternative A B S) : PointActionOrder E := by
  unfold PointActionOrder
  have hfield (r : FSource.FieldExtensionRow (D := D))
      (hs : Nonempty (S ≃* (FSource.C 2 × DihedralGroup 4))) : Nat.card E = 720 := by
    obtain ⟨_,hc,⟨e⟩⟩ := s.field_extension S r hs
    rw [←Nat.card_congr (MulEquiv.ofBijective g
      ⟨symmetric_source_injective g (by decide) e,hg⟩).toEquiv,symmetric_card e]
    decide
  rcases rows with (rows | hr) | hr
  · cases rows with
    | one hs _ _ _ => exact (hncyc hs).elim
    | two hm => exact (ComponentRows.OffenderReduction.not_row_two inferInstance hm).elim
    | three r _ _ _ => exact (ComponentRows.OffenderReduction.not_productRow inferInstance r).elim
    | four F hn hm e _ _ hs _ _ =>
      exact (c.not_prime_linear_row hs F hn hm e).elim
    | five F hn hm _ e _ hs _ _ =>
      exact (c.not_prime_projective_row hs F hn hm e).elim
    | six hm ht hq hs _ _ =>
      rcases hm with h | ⟨F,hn,hm,⟨e⟩⟩
      · rcases t.alternating_six h with ⟨e,_⟩ | ⟨_,e,_⟩
        · have hc := cubic_alternating_card h
          rw [Nat.card_congr e.toEquiv] at hc
          norm_num [Nat.factorial] at hc
          omega
        · have hc := alternating_card e
          norm_num [Nat.factorial] at hc
          omega
      · have hc := quotient_card_of_dihedral c hg
          (show FSource.DihedralPSL2Row S from ⟨F,hn,hm,e,ht,hq,hs⟩)
        omega
    | seven hm _ _ _ _ =>
      rcases hm with he | h
      · obtain ⟨e⟩ := he
        let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
        let : IsSimpleGroup D := e.isSimpleGroup
        have hc := alternating_card e
        rw [Nat.card_congr (MulEquiv.ofBijective g ⟨simple_source_injective g,hg⟩).toEquiv] at hc
        norm_num [Nat.factorial] at hc
        omega
      · obtain ⟨_,e,_⟩ := t.alternating_seven h
        have hc := alternating_card e
        norm_num [Nat.factorial] at hc
        omega
    | eight hm _ hs _ _ =>
      rcases hm with hh | hr
      · obtain ⟨h⟩ := hh
        rcases t.symmetric_six h with ⟨e,_⟩ | ⟨_,e,_⟩
        · have hc := cubic_symmetric_card h
          rw [Nat.card_congr e.toEquiv] at hc
          norm_num [Nat.factorial] at hc
          omega
        · have hc := symmetric_card e
          norm_num [Nat.factorial] at hc
          omega
      · obtain ⟨r⟩ := hr
        have hc := hfield r hs
        omega
    | nine hm _ _ _ _ =>
      rcases hm with he | hh
      · obtain ⟨e⟩ := he
        have hc := symmetric_card e
        rw [Nat.card_congr (MulEquiv.ofBijective g
          ⟨symmetric_source_injective g (by decide) e,hg⟩).toEquiv] at hc
        norm_num [Nat.factorial] at hc
        omega
      · obtain ⟨h⟩ := hh
        obtain ⟨_,e,_⟩ := t.symmetric_seven h
        have hc := symmetric_card e
        norm_num [Nat.factorial] at hc
        omega
    | ten p hp hm h ht _ _ _ _ => exact (d.not_ambient p hp hm h ht).elim
    | eleven r _ _ _ _ =>
      obtain ⟨_,hi,⟨e⟩⟩ := d.graph_extension r
      have hc := Nat.card_congr e.toEquiv
      rw [Nat.card_congr (MulEquiv.ofBijective g ⟨hi,hg⟩).toEquiv,
        Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hc
      omega
    | twelve e _ _ _ _ => exact (s.not_mathieu ⟨e⟩).elim
    | thirteen _ e _ _ _ _ => exact (s.not_mathieu_component ⟨e⟩).elim
  · obtain ⟨r⟩ := hr
    have hc := quotient_card_of_dihedral c hg r
    omega
  · obtain ⟨r⟩ := hr
    obtain ⟨_,_,⟨e⟩⟩ := s.square_field S r
    have hc := symmetric_card e
    rw [Nat.card_congr (MulEquiv.ofBijective g
      ⟨symmetric_source_injective g (by decide) e,hg⟩).toEquiv] at hc
    norm_num [Nat.factorial] at hc
    omega

private theorem odd_dvd_offender {E : Type*} [Group E] [Finite E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    {m : ℕ} (hm : Odd m) (hd : m ∣ Nat.card E) : m ∣ Nat.card (offenderSubgroup ρ) := by
  let N := offenderSubgroup ρ
  let : N.Normal := offenderSubgroup_normal ρ
  obtain ⟨k,hk⟩ := hq.exists_card_eq
  have hc : Nat.card E = Nat.card N * 2^k := by
    rw [←hk,←index_eq_card,card_mul_index]
  rw [hc] at hd
  exact ((Nat.coprime_two_right.mpr hm).pow_right k).dvd_of_dvd_mul_right hd

private theorem point_not_rank_one_actor
    (horder : PointActionOrder E)
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ))
    (h : QuasisimpleComparison.ActorPruning.RankOneActorModel (offenderSubgroup ρ)) : False := by
  have hd := (offenderSubgroup ρ).card_subgroup_dvd_card
  have h45 := odd_dvd_offender ρ hq (by decide : Odd 45)
  have h27 := odd_dvd_offender ρ hq (by decide : Odd 27)
  cases h with
  | linearTwo F hlo hhi e =>
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq] at hd h45 h27
    interval_cases hn : F.degree <;>
      rcases horder with he | he | he | he | he | he | he | he
    all_goals
      solve
      | norm_num [he,hn] at hd
      | norm_num [he,hn] at h45
      | norm_num [he,hn] at h27
  | symmetricFive e =>
    have hc : Nat.card (offenderSubgroup ρ) = 120 := by
      rw [symmetric_card e]
      decide
    rw [hc] at hd h45 h27
    rcases horder with he | he | he | he | he | he | he | he
    all_goals
      solve
      | norm_num [he] at hd
      | norm_num [he] at h45

private theorem point_not_large_actor
    (horder : PointActionOrder E)
    (h : QuasisimpleComparison.ActorPruning.LargeActorModel (offenderSubgroup ρ)) : False := by
  have hb : Nat.card (offenderSubgroup ρ) ≤ 12096 :=
    (Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype Subtype.val_injective).trans
      (by rcases horder with he | he | he | he | he | he | he | he <;> omega)
  cases h with
  | linearThreeFour F hn e =>
    have hc : Nat.card (offenderSubgroup ρ) = 60480 := by
      rw [Nat.card_congr e.toEquiv,
        card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier)),
        Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,
        Matrix.PSL3.LinearThree.card_projective_mul_scalar,F.card_eq,hn]
      decide
    omega
  | linearFourTwo e =>
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    norm_num only [Nat.card_zmod,Fin.prod_univ_succ,Fin.val_zero,Fin.val_succ,
      Finset.prod_empty,mul_one] at hc
    have hd : Nat.card (offenderSubgroup ρ) = 20160 := by
      rw [Nat.card_congr e.toEquiv,
        card_eq_card_quotient_mul_card_subgroup (center SL(4,ZMod 2)),
        Atlas.ExceptionalSupport.card_sl_center,hc]
      norm_num
    omega
  | symmetricEight e =>
    have hc := symmetric_card e
    norm_num [Nat.factorial] at hc
    omega

/-- The original point action has a small offender actor. The quotient by
that actor is used only as a two-group; it is not assumed trivial. -/
theorem point_small_actor
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (horder : PointActionOrder E)
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ)) :
    QuasisimpleComparison.SmallActorModel (offenderSubgroup ρ) := by
  rcases QuasisimpleComparison.ActorPruning.actor_split b with h | h | h
  · exact h
  · exact (point_not_rank_one_actor horder hq h).elim
  · exact (point_not_large_actor horder h).elim

/-- All remaining module alternatives live on the original B.5 moved section
or its central quotient, including the corrected cubic-six geometry. -/
theorem point_source_sections
    (b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (horder : PointActionOrder E)
    (hq : letI := offenderSubgroup_normal ρ; IsPGroup 2 (E ⧸ offenderSubgroup ρ)) :
    QuasisimpleComparison.SmallActorModel (offenderSubgroup ρ) ∧
      SectionAlternatives b.source.sectionData := by
  have h := point_small_actor b horder hq
  exact ⟨h,b.sectionAlternatives h⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
