module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticAbelianSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalElementaryMovers

/-!
# Original backward selection for elementary cross images

Every original neighboring mover has at least sixty-four images modulo Q_a.
If all its squares lie in Q_a, the full-kernel natural marking excludes an
outer involution and puts its image in the same symplectic component. The
checked point-radical calculation then supplies the actual residual generator.
Together with strict movement this constructs the overlapping backward
critical path, with no inner-placement or commutator callback.

The canonical mover's squares always lie in its own kernel Q_d, by its
quadratic action on the entire elementary seed. Thus a remaining failure of
strict backward selection produces an actual x with x^2 in Q_d but outside
Q_a. This retains both literal kernels; it does not exclude that case.
Strict movement, the distance exclusions and SymplecticPlaneRecognition
remain open.

Source: MS93 (5.4)--(5.7), pp.915--919, in the original field-four geometry
used by Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

theorem original_neighbor_elementary_mover_placement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (∀ x ∈ LocalPackage.J R d t, x^2 ∈ Q R a) →
      LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a ∧
      ⁅LocalPackage.J R d t,LocalPackage.J R d t⁆ ≤ Q R a := by
  intro R a d t ha hat hdt hsquare
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  exact original_large_elementary_mover_placement R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq ha (LocalPackage.J R d t)
    ((LocalPackage.J_le_radical R d t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (lt_of_lt_of_le (by decide : 16 < 64)
      (c.original_neighbor_mover_cross_index_ge_64 eK ha hat hdt)) hsquare

/-- Elementary unequal cross images supply the full-kernel one-root generator. -/
theorem original_unequal_elementary_mover_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      (∀ x ∈ LocalPackage.J R d t, x^2 ∈ Q R a) →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      Q R a ≤ LocalPackage.J R d t ∧
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ (LocalPackage.J R d t).map (MulAut.conj g).toMonoidHom ⊔ Z R z := by
  intro R geometry a z d t path hat hdt hne hsquare hza haz
  obtain ⟨hinner,hcomm⟩ := c.original_neighbor_elementary_mover_placement eK
    path.start_color hat hdt hsquare
  exact c.original_unequal_abelian_mover_generator eK geometry path hat hdt hne
    hinner hcomm hza haz

/-- The literal square-containment condition now replaces both inner placement
and abelian-image premises in the unequal-mover backward-path construction. -/
theorem original_backward_path_of_elementary_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      (∀ x ∈ LocalPackage.J R d t, x^2 ∈ Q R a) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hsquare hmove
  by_cases heq : LocalPackage.J R d t = LocalPackage.J R a t
  · exact c.original_backward_path_of_equal_strict_mover eK geometry hb path hat hdt heq hmove
  obtain ⟨hinner,hcomm⟩ := c.original_neighbor_elementary_mover_placement eK
    path.start_color hat hdt hsquare
  exact c.original_backward_path_of_unequal_abelian_strict_mover eK geometry hb path
    hat hdt heq hinner hcomm hmove

open scoped commutatorElement in
/-- Squares of the original small mover lie in its own entire action kernel.
This follows from its actual quadratic action, not from a quotient label. -/
theorem original_edge_mover_squares_mem_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      ∀ x ∈ LocalPackage.J R a t, x^2 ∈ Q R a := by
  intro R a t ha hat x hx
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  obtain ⟨geometry,hpos,_⟩ := c.exists_positive_even_geometry eK
  let := geometry.Z_elementary hpos a ha
  have hJS : LocalPackage.J R a t ≤ stabilizer R a :=
    (LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat))
  have hcomm : ⁅LocalPackage.J R a t,Z R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (hJS.trans (Z_normalized R a))
  have hquad := c.original_edge_mover_quadratic eK ha hat
  rw [←C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a ha]
  refine ⟨(stabilizer R a).pow_mem (hJS hx) 2,?_⟩
  intro z hz
  have hcz := commutator_mem_commutator hx hz
  have hfix : x * ⁅x,z⁆ * x⁻¹ = ⁅x,z⁆ := by
    rw [hquad hcz x hx,mul_inv_cancel_right]
  have hh : ⁅x^2,z⁆ = 1 := by
    rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hfix,←pow_two,
      elemPow_eq_one_of_isElementaryAbelian _ (hcomm hcz)]
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

/-- Every remaining failure of the strict backward selection has a literal
square crossing the two original kernels. The elementary-image case is
fully discharged, including the previously explicit inner placement. -/
theorem original_backward_path_or_cross_kernel_square
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2))) ∨
      (LocalPackage.J R d t ≠ LocalPackage.J R a t ∧
        ∃ x ∈ LocalPackage.J R d t, x^2 ∈ Q R d ∧ x^2 ∉ Q R a) := by
  intro R geometry hb a z d t path hat hdt hmove
  by_cases heq : LocalPackage.J R d t = LocalPackage.J R a t
  · exact Or.inl (c.original_backward_path_of_equal_strict_mover eK geometry hb path hat hdt heq hmove)
  by_cases hsquare : ∀ x ∈ LocalPackage.J R d t, x^2 ∈ Q R a
  · exact Or.inl (c.original_backward_path_of_elementary_strict_mover eK geometry hb path hat hdt hsquare hmove)
  push Not at hsquare
  obtain ⟨x,hx,hbad⟩ := hsquare
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  exact Or.inr ⟨heq,x,hx,c.original_edge_mover_squares_mem_kernel eK hd hdt x hx,hbad⟩
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
