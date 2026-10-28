module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.AlternatingFixed
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.BinaryPermutationSixCover.Facts
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.SmallDualOffender
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.DualFixedSupplement
public import Theory.ElementaryAbelian.Injective

/-!
# The alternating moved-space estimate for B.5.13

The literal moved space covers the natural A₆ or A₈ module. Irr⁺ supplies
commutator generation, and the dual first-cohomology calculation bounds its
central kernel by one dimension. An elementary actor of rank at least two
therefore fixes at most four dimensions of the moved space. Quadratic action
puts its displacement inside that fixed space.

Source: Aschbacher–Smith, B.5.13, printed pp.111–112, with B.3.2 and I.1.5–6.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private noncomputable def movedProjection (s : MovedSection ρ L) :
    Representation.IntertwiningMap (s.space.toRepresentation.comp L.subtype) (s.action.comp L.subtype) :=
  s.central.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem movedProjection_isCover (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) : IsCover (movedProjection s) := by
  refine ⟨Submodule.mkQ_surjective _, ?_, ?_⟩
  · intro v hv g
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    rw [s.central_eq] at hmem
    exact hmem g
  · let τ := s.space.toRepresentation.comp L.subtype
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨τ ⟨g, hg⟩ ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem dualH1_dimension {n : ℕ} (hn : n = 6 ∨ n = 8)
    (s : MovedSection ρ L) (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural n)) :
    Module.finrank (ZMod 2) (H1 (Representation.dual (s.action.comp L.subtype))) = 1 := by
  let E := e.linearEquiv.symm.dualMap
  have he : ∀ g f, E (Representation.dual (s.action.comp L.subtype) g f) =
      Representation.dual (alternatingNatural n) (e.groupEquiv g) (E f) := by
    intro g f
    ext w
    change f (s.central.quotientRepresentation ((g : G)⁻¹) (e.linearEquiv.symm w)) =
      f (e.linearEquiv.symm (alternatingNatural n ((e.groupEquiv g)⁻¹) w))
    congr 1
    apply e.linearEquiv.injective
    change e.linearEquiv ((s.action.comp L.subtype) g⁻¹ (e.linearEquiv.symm w)) = _
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply,
      e.groupEquiv.map_inv]
  rw [(H1Congr _ _ e.groupEquiv E he).finrank_eq]
  rcases hn with rfl | rfl
  · exact BinaryPermutation.alternatingSix_natural_dual_finrank_H1
  · exact BinaryPermutation.alternatingEight_natural_dual_finrank_H1

/-- The original moved quotient has a central kernel of dimension at most one. -/
theorem alternating_moved_central_finrank_le_one {n : ℕ} (hn : n = 6 ∨ n = 8)
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hnat : IsAlternatingNatural (s.action.comp L.subtype) n) :
    Module.finrank (ZMod 2) s.central.toSubmodule ≤ 1 := by
  obtain ⟨e⟩ := hnat
  have h := finrank_ker_le_H1_of_cover (movedProjection s) (movedProjection_isCover s hi)
  rw [dualH1_dimension hn s e] at h
  change Module.finrank (ZMod 2) s.central.toSubmodule.mkQ.ker ≤ 1 at h
  rw [Submodule.ker_mkQ] at h
  exact h

private theorem alternating_natural_fixed_bound {n : ℕ} (hn : n = 6 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) (hA : IsElementaryTwo A)
    (heven : A ≤ alternatingGroup (Fin n)) (hr : 2 ≤ rank A) :
    Module.finrank (ZMod 2) (fixedSpace (BinaryPermutation.naturalRepresentation (Fin n)) A) ≤ 3 := by
  rcases hn with rfl | rfl
  · have hf := BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    have hp := fixedCodim_pos_of_faithful _ hf hA.1
    have hd := fixedCodim_add_finrank (BinaryPermutation.naturalRepresentation (Fin 6)) A
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hd
    norm_num only [Fintype.card_fin] at hd
    omega
  · exact alternatingEight_natural_fixed_finrank_le_three A hA heven hr

/-- Every contained elementary actor of rank at least two fixes at most four
dimensions of the original moved module. -/
theorem alternating_moved_fixed_finrank_le_four {n : ℕ} (hn : n = 6 ∨ n = 8)
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hnat : IsAlternatingNatural (s.action.comp L.subtype) n)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L) (hr : 2 ≤ rank A) :
    Module.finrank (ZMod 2) (fixedSpace s.space.toRepresentation A) ≤ 4 := by
  obtain ⟨e⟩ := hnat
  let f := (alternatingGroup (Fin n)).subtype.comp e.groupEquiv.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.groupEquiv.injective
  let B := (A.subgroupOf L).map f
  have hAr : rank (A.subgroupOf L) = rank A := rank_subgroupOf hAL
  have hBr : rank B = rank A := (rank_map_injective f hf _).trans hAr
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    let : IsElementaryAbelian 2 (A.subgroupOf L) :=
      IsElementaryAbelian.subgroupOf hAL
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    have hz : rank B = 0 := hb ▸ rank_bot
    omega
  have hBeven : B ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨g, _, rfl⟩
    exact (e.groupEquiv g).property
  have hfix := alternating_natural_fixed_bound hn B hB hBeven (hBr ▸ hr)
  have he : fixedCodim s.action A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin n)) B := by
    rw [← fixedCodim_subgroupOf s.action hAL]
    exact fixedCodim_map_equivariant _ _ f e.linearEquiv (fun g v => e.intertwines g v) _
  have hd := e.linearEquiv.finrank_eq
  have hq := fixedCodim_add_finrank s.action A
  have hb := fixedCodim_add_finrank (BinaryPermutation.naturalRepresentation (Fin n)) B
  have hu := fixedCodim_add_finrank s.space.toRepresentation A
  have hdim := s.central.toSubmodule.finrank_quotient_add_finrank
  have hk := alternating_moved_central_finrank_le_one hn s hi ⟨e⟩
  have hcod := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  change fixedCodim s.action A + _ ≤ _ at hcod
  omega

private theorem intersection_rank_ge_two [L.Normal]
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : 3 ≤ rank A) (hindex : L.index ≤ 2) :
    2 ≤ rank (A ⊓ L) := by
  let : IsElementaryAbelian 2 A := hA.2
  let C := L.subgroupOf A
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective C.subtype C.subtype_injective
  obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 C).exists_card_eq
  have heq : rank C = rank (A ⊓ L) := by
    rw [← rank_subgroupOf (show A ⊓ L ≤ A from inf_le_left), inf_subgroupOf_left]
  have hcard := C.card_mul_index
  have hi : C.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero L.index_ne_zero_of_finite)
      (L.relIndex_dvd_index_of_normal A)).trans hindex
  have hlow : 8 ≤ Nat.card A := by
    rw [hA.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hr
  rw [hd] at hcard
  have hdim : rank C = d := by rw [rank, hd, Nat.log_pow (by decide)]
  by_contra! h
  have hdle : d ≤ 1 := by omega
  interval_cases d <;> norm_num at hcard <;> omega

/-- An alternating natural moved section with index at most two gives the
quadratic bound for the literal original dual. -/
theorem quadraticRatio_le_two_of_alternating_moved [L.Normal]
    {n : ℕ} (hn : n = 6 ∨ n = 8)
    (s : MovedSection ρ.dual L) (hi : IsIrrPlus ρ.dual L s.space.toSubmodule)
    (hnat : IsAlternatingNatural (s.action.comp L.subtype) n)
    (hindex : L.index ≤ 2) (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  obtain ⟨A, hA⟩ := hff
  obtain ⟨A, _, hm, hquad, _⟩ := hA.exists_quadratic_minimalBestOffender ρ.dual
  have ho := hm.1.isOffender ρ.dual
  by_cases hr : rank A ≤ 2
  · exact quadraticRatio_le_two_of_small_dual_offender ρ ho hr
  have hrB := intersection_rank_ge_two ho.1 (by omega) hindex
  have hB : IsElementaryTwo (A ⊓ L) := ho.1.of_le inf_le_left (by
    intro hz
    rw [hz, Representation.BinaryOffender.rank_bot] at hrB
    omega)
  have hqB : IsQuadratic ρ.dual (A ⊓ L) :=
    fun a ha b hb v => hquad a ha.1 b hb.1 v
  have hf := alternating_moved_fixed_finrank_le_four hn s hi hnat hB inf_le_right hrB
  have hle : subspaceCommutator ρ.dual ⊤ (A ⊓ L) ≤
      s.space.toSubmodule ⊓ fixedSpace ρ.dual (A ⊓ L) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    refine ⟨?_, fun b => hqB b b.property a ha v⟩
    rw [s.space_eq]
    exact Submodule.subset_span ⟨a, ha.2, v, Submodule.mem_top, rfl⟩
  have hdim := Submodule.finrank_mono hle
  rw [← (subrepresentationFixedEquiv ρ.dual s.space (A ⊓ L)).finrank_eq] at hdim
  have hcod : fixedCodim ρ (A ⊓ L) =
      Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ (A ⊓ L)) := by
    rw [subspaceCommutator_top_eq_coinvariants]
    exact finrank_quotient_invariants_eq_dual_commutator (ρ.comp (A ⊓ L).subtype)
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨A ⊓ L, hB, (isQuadratic_dual_iff ρ _).mp hqB, ?_⟩
  omega

end CFSG.Quasithin.ChapterB.SourceB513
