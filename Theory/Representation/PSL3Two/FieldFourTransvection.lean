module
public import Theory.Representation.PSL3Two.RankTwoOuterRecognition
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Field-four transvections and outer automorphisms of binary SL₃

On the moved subspace, perfectness gives full movement. Rank at most two
for an involution and an implemented outer automorphism identify the binary
module with the natural-plus-dual pair. Its invertible commutant is trivial,
contradicting any commuting operator without nonzero fixed vectors.

For an F₄-linear action, a nontrivial field scalar gives exactly such an
operator, and a transvection has binary displacement two. The outer actor
need only be binary linear: no F₄-linearity is imposed on it. Trivial
summands are removed rather than assumed absent.

Source application: the residual PSL₃(2) row in Aschbacher–Smith 8.2.9,
printed p.721, refs/quasithin.pdf; the recognition uses the concrete H.6.1
catalogue and the three-involution generation bound.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]
set_option backward.isDefEq.respectTransparency false

omit [FiniteDimensional (ZMod 2) M] in
private theorem moved_map_eq
    (ρ : Representation (ZMod 2) Group M)
    (α : MulAut Group) (f : M ≃ₗ[ZMod 2] M)
    (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v)) :
    (subspaceCommutator ρ ⊤ ⊤).map f.toLinearMap = subspaceCommutator ρ ⊤ ⊤ := by
  have hh := subspaceCommutator_map_embedding ρ ρ α.symm.toMonoidHom f.toLinearMap
    (fun g v => by
      change ρ g (f v) = f (ρ (α.symm g) v)
      rw [hf,α.apply_symm_apply])
    ⊤ ⊤
  simpa only [Submodule.map_top,LinearEquiv.range,Subgroup.map_top_of_surjective α.symm.toMonoidHom α.symm.surjective] using hh.symm

/-- A nontrivial binary SL₃(2) module with involution rank at most two
cannot simultaneously admit an outer actor and a commuting invertible
operator with no nonzero fixed vector. The moved submodule removes any
trivial summands; no semisimplicity hypothesis is needed. -/
theorem no_rank_two_outer_fixedPointFree_commutant
    (ρ : Representation (ZMod 2) Group M)
    (hmove : ∃ g v, ρ g v ≠ v)
    (a : Group) (ha : a^2=1) (hane : a≠1)
    (hr : fixedCodim ρ (zpowers a) ≤ 2)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : M ≃ₗ[ZMod 2] M) (hf : ∀ g v, f (ρ g v) = ρ (α g) (f v))
    (c : M ≃ₗ[ZMod 2] M) (hc : ∀ g v, c (ρ g v) = ρ g (c v))
    (hcf : ∀ v, c v=v → v=0) : False := by
  let : _root_.Group.IsPerfect Group := Atlas.sl_perfect 3 (by decide)
  let : _root_.Group.IsPerfect (⊤ : Subgroup Group) :=
    _root_.Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv : (⊤ : Subgroup Group) ≃* Group).symm.toMonoidHom)
      Subgroup.topEquiv.symm.surjective
  let U := subspaceCommutator ρ ⊤ ⊤
  have hU := subspaceCommutator_invariant ρ (⊤ : Submodule (ZMod 2) M) (⊤ : Subgroup Group)
  let S : Subrepresentation ρ := ⟨U,fun g v hv => (hU (mem_top g) v).2 hv⟩
  have hSne : S.toSubmodule ≠ ⊥ := by
    intro hh
    obtain ⟨g,v,hv⟩ := hmove
    have hm : ρ g v-v ∈ S.toSubmodule := Submodule.subset_span ⟨g,mem_top _,v,Submodule.mem_top,rfl⟩
    rw [hh] at hm
    exact hv (sub_eq_zero.mp hm)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hSne
  have hfull : subspaceCommutator S.toRepresentation ⊤ ⊤=⊤ := by
    apply Submodule.map_injective_of_injective S.toSubmodule.subtype_injective
    have hm := subspaceCommutator_map_embedding ρ S.toRepresentation (MonoidHom.id Group)
      S.toSubmodule.subtype (fun _ _ => rfl) ⊤ ⊤
    have hp := subspaceCommutator_idempotent_of_perfect ρ (⊤ : Subgroup Group)
    rw [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] at hm
    rw [←hm,Submodule.map_top,Submodule.range_subtype]
    exact hp
  let F := f.ofSubmodules S.toSubmodule S.toSubmodule (moved_map_eq ρ α f hf)
  let C := c.ofSubmodules S.toSubmodule S.toSubmodule (moved_map_eq ρ (MulEquiv.refl _) c hc)
  have hF (g : Group) (v : S.toSubmodule) :
      F (S.toRepresentation g v) = S.toRepresentation (α g) (F v) := Subtype.ext (hf g v)
  obtain ⟨e⟩ := RankTwoOuterRecognition.equiv_natural_dual_of_involution_fixedCodim_le_two
    S.toRepresentation hfull a ha hane ((fixedCodim_subrepresentation_le ρ S _).trans hr)
    α hα F hF
  let C' := e.toLinearEquiv.symm.trans (C.trans e.toLinearEquiv)
  have hC' (g : Group) (v : NaturalDual.Space) : C' (NaturalDual.action g v) =
      NaturalDual.action g (C' v) := by
    change e (C (e.symm (NaturalDual.action g v))) = NaturalDual.action g (e (C (e.symm v)))
    have he1 : e.symm (NaturalDual.action g v) = S.toRepresentation g (e.symm v) :=
      LinearMap.congr_fun (e.symm.isIntertwining' g) v
    rw [he1]
    have hh : C (S.toRepresentation g (e.symm v)) = S.toRepresentation g (C (e.symm v)) :=
      Subtype.ext (hc g (e.symm v))
    rw [hh]
    exact LinearMap.congr_fun (e.isIntertwining' g) (C (e.symm v))
  have heq := NaturalDual.centralizer_eq_one C' hC'
  have hcz (v : S.toSubmodule) : c (v : M) = v := by
    have hh := LinearEquiv.congr_fun heq (e v)
    change e (C (e.symm (e v))) = e v at hh
    rw [e.symm_apply_apply] at hh
    exact congrArg Subtype.val (e.toLinearEquiv.injective hh)
  obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
  exact hv (Subtype.ext (hcf v (hcz v)))

/-- An actual field-four transvection cannot extend to an outer automorphism
of the same binary SL₃(2). The implementing map may be only binary linear. -/
theorem no_field_four_transvection_outer
    {F Y : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup Y] [Module F Y] [Module (ZMod 2) Y]
    [IsScalarTower (ZMod 2) F Y] [FiniteDimensional F Y]
    (hF : Nat.card F=4) (μ : Representation F Group Y)
    (a : Group) (ha : a^2=1) (hane : a≠1)
    (hr : Module.finrank F (LinearMap.range (μ a-1))=1)
    (α : MulAut Group) (hα : α ∉ MulAut.innerSubgroup Group)
    (f : Y ≃ₗ[ZMod 2] Y) (hf : ∀ g v, f (μ g v) = μ (α g) (f v)) : False := by
  let : FiniteDimensional (ZMod 2) Y := Module.Finite.trans F Y
  let ρ := Representation.restrictScalars (k := ZMod 2) μ
  have hdim : Module.finrank (ZMod 2) F=2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [hF,Nat.card_zmod] at hh
    apply Nat.pow_right_injective (by decide : 1<2)
    exact hh.symm
  let P := LinearMap.range (ρ a-1)
  let b : P ≃ₗ[ZMod 2] LinearMap.range (μ a-1) := {
    toFun x := ⟨x,x.property⟩
    invFun x := ⟨x,x.property⟩
    left_inv x := rfl
    right_inv x := rfl
    map_add' x y := rfl
    map_smul' c x := rfl }
  have hbinary : fixedCodim ρ (zpowers a) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    have hh := Module.finrank_mul_finrank (ZMod 2) F (LinearMap.range (μ a-1))
    rw [←b.finrank_eq,hdim,hr] at hh
    change Module.finrank (ZMod 2) P ≤ 2
    omega
  have hmove : ∃ g v, ρ g v ≠ v := by
    by_contra! hz
    have hh : μ a=1 := by
      apply LinearMap.ext
      intro v
      exact hz a v
    rw [hh,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨z,hz,hz1⟩ := ENat.exists_ne_ne_of_three_le
    (α := F) (by rw [ENat.card_eq_coe_fintype_card,←Nat.card_eq_fintype_card,hF]; norm_num) 0 1
  let c := (LinearEquiv.smulOfNeZero F Y z hz).restrictScalars (ZMod 2)
  apply no_rank_two_outer_fixedPointFree_commutant ρ hmove a ha hane hbinary α hα f hf c
  · intro g v
    exact (μ g).map_smul z v |>.symm
  · intro v hv
    have hh : (z-1) • v=0 := by
      rw [sub_smul,one_smul]
      exact sub_eq_zero.mpr hv
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz1)
end BinaryLinearThree
