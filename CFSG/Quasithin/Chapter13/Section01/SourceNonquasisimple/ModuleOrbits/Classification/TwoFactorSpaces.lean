module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.HyperplaneMarking
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.FirstFactor
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedIrreducibility
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.Dimension
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Generation

/-!
# The selected component in a two-factor source representation

The B.5.6(3) decomposition lives in the global fixed quotient. Perfectness
shows that the selected component fixes the opposite original source space,
and that the opposite factor fixes its moved space. These identities lift
the quotient decomposition to a fixed supplement and identify the literal
central quotient of the moved section with the specified factor module.

Offender generation also descends to the full moved factor. For a doubled
natural SL3(2) quotient, the resulting six-dimensional bound eliminates its
fixed kernel. The single-natural row retains the B.4.8(2) Sylow fixed-space
identity, including its ambient fixed supplement.

Source: Aschbacher--Smith B.5.6(3), p.105, and 13.1.10, pp.871--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
namespace ProductMarkings
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem factor_moved_le {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : moved ρ A ≤ U.toSubmodule := by
  cases h with
  | natural he _ => exact he.ge
  | doubleNatural _ _ he _ => exact he.ge
  | exceptional he _ => exact he

/-- Disjoint quotient summands intersect only in the original global fixed space. -/
theorem twoFactors_intersection_fixed (d : SourceTwoFactorCase ρ) :
    d.firstSpace.toSubmodule ⊓ d.secondSpace.toSubmodule ≤ ρ.invariants := by
  intro v hv
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact d.decomposition.disjoint.le_bot
    ⟨⟨v,hv.1,rfl⟩,⟨v,hv.2,rfl⟩⟩

/-- A perfect subgroup of the first factor fixes the entire opposite source space,
including its extension data before passage to the global fixed quotient. -/
theorem twoFactors_opposite_fixed (d : SourceTwoFactorCase ρ)
    {C : Subgroup D} [Group.IsPerfect C] (hCA : C ≤ d.first) :
    d.secondSpace.toSubmodule ≤ fixedSpace ρ C := by
  apply le_fixedSpace_of_commutator_le_fixedSpace ρ C d.secondSpace.toSubmodule
    (le_subspaceStabilizer ρ _ (fun g _ v hv => d.secondSpace.apply_mem_toSubmodule g hv))
  apply le_trans _ (show ρ.invariants ≤ fixedSpace ρ C from fun _ hv g => hv g)
  apply le_trans _ (twoFactors_intersection_fixed d)
  apply le_inf
  · apply le_trans _ (factor_moved_le d.firstCase)
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,_,rfl⟩
    exact ⟨g,hCA hg,v,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,hv,rfl⟩
    exact d.secondSpace.toSubmodule.sub_mem (d.secondSpace.apply_mem_toSubmodule g hv) hv

private theorem product_commute {A B : Subgroup D} (d : InternalProduct A B)
    (a : A) (b : B) : (a : D) * (b : D) = (b : D) * (a : D) := by
  have hh : d.equiv ((a,1) * (1,b)) = d.equiv ((1,b) * (a,1)) := by simp
  rw [map_mul,map_mul] at hh
  simpa only [d.apply_eq,OneMemClass.coe_one,mul_one,one_mul] using hh

/-- Opposite-factor centralization holds on the literal moved component space. -/
theorem twoFactors_moved_fixed (d : SourceTwoFactorCase ρ)
    {C : Subgroup D} [Group.IsPerfect C] (hCA : C ≤ d.first) :
    moved ρ C ≤ fixedSpace ρ d.second := by
  have hw := twoFactors_opposite_fixed d hCA
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,_,rfl⟩ b
  have hv : ρ (b : D) v - v ∈ d.secondSpace.toSubmodule :=
    factor_moved_le d.secondCase (Submodule.subset_span ⟨b,b.property,v,Submodule.mem_top,rfl⟩)
  have hh := hw hv ⟨g,hg⟩
  change ρ g (ρ (b : D) v - v) = ρ (b : D) v - v at hh
  have hc : ρ (b : D) (ρ g v) = ρ g (ρ (b : D) v) := by
    rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul,
      product_commute d.product ⟨g,hCA hg⟩ b]
  change ρ (b : D) (ρ g v - v) = ρ g v - v
  rw [map_sub,hc]
  rw [map_sub] at hh
  exact sub_eq_sub_iff_add_eq_add.mpr ((sub_eq_sub_iff_add_eq_add.mp hh).trans (add_comm _ _))

/-- The quotient direct sum lifts to a supplement by the fixed space of the
selected perfect component; no splitting of V is assumed. -/
theorem twoFactors_supplement (d : SourceTwoFactorCase ρ)
    {C : Subgroup D} [Group.IsPerfect C] (hCA : C ≤ d.first) :
    d.firstSpace.toSubmodule ⊔ fixedSpace ρ C = ⊤ := by
  apply top_unique
  intro v _
  have hv : (fixed ρ).toSubmodule.mkQ v ∈
      ((fixed ρ).quotientImage d.firstSpace).toSubmodule ⊔
        ((fixed ρ).quotientImage d.secondSpace).toSubmodule :=
    by rw [d.decomposition.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u,⟨u0,hu0,rfl⟩,w,⟨w0,hw0,rfl⟩,he⟩ := Submodule.mem_sup.mp hv
  have hz : v - (u0 + w0) ∈ ρ.invariants := by
    apply (Submodule.Quotient.eq ρ.invariants).mp
    change ρ.invariants.mkQ v = ρ.invariants.mkQ (u0+w0)
    rw [map_add]
    exact he.symm
  have hw := twoFactors_opposite_fixed d hCA hw0
  have hc : w0 + (v - (u0+w0)) ∈ fixedSpace ρ C :=
    (fixedSpace ρ C).add_mem hw (fun g => hz g)
  exact Submodule.mem_sup.mpr ⟨u0,hu0,w0+(v-(u0+w0)),hc,by abel⟩

end ProductMarkings
namespace ProductMarkings
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

/-- Identical original subspaces have identical images under the global fixed quotient. -/
def imageSpaceEquiv {A C : Subgroup D} (s : MovedSection ρ C)
    (U : Subrepresentation ρ) (hCA : C = A) (hU : U.toSubmodule = moved ρ A) :
    ActionEquiv (((fixed ρ).quotientImage s.space).toRepresentation.comp C.subtype)
      (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) where
  groupEquiv := MulEquiv.subgroupCongr hCA
  linearEquiv := LinearEquiv.ofEq _ _ (congrArg (Submodule.map ρ.invariants.mkQ)
    (s.space_eq.trans (hCA ▸ hU.symm)))
  intertwines _ _ := Subtype.ext rfl

/-- The natural quotient of a selected perfect factor is exactly U/C_U(C),
using the original quotient map and opposite-factor centralization. -/
def twoFactors_sectionImage {C : Subgroup D} [Group.IsPerfect C]
    (d : SourceTwoFactorCase ρ) (s : MovedSection ρ C)
    (hCA : C = d.first) (hU : d.firstSpace.toSubmodule = moved ρ d.first) :
    ActionEquiv (s.action.comp C.subtype)
      (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) := by
  have hp : InternalProduct C d.second := hCA ▸ d.product
  have hw : s.space.toSubmodule ≤ fixedSpace ρ d.second := by
    rw [s.space_eq]
    exact twoFactors_moved_fixed d hCA.le
  exact composeAction (ChapterB.SourceInduction.FactorExtraction.sectionImageAction s hp hw)
    (imageSpaceEquiv s d.firstSpace hCA hU)

/-- The still-open factor rows retain their literal quotient actions and,
in the exceptional case, all B.4.8(3) extension fields. -/
inductive RemainingFactorCase (A : Subgroup D) (U : Subrepresentation ρ) : Prop
  | symmetricFive (moved_eq : U.toSubmodule = moved ρ A)
      (natural : IsSymmetricNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) 5)
  | exceptional (moved_le : moved ρ A ≤ U.toSubmodule)
      (extension : FourDimensionalSource (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))
end ProductMarkings

namespace ProductMarkings
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

theorem component_eq_linearThree {A C : Subgroup D}
    (hC : IsComponent D C) (hCA : C ≤ A) (F : BinaryField) (ho : Odd F.degree)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : C = A := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F.Carrier) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup A := (e.trans
    (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq ho)).isSimpleGroup
  exact component_eq_of_simple_factor hC hCA

theorem linearThree_degree [Finite D] (F : BinaryField) (ho : Odd F.degree)
    (e : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hr : primeRank 2 D = 2) : F.degree = 1 := by
  let ep := e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv F.card_eq ho)
  have hh := Matrix.PSL3Even.two_rank F.Carrier F.degree_pos F.card_eq
  rw [primeRank_equiv 2 ep] at hr
  omega

/-- The B.4.8(2) fixed-space equality applies through an actual supplement
by component-fixed vectors, retaining both lower and upper extension data. -/
theorem three_fixed_of_sylow [FiniteDimensional (ZMod 2) V]
    {C : Subgroup D} (s : MovedSection ρ C)
    (hi : IsIrrPlus ρ C s.space.toSubmodule)
    (a : ActionEquiv (s.action.comp C.subtype) (linearNatural BinaryField.two 3))
    (hz : s.central.toSubmodule ≠ ⊥)
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ C = ⊤)
    (S : Sylow 2 BinaryLinearThree.Group) (v : V)
    (hv : ∀ g : S, ρ (a.groupEquiv.symm (g : BinaryLinearThree.Group)) v = v) :
    v ∈ fixedSpace ρ C := by
  have hmem : v ∈ s.space.toSubmodule ⊔ fixedSpace ρ C := hs ▸ Submodule.mem_top
  obtain ⟨w,hw,c,hc,rfl⟩ := Submodule.mem_sup.mp hmem
  have hwS : (⟨w,hw⟩ : s.space.toSubmodule) ∈
      fixedSpace (threeCoverAction s a) (S : Subgroup BinaryLinearThree.Group) := by
    intro g
    change threeCoverAction s a (g : BinaryLinearThree.Group) ⟨w,hw⟩ = ⟨w,hw⟩
    rw [threeCoverAction_apply]
    apply Subtype.ext
    have hh := hv g
    rw [map_add,show ρ (a.groupEquiv.symm (g : BinaryLinearThree.Group)) c = c from hc _] at hh
    exact add_right_cancel hh
  rw [threeCover_sylow_fixed s a hi hz S,
    threeCover_fixed_eq_central,s.central_eq] at hwS
  intro k
  change ρ (k : D) (w+c) = w+c
  rw [map_add,show ρ (k : D) c = c from hc k]
  exact congrArg (fun x => x+c) (congrArg Subtype.val (hwS k))
end ProductMarkings

namespace ProductMarkings
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

omit [Finite D] [FiniteDimensional (ZMod 2) V] in
theorem section_moved_full {C : Subgroup D} [Group.IsPerfect C] (s : MovedSection ρ C) :
    moved (s.space.toRepresentation.comp C.subtype) ⊤ = ⊤ := by
  rw [moved_comp_map, ← MonoidHom.range_eq_map, C.range_subtype]
  apply Submodule.map_injective_of_injective s.space.toSubmodule.subtype_injective
  have hh := subspaceCommutator_map_embedding ρ s.space.toRepresentation (MonoidHom.id D)
    s.space.toSubmodule.subtype (fun _ _ => rfl) C ⊤
  simp only [Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] at hh
  rw [Submodule.map_top,Submodule.range_subtype,← hh,s.space_eq]
  exact subspaceCommutator_idempotent_of_perfect ρ C

/-- Original offender generation descends to the selected fully moved factor. -/
theorem twoFactors_moved_ff (d : SourceTwoFactorCase ρ)
    (hgen : offenderSubgroup ρ = ⊤)
    {C : Subgroup D} [Group.IsPerfect C] [Nontrivial C]
    (s : MovedSection ρ C) (hCA : C = d.first)
    (hU : d.firstSpace.toSubmodule = moved ρ d.first) :
    IsFFModule (s.space.toRepresentation.comp C.subtype) := by
  subst C
  have hs : s.space.toSubmodule = d.firstSpace.toSubmodule := s.space_eq.trans hU.symm
  have hf : Function.Injective (s.space.toRepresentation.comp d.first.subtype) := by
    intro a b hab
    apply d.firstCase.faithful
    apply LinearMap.ext
    rintro ⟨q,v,hv,rfl⟩
    apply Subtype.ext
    have hv' : v ∈ s.space.toSubmodule := hs.symm ▸ hv
    have he := congrArg Subtype.val (LinearMap.congr_fun hab (⟨v,hv'⟩ : s.space.toSubmodule))
    exact congrArg ρ.invariants.mkQ he
  have hw : s.space.toSubmodule ≤ fixedSpace ρ d.second := by
    rw [s.space_eq]
    exact twoFactors_moved_fixed d le_rfl
  exact ChapterB.SourceInduction.FactorExtraction.ff_of_generated
    (second_generated ρ d.product.swap s.space hw hf hgen)

omit [Finite D] in
/-- The full moved action has dimension at most six, by its own descended offender. -/
theorem three_moved_finrank_le_six {C : Subgroup D} [Group.IsPerfect C]
    (s : MovedSection ρ C) (e : C ≃* BinaryLinearThree.Group)
    (hFF : IsFFModule (s.space.toRepresentation.comp C.subtype)) :
    Module.finrank (ZMod 2) s.space.toSubmodule ≤ 6 := by
  let σ := s.space.toRepresentation.comp C.subtype
  let τ := σ.comp e.symm.toMonoidHom
  have hfull : moved τ ⊤ = ⊤ := by
    rw [moved_comp_map,Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]
    exact section_moved_full s
  have hFF' : IsFFModule τ := hFF.map_equivariant σ τ e.toMonoidHom e.injective
    (LinearEquiv.refl _ _) (by
      intro g v
      change σ g v = σ (e.symm (e g)) v
      rw [e.symm_apply_apply])
  exact BinaryLinearThree.ResidualFFForms.ConstituentBudget.finrank_le_six τ hfull hFF'

omit [Finite D] in
/-- A doubled natural central quotient fills that six-dimensional bound;
its literal fixed kernel must therefore vanish. -/
theorem doubled_section_central_eq_bot {C : Subgroup D} [Group.IsPerfect C]
    (s : MovedSection ρ C)
    (a : ActionEquiv (s.action.comp C.subtype) (repeated (linearNatural BinaryField.two 3) 2))
    (hFF : IsFFModule (s.space.toRepresentation.comp C.subtype)) : s.central.toSubmodule = ⊥ := by
  have hb := three_moved_finrank_le_six s a.groupEquiv hFF
  have hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 6 :=
    a.linearEquiv.finrank_eq.trans (by
      change Module.finrank (ZMod 2) (Fin 2 → Fin 3 → ZMod 2) = 6
      simpa only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] using
        (Module.finrank_pi_fintype (R := ZMod 2) (M := fun _ : Fin 2 => Fin 3 → ZMod 2)))
  have hr := Submodule.finrank_quotient_add_finrank s.central.toSubmodule
  exact Submodule.finrank_eq_zero.mp (by omega)
end ProductMarkings

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
