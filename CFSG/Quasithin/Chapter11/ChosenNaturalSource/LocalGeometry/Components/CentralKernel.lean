module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Uniqueness
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import Theory.Representation.BinaryOffender.IrreducibleCentralLift

/-!
# Other components on the full plane with a small central quotient

The natural moved submodule, rather than the whole central cover, is Irr⁺.
A commuting perfect component fixes this moved submodule. If its codimension
is at most two over F₂, perfectness also kills the quotient action. The
remaining displacement action is abelian and hence trivial. No splitting or
vanishing of the original central kernel is used.

The source application keeps the literal normalizer action on V₂ and its
noncentralizing convention. The preceding natural-cover facts and second
component membership remain inputs to the source-family assembly owner.

Source: Aschbacher--Smith, 11.1.3, printed p.765, with the central-cover
correction to the invocation of A.1.41. The bound applies in particular to
the field-four case of the preceding 11.0.3(3).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.CentralizerField Representation.BinaryOffender.CentralizerField
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components

private theorem action_commutes_of_commutator_le_kernel
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) {A B : Subgroup H}
    (hcomm : ⁅B,A⁆ ≤ ρ.ker) (b : B) (a : A) (w : W) :
    ρ b (ρ a w) = ρ a (ρ b w) := by
  have hk : ρ.asGroupHom ⁅(b : H), (a : H)⁆ = 1 := by
    apply Units.ext
    exact hcomm (commutator_mem_commutator b.property a.property)
  rw [map_commutatorElement] at hk
  exact LinearMap.congr_fun
    (congrArg Units.val (commutatorElement_eq_one_iff_mul_comm.mp hk)) w

private theorem perfect_fixes_moved_of_commutator_le_kernel
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) {A B : Subgroup H} [Group.IsPerfect B]
    (hirr : IsIrrPlus ρ A (subspaceCommutator ρ ⊤ A))
    (hcomm : ⁅B,A⁆ ≤ ρ.ker) : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B := by
  let I := subspaceCommutator ρ ⊤ A
  have hstab : B ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    intro b hb
    change I ≤ I.comap (ρ b)
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,w,_,rfl⟩
    change ρ b (ρ a w-w) ∈ I
    rw [map_sub,action_commutes_of_commutator_le_kernel ρ hcomm ⟨b,hb⟩ ⟨a,ha⟩]
    exact Submodule.subset_span ⟨a,ha,ρ b w,Submodule.mem_top,rfl⟩
  let σ := (invariantSubspace ρ A I hirr.choose).toRepresentation
  let C := linearCentralizer σ
  let a := (stabilizerRepresentation ρ I).asGroupHom.comp (inclusion hstab)
  have ha (b : B) : a b ∈ C := by
    apply (mem_linearCentralizer_iff σ _).mpr
    intro l v
    apply Subtype.ext
    exact action_commutes_of_commutator_le_kernel ρ hcomm b l v
  let ψ : B →* C := a.codRestrict C ha
  let : IsCyclic C :=
    (centralizer_cyclic_odd ρ A I hirr.choose hirr.choose_spec.1 hirr.choose_spec.2).1
  let : Group.IsSolvable C :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := C)).comm a b
  have hψ (b : B) : ψ b = 1 := by
    have hm := map_solvableResidual_le ψ
    rw [solvableResidual_eq_top,solvableResidual_eq_bot,← MonoidHom.range_eq_map] at hm
    exact mem_bot.mp (hm (MonoidHom.mem_range.mpr ⟨b,rfl⟩))
  intro w hw b
  exact congrArg Subtype.val
    (congrArg (fun c : C => c.val.val (⟨w,hw⟩ : I)) (hψ b))

private theorem perfect_fixes_of_small_moved_quotient
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) {A B : Subgroup H} [Group.IsPerfect B]
    (hirr : IsIrrPlus ρ A (subspaceCommutator ρ ⊤ A))
    (hcomm : ⁅B,A⁆ ≤ ρ.ker)
    (hdim : Module.finrank (ZMod 2) (W ⧸ subspaceCommutator ρ ⊤ A) ≤ 2) :
    (⊤ : Submodule (ZMod 2) W) ≤ fixedSpace ρ B := by
  let I := subspaceCommutator ρ ⊤ A
  have hfix : I ≤ fixedSpace ρ B :=
    perfect_fixes_moved_of_commutator_le_kernel ρ hirr hcomm
  let J : Subrepresentation (ρ.comp B.subtype) :=
    ⟨I, fun b w hw => (hfix hw b).symm ▸ hw⟩
  have hdiff : subspaceCommutator ρ ⊤ B ≤ I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,w,_,rfl⟩
    apply (Submodule.Quotient.eq I).mp
    exact LinearMap.congr_fun
      (representation_eq_one_of_isPerfect_of_finrank_le_two J.quotientRepresentation
        hdim ⟨b,hb⟩) (I.mkQ w)
  exact le_fixedSpace_of_commutator_le_fixedSpace ρ B ⊤
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (hdiff.trans hfix)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : ChapterB.QuasisimpleSource.BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- The actual moved plane for the second local component. The full plane
and its central quotient are not silently identified. -/
@[expose] def secondMoved : Submodule (ZMod 2) (Additive (f.Vi 1)) :=
  subspaceCommutator (flagAction f 1) ⊤
    ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G)))

/-- Other relative components centralize the full plane when the complement
to its Irr⁺ moved module has binary dimension at most two. -/
theorem other_component_centralizes_of_small_moved_quotient (S : D.NonbinaryNaturalInput)
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hirr : IsIrrPlus (flagAction f 1)
      ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) (secondMoved f))
    (hdim : Module.finrank (ZMod 2) (Additive (f.Vi 1) ⧸ secondMoved f) ≤ 2)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) K)
    (hne : K ≠ f.Li 1) : K ≤ centralizer (f.Vi 1 : Set G) := by
  let H := normalizer (f.Vi 1 : Set G)
  let A := (f.Li 1).subgroupOf H
  let ρ := flagAction f 1
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 1)) (pCore 2 H) pCore_isPGroup
  have hcore' : A.pCoreIn 2 ≤ ρ.ker := by
    rw [pCoreIn_subgroupOf 2 _ _ hL.1, flagAction_ker]
    exact comap_mono hcore
  have hne' : K.subgroupOf H ≠ A := by
    intro he
    apply hne
    calc
      K = (K.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hK.1).symm
      _ = A.map H.subtype := congrArg (map H.subtype) he
      _ = f.Li 1 := map_subgroupOf_eq_of_le hL.1
  have hcomm := (ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hQ hK.2 hL.2 hne').1
  let := hK.2.perfect
  have hfix := perfect_fixes_of_small_moved_quotient ρ hirr
    (hcomm.trans (inf_le_right.trans hcore')) hdim
  intro k hk v hv
  have he := hfix (show Additive.ofMul (⟨v,hv⟩ : f.Vi 1) ∈
    (⊤ : Submodule (ZMod 2) (Additive (f.Vi 1))) from trivial)
      (⟨⟨k,hK.1 hk⟩,hk⟩ : K.subgroupOf H)
  have he' := congrArg (fun w : Additive (f.Vi 1) => (w.toMul : G)) he
  change k * v * k⁻¹ = v at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- The literal 11.1.3 conclusion using the moved module and its small quotient.
This repairs the whole-plane Irr⁺ premise in the field-four central-cover branch. -/
theorem uniqueNoncentral_second_of_small_moved_quotient (S : D.NonbinaryNaturalInput)
    (hL : Source.ComponentIn (normalizer (f.Vi 1 : Set G)) (f.Li 1))
    (hirr : IsIrrPlus (flagAction f 1)
      ((f.Li 1).subgroupOf (normalizer (f.Vi 1 : Set G))) (secondMoved f))
    (hdim : Module.finrank (ZMod 2) (Additive (f.Vi 1) ⧸ secondMoved f) ≤ 2)
    (hcore : (f.Li 1).pCoreIn 2 ≤ centralizer (f.Vi 1 : Set G)) :
    Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1) := by
  have hn : ¬ f.Li 1 ≤ centralizer (f.Vi 1 : Set G) := by
    intro hc
    apply hirr.not_le_fixedSpace (flagAction f 1)
    intro v _ a
    have hk : (a : normalizer (f.Vi 1 : Set G)) ∈ (flagAction f 1).ker := by
      rw [flagAction_ker]
      exact hc a.property
    exact LinearMap.congr_fun hk v
  refine ⟨⟨hL,hn⟩,?_⟩
  intro K hK
  by_contra hne
  exact hK.2 (other_component_centralizes_of_small_moved_quotient f S hL hirr hdim
    hcore hK.1 hne)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
