module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeOffender
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# The binary SL3 moved space is doubled natural

The earlier intrinsic SL3(2) calculation classifies a faithful fully moved
FF action by its actual quotient map to one or two natural copies. A one-copy
quotient with precisely the fixed kernel is an Irr⁺ module, including the
nonsplit four-dimensional cover. In the reducible source branch this is
impossible. The two-copy case exhausts the proved six-dimensional bound,
so its central kernel vanishes and gives actual doubled-natural coordinates.

The original source consumer uses the proved component offender to obtain
FF on the literal component action, transports through the actual SL3 mark,
and applies this argument to [V,L]. No G=L or splitting premise is assumed.
The intrinsic earlier classification is standard-axiom audited separately;
its proofs use checked matrices and cohomology, not universal B.5.1.

Source: Aschbacher--Smith B.4.8--9 and B.5.1, printed pp.91--103.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped ENNReal MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v w

/-- A fully moved module with an irreducible quotient by exactly its fixed
vectors is an Irr⁺ member, on its actual space. -/
theorem irrPlus_top_of_central_quotient
    {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    [IsIrreducible σ] (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hk : f.ker = fixedSpace ρ ⊤) (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤) : IsIrrPlus ρ ⊤ ⊤ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  apply isIrrPlus_of_minimal ρ (le_subspaceStabilizer ρ ⊤ (by simp)) hm
  · intro hfix
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    obtain ⟨v,rfl⟩ := hf w
    exact hw ((show v ∈ f.ker from hk.symm ▸ hfix Submodule.mem_top))
  · intro J hJ _
    let I : Subrepresentation σ := {
      toSubmodule := J.map f
      apply_mem_toSubmodule g := by
        rintro _ ⟨v,hv,rfl⟩
        exact ⟨ρ g v,(hJ (Subgroup.mem_top g) v).2 hv,he g v⟩ }
    rcases eq_bot_or_eq_top I with hz | ht
    · right
      intro v hv
      rw [← hk]
      have hv' : f v ∈ I := ⟨v,hv,rfl⟩
      rw [hz] at hv'
      exact hv'
    · left
      have hs : (⊤ : Submodule (ZMod 2) V) ≤ J ⊔ fixedSpace ρ ⊤ := by
        intro v _
        have hv : f v ∈ I := ht ▸ Submodule.mem_top
        obtain ⟨j,hj,heq⟩ := hv
        apply Submodule.mem_sup.mpr
        refine ⟨j,hj,v-j,?_,by abel⟩
        rw [← hk]
        change f (v-j) = 0
        rw [map_sub,heq,sub_self]
      have hc := subspaceCommutator_le_of_le_sup_fixedSpace ρ hJ hs
      rw [hm] at hc
      exact top_unique hc

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition

/-- One natural quotient with exactly the fixed kernel is the genuine Irr⁺
alternative, including its nonsplit central extension. -/
theorem binaryThree_one_quotient_irrPlus
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V)
    (q : ModuleQuotient ρ 1) (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤) : IsIrrPlus ρ ⊤ ⊤ := by
  let f : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) := (LinearMap.proj (0 : Fin 1)).comp q.projection
  let σ := (specialLinearNatural (k := ZMod 2) 3).comp q.marking.toMonoidHom
  let a : ActionEquiv σ (linearNatural BinaryField.two 3) :=
    ⟨q.marking,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  let : IsIrreducible σ := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide))
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v,hv⟩ := q.surjective (fun _ => w)
    exact ⟨v,congrFun hv 0⟩
  have hk : f.ker = fixedSpace ρ ⊤ := by
    rw [← q.kernel]
    ext v
    change q.projection v 0 = 0 ↔ q.projection v = 0
    constructor
    · intro hv
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      change q.projection v i = 0
      rw [hi]
      exact hv
    · intro hv
      exact congrFun hv 0
  exact irrPlus_top_of_central_quotient ρ σ f hf hk (fun g v => q.equivariant g v 0) hm

/-- In the fully moved binary SL3 action, failure of Irr⁺ forces the actual
space to be a direct sum of two equally marked natural modules. Both one-copy
central attachments are excluded by their irreducible fixed-space quotient. -/
theorem binaryThree_fullyMoved_double
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V) (hf : Function.Injective ρ)
    (hm : subspaceCommutator ρ ⊤ ⊤ = ⊤) (hff : IsFFModule ρ)
    (hnot : ¬ IsIrrPlus ρ ⊤ ⊤) : IsRepeatedLinearNatural ρ BinaryField.two 3 2 := by
  obtain ⟨m,hm',⟨q⟩⟩ := ExtensionControl.exists_moduleQuotient ρ hf hm hff
  rcases hm' with rfl | rfl
  · exact (hnot (binaryThree_one_quotient_irrPlus ρ q hm)).elim
  · have hd := ExtensionControl.finrank_le_six ρ hm hff
    have hdim := q.projection.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr q.surjective,finrank_top] at hdim
    have htarget : Module.finrank (ZMod 2) (Fin 2 → Fin 3 → ZMod 2) = 6 := by simp [Module.finrank_pi_fintype]
    have hz : Module.finrank (ZMod 2) q.projection.ker = 0 := by omega
    have hi : Function.Injective q.projection := LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    refine ⟨⟨q.marking,LinearEquiv.ofBijective q.projection ⟨hi,q.surjective⟩,?_⟩⟩
    intro g v
    funext i
    exact q.equivariant g v i

/-- The reducible original B.5.1 action with binary SL3 component has
literal doubled-natural coordinates on [V,L], with a single component marking. -/
theorem binaryThree_source_moved_double
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) (s : MovedSection ρ L)
    (mark : L ≃* SL) :
    IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two 3 2 := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let μ := s.space.toRepresentation
  let δ := μ.comp L.subtype
  let σ := δ.comp mark.symm.toMonoidHom
  have hfL : Function.Injective δ := by
    intro x y hxy
    apply IrreducibleBranch.component_faithful h s
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun hxy v)
  have hfσ : Function.Injective σ := hfL.comp mark.symm.injective
  obtain ⟨A,hA,hAL⟩ := linearThree_component_offender ρ hK hsemisimple h36 earlier h hnot
    BinaryField.two mark
  have hffδ : IsFFModule δ := ⟨A.subgroupOf L,
    (((bestOffender_on_subrepresentation ρ s.space hA.1).isOffender μ).subgroupOf μ hAL)⟩
  have hffσ : IsFFModule σ := hffδ.map_equivariant δ σ mark.toMonoidHom mark.injective
    (LinearEquiv.refl _ _) (by intro g v; change δ g v = δ (mark.symm (mark g)) v; rw [mark.symm_apply_apply])
  have hmμ : subspaceCommutator μ ⊤ L = ⊤ := moved_commutator_top ρ s
  have hmσ : subspaceCommutator σ ⊤ ⊤ = ⊤ := by
    have hle : subspaceCommutator μ ⊤ L ≤ subspaceCommutator σ ⊤ ⊤ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      refine Submodule.subset_span ⟨mark ⟨g,hg⟩,Subgroup.mem_top _,v,Submodule.mem_top,?_⟩
      change μ g v - v = δ (mark.symm (mark ⟨g,hg⟩)) v - v
      rw [mark.symm_apply_apply]
      rfl
    rw [hmμ] at hle
    exact top_unique hle
  have hnσ : ¬ IsIrrPlus σ ⊤ ⊤ := by
    intro hi
    let e : (⊤ : Subgroup SL) ≃* L := (topEquiv : (⊤ : Subgroup SL) ≃* SL).trans mark.symm
    have hμ : IsIrrPlus μ L ⊤ := hi.of_intertwining σ μ e.toMonoidHom e.surjective
      (LinearMap.id) Function.injective_id (fun _ _ => rfl) (by simp)
    apply moved_not_irrPlus ρ h s hnot
    change IsIrrPlus μ L (subspaceCommutator μ ⊤ L)
    rwa [hmμ]
  obtain ⟨a⟩ := binaryThree_fullyMoved_double σ hfσ hmσ hffσ hnσ
  refine ⟨⟨mark.trans a.groupEquiv,a.linearEquiv,?_⟩⟩
  intro g v
  have he := a.intertwines (mark g) v
  change a.linearEquiv (δ (mark.symm (mark g)) v) = _ at he
  simpa only [δ,μ,MulEquiv.trans_apply,mark.symm_apply_apply] using he

/-- Degree-one field transport in the original source retains actual
component coordinates and the doubled-natural conclusion. -/
theorem linearThree_degreeOne_source_moved_double
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) (s : MovedSection ρ L)
    (F : BinaryField) (hF : F.degree = 1) (mark : L ≃* SL(3,F.Carrier)) :
    IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two 3 2 := by
  exact binaryThree_source_moved_double ρ hK hsemisimple h36 earlier h hnot s
    (mark.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
