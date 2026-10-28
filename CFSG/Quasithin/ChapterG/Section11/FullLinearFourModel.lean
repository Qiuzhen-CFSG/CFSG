module
public import CFSG.Quasithin.ChapterG.Section11.ExchangedModels
public import Theory.Representation.NormalComponentConstituents.FullLinear
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Action
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.MarkedComparison.Transport
public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.NormalComponentConstituents.FullLinearFourLift
public import Theory.GroupTheory.DerivedAutomorphismAction

/-!
# Reconstructing the whole exceptional full-four action

The full constituent quotient first forces the normal component orbit to have
full GL₄(2) image. The original alternating form and exchanged complementary
pair kill its kernel. Homogeneity and irreducibility make the component orbit
self-centralizing; its properness and the order-two outer group then identify
the whole group with Aut(GL₄(2)), hence S₈. The marked comparison constructs
the actual natural-plus-dual intertwiner, including both summands.

The original X, X₀, point, isotropic space and form are retained through literal
images and transport formulas. This recognizes the exceptional branch in
`ExchangedModels`; it does not assert exhaustion or an ambient exclusion.
Source: Aschbacher--Smith G.10.15--16 and G.11.6--7, printed pp.363--367;
the full-four correction is recorded in `docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.FullLinearFour
open Representation.BinaryOffender.FullLinearFourLift

/-- Coordinates on the actual faithful constituent quotient. -/
theorem quotient_coordinates {D U : Type*} [Group D] [AddCommGroup U]
    [Module (ZMod 2) U] (σ : Representation (ZMod 2) D U)
    (hm : Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤ (Section06.binaryLinearAction 4)) :
    ∃ (d : (D ⧸ σ.ker) ≃* BinaryLinear.OuterCyclic.LinearGroup 4)
      (f : U ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 4),
      ∀ (g : D) (u : U), f (σ g u) = d (QuotientGroup.mk' σ.ker g) (f u) := by
  obtain ⟨e,c,stable,hc⟩ := hm
  refine ⟨Subgroup.topEquiv.symm.trans e,
    (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) U) ≃ₗ[ZMod 2] U).symm.trans c, ?_⟩
  intro g u
  exact hc ⟨QuotientGroup.mk' σ.ker g,mem_top _⟩ ⟨u,Submodule.mem_top⟩

/-- Perfectness removes the abelian supplement from the full linear image. -/
theorem full_normal_constituent
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H Y : Subgroup G) [H.Normal]
    [IsMulCommutative Y] (I : Submodule (ZMod 2) V)
    (hH : H ≤ subspaceStabilizer ρ I) (hY : Y ≤ subspaceStabilizer ρ I)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H Y I hH hY)) ⊤ ⊤
      (Section06.binaryLinearAction 4)) :
    finrank (ZMod 2) I = 4 ∧
      Function.Surjective (invariantSubspace ρ H I hH).toRepresentation.asGroupHom := by
  let P := H ⊔ Y
  let σ := Section09.constituentAction ρ H Y I hH hY
  obtain ⟨d,f,hf⟩ := quotient_coordinates σ hm
  have hd : finrank (ZMod 2) I = 4 := by simpa [BinaryLinear.OuterCyclic.Space] using f.finrank_eq
  have hs : Function.Surjective σ.asGroupHom := by
    intro a
    let t := (f.symm.trans (LinearMap.GeneralLinearGroup.toLinearEquiv a)).trans f
    obtain ⟨q,hq⟩ := d.surjective t
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective σ.ker q
    refine ⟨g,?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply f.injective
    change f (σ g u) = f (a.val u)
    rw [hf,hq]
    change f (a.val (f.symm (f u))) = f (a.val u)
    rw [f.symm_apply_apply]
  let E := (LinearMap.GeneralLinearGroup.congrLinearEquiv f).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _)
  let := BinaryNaturalDual.ModelOrbits.AutomorphismModel.linear_perfect (by decide : 3 ≤ 4)
  let : Group.IsPerfect (LinearMap.GeneralLinearGroup (ZMod 2) I) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  let N := (H.subgroupOf P).map σ.asGroupHom
  let Z := (Y.subgroupOf P).map σ.asGroupHom
  let : N.Normal := Subgroup.Normal.map inferInstance σ.asGroupHom hs
  have hNZ : N ⊔ Z = ⊤ := by
    rw [← Subgroup.map_sup, (Subgroup.codisjoint_subgroupOf_sup H Y).eq_top,
      ← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr hs]
  have hN : N = ⊤ := by
    have hh := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNZ inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hh
    exact top_unique hh
  refine ⟨hd,?_⟩
  intro a
  obtain ⟨g,hg,he⟩ := hN.ge (mem_top a)
  exact ⟨⟨g.val,hg⟩,he⟩

open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits

/-- Whole-group coordinates, with the original normal actor and both summands. -/
structure WholeActionModel
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H : Subgroup G)
    (I J : Submodule (ZMod 2) V) where
  componentEquiv : H ≃* LinearGroup 4
  groupEquiv : G ≃* MulAut (LinearGroup 4)
  naturalEquiv : I ≃ₗ[ZMod 2] Space 4
  dualEquiv : J ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Space 4)
  spaceEquiv : V ≃ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 4
  component_action : ∀ a : H, groupEquiv a = MulAut.conj (componentEquiv a)
  natural_coordinates : ∀ u : I, spaceEquiv u = (naturalEquiv u,0)
  dual_coordinates : ∀ u : J, spaceEquiv u = (0,dualEquiv u)
  equivariant : ∀ g v, spaceEquiv (ρ g v) =
    (AutomorphismModel.coordinateAction (Or.inl rfl)).representation (groupEquiv g) (spaceEquiv v)

/-- Lift the literal full constituent quotient to the full automorphism action. -/
theorem whole_action_model
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (H X : Subgroup G) [H.Normal] [IsElementaryAbelian 2 X]
    (hHne : H ≠ ⊥) (I : Submodule (ZMod 2) V)
    (hI : Homogeneous.IsIrrPlusWith ρ H X I)
    (hiI : IsIrreducible (invariantSubspace ρ H I hI.invariant).toRepresentation)
    (x : X) (hx : I.map (ρ x) ≠ I) (hcompl : IsCompl I (I.map (ρ x)))
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H (X ⊓ subspaceStabilizer ρ I)
        I hI.invariant inf_le_right)) ⊤ ⊤ (Section06.binaryLinearAction 4)) :
    Nonempty (WholeActionModel ρ H I (I.map (ρ x))) := by
  let Y := X ⊓ subspaceStabilizer ρ I
  let : IsMulCommutative Y := ⟨⟨fun a b => Subtype.ext
    (setLike_mul_comm (s := X) a.property.1 b.property.1)⟩⟩
  let R := invariantSubspace ρ H I hI.invariant
  have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property)
  obtain ⟨hd,hs⟩ := full_normal_constituent ρ H Y I hI.invariant inf_le_right hm
  have hiso := isotropic_of_full_constituent ρ B halt hp H I hI.invariant (by omega) hs
  have hfI : Function.Injective R.toRepresentation.asGroupHom := by
    apply faithful_isotropic_pair ρ hf B hnd hp H I hI.invariant hiI hiso (x : G)
    simpa only [hxinv] using hcompl.sup_eq_top
  obtain ⟨d,f,hfcoord⟩ := quotient_coordinates
    (Section09.constituentAction ρ H Y I hI.invariant inf_le_right) hm
  let E := (LinearMap.GeneralLinearGroup.congrLinearEquiv f).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _)
  let eH : H ≃* LinearGroup 4 :=
    (MulEquiv.ofBijective R.toRepresentation.asGroupHom ⟨hfI,hs⟩).trans E
  have hnat (a : H) (u : I) : f (R.toRepresentation a u) = eH a (f u) := by
    change f (R.toRepresentation a u) = f (R.toRepresentation a (f.symm (f u)))
    rw [f.symm_apply_apply]
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi H hHne
  have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top]
    exact sup_le (Homogeneous.le_orbitSpan ρ X I) (le_iSup (fun t : X => I.map (ρ t)) x)
  have hc := centralizer_eq_bot_of_full_homogeneous ρ hf hi H X I hI hfix hgen (by omega) hs
  have hproper : H ≠ ⊤ := by
    intro htop
    exact hx ((subspace_map_eq_iff ρ I x).mpr (hI.invariant (htop.symm ▸ mem_top _)))
  have ho : Nat.card (MulAut.Outer H) ≤ H.index := by
    rw [Nat.card_congr (MulAut.outerCongr eH).toEquiv]
    change (MulAut.innerSubgroup (LinearGroup 4)).index ≤ H.index
    rw [AutomorphismModel.inner_index (Or.inl rfl)]
    exact H.one_lt_index_of_ne_top hproper
  let eA : G ≃* MulAut H := MulEquiv.ofBijective MulAut.conjNormal
    (MulAut.conjNormal_bijective_of_outer_card_le_index H hc ho)
  have hinner (a : H) : eA (a : G) = MulAut.conj a := MulAut.conjNormal_val
  have hinner' (a : H) : eA.symm (MulAut.conj a) = (a : G) := by
    apply eA.injective
    rw [eA.apply_symm_apply,hinner]
  have hU (a : H) (u : Space 4) :
      ρ (eA.symm (MulAut.conj a)) (f.symm u : V) = (f.symm (eH a u) : V) := by
    rw [hinner']
    have he := hnat a (f.symm u)
    rw [f.apply_symm_apply] at he
    have he' : R.toRepresentation a (f.symm u) = f.symm (eH a u) := by
      apply f.injective
      rw [f.apply_symm_apply]
      exact he
    exact congrArg (fun z : I => (z : V)) he'
  have hout : ∃ t : G, eA t ∉ MulAut.innerSubgroup H ∧ I.map (ρ t) = I.map (ρ x) := by
    refine ⟨x,?_,rfl⟩
    apply hI.conjugation_not_inner ρ hfix x
    simpa only [hxinv] using hx
  obtain ⟨eJ,eV,hIcoord,hJcoord,heq⟩ := MarkedComparison.exists_equiv_of_automorphismEquiv
    (Or.inl rfl) (AutomorphismModel.coordinateAction (Or.inl rfl)) ρ eA eH hcompl f hU hout
  exact ⟨⟨eH,eA.trans (MulAut.congr eH),f,eJ,eV,
    fun a => by change MulAut.congr eH (eA a) = _; rw [hinner,MulAut.congr_conj],
    hIcoord,hJcoord,heq⟩⟩


namespace WholeActionModel
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {H : Subgroup G} {I J : Submodule (ZMod 2) V}
  (m : WholeActionModel ρ H I J)

@[expose] def symmetricEquiv : G ≃* Equiv.Perm (Fin 8) :=
  m.groupEquiv.trans BinaryNaturalDual.FourActors.permutationEquiv

theorem component_map : H.map m.groupEquiv.toMonoidHom = MulAut.innerSubgroup (LinearGroup 4) := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨m.componentEquiv ⟨a,ha⟩, (m.component_action ⟨a,ha⟩).symm⟩
  · rintro _ ⟨a,rfl⟩
    exact ⟨m.componentEquiv.symm a,(m.componentEquiv.symm a).property,
      (m.component_action (m.componentEquiv.symm a)).trans (by rw [m.componentEquiv.apply_symm_apply])⟩

@[expose] def actor (X : Subgroup G) : Subgroup (MulAut (LinearGroup 4)) := X.map m.groupEquiv.toMonoidHom

@[expose] def actorEquiv (X : Subgroup G) : X ≃* m.actor X := m.groupEquiv.subgroupMap X

@[expose] def distinguishedActor (X : Subgroup G) (X₀ : Subgroup X) : Subgroup (m.actor X) :=
  X₀.map (m.actorEquiv X).toMonoidHom

theorem actor_elementary (X : Subgroup G) [IsElementaryAbelian 2 X] :
    IsElementaryAbelian 2 (m.actor X) := IsElementaryAbelian.map _

@[expose] def markedPoint (v : V) : BinaryNaturalDual.CoordinateSpace 4 := m.spaceEquiv v

@[expose] def markedSpace (W : Submodule (ZMod 2) V) : Submodule (ZMod 2) (BinaryNaturalDual.CoordinateSpace 4) :=
  W.map m.spaceEquiv.toLinearMap

@[expose] def markedForm (B : LinearMap.BilinForm (ZMod 2) V) :
    LinearMap.BilinForm (ZMod 2) (BinaryNaturalDual.CoordinateSpace 4) :=
  B.compl₁₂ m.spaceEquiv.symm.toLinearMap m.spaceEquiv.symm.toLinearMap

@[simp] theorem markedForm_apply (B : LinearMap.BilinForm (ZMod 2) V) (u w : V) :
    m.markedForm B (m.spaceEquiv u) (m.spaceEquiv w) = B u w := by
  change B (m.spaceEquiv.symm (m.spaceEquiv u)) (m.spaceEquiv.symm (m.spaceEquiv w)) = _
  rw [m.spaceEquiv.symm_apply_apply,m.spaceEquiv.symm_apply_apply]

theorem markedForm_nondegenerate (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate) :
    (m.markedForm B).Nondegenerate := by
  constructor
  · intro u hu
    apply m.spaceEquiv.symm.injective
    rw [map_zero]
    apply hB.1
    intro w
    simpa only [markedForm,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
      m.spaceEquiv.symm_apply_apply] using hu (m.spaceEquiv w)
  · intro u hu
    apply m.spaceEquiv.symm.injective
    rw [map_zero]
    apply hB.2
    intro w
    simpa only [markedForm,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
      m.spaceEquiv.symm_apply_apply] using hu (m.spaceEquiv w)

theorem markedForm_alternating (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) :
    (m.markedForm B).IsAlt := fun u => hB (m.spaceEquiv.symm u)

theorem markedForm_preserves (B : LinearMap.BilinForm (ZMod 2) V)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w) :
    ∀ g u w, m.markedForm B
      ((AutomorphismModel.coordinateAction (Or.inl rfl)).representation g u)
      ((AutomorphismModel.coordinateAction (Or.inl rfl)).representation g w) = m.markedForm B u w := by
  intro g u w
  obtain ⟨a,rfl⟩ := m.groupEquiv.surjective g
  obtain ⟨u,rfl⟩ := m.spaceEquiv.surjective u
  obtain ⟨w,rfl⟩ := m.spaceEquiv.surjective w
  rw [← m.equivariant,← m.equivariant,m.markedForm_apply,m.markedForm_apply,hp]

theorem actor_restriction (X : Subgroup G) (x : X) (u : V) :
    (AutomorphismModel.coordinateAction (Or.inl rfl)).representation
      (m.actorEquiv X x) (m.spaceEquiv u) = m.spaceEquiv (ρ x u) := (m.equivariant x u).symm

theorem distinguishedActor_restriction (X : Subgroup G) (X₀ : Subgroup X) (x : X) :
    m.actorEquiv X x ∈ m.distinguishedActor X X₀ ↔ x ∈ X₀ := by
  exact (mem_map_equiv (f := m.actorEquiv X)).trans (by rw [MulEquiv.symm_apply_apply])

theorem marked_point_fixed (v : V) (X : Subgroup G) (hX : X ≤ Section10.pointCentralizer ρ v) :
    ∀ x : m.actor X, (AutomorphismModel.coordinateAction (Or.inl rfl)).representation x
      (m.markedPoint v) = m.markedPoint v := by
  intro x
  obtain ⟨a,rfl⟩ := (m.actorEquiv X).surjective x
  rw [markedPoint,m.actor_restriction,hX a.property]

theorem marked_space_isotropic (B : LinearMap.BilinForm (ZMod 2) V)
    (W : Submodule (ZMod 2) V) (hi : ∀ u ∈ W, ∀ w ∈ W, B u w = 0) :
    ∀ u ∈ m.markedSpace W, ∀ w ∈ m.markedSpace W, m.markedForm B u w = 0 := by
  rintro _ ⟨u,hu,rfl⟩ _ ⟨w,hw,rfl⟩
  exact (m.markedForm_apply B u w).trans (hi u hu w hw)

theorem marked_displacement (B : LinearMap.BilinForm (ZMod 2) V) (v : V)
    (W : Submodule (ZMod 2) V) (X : Subgroup G)
    (hd : ∀ x : X, ∀ u, B v u = 0 → ρ x u - u ∈ W) :
    ∀ x : m.actor X, ∀ u, m.markedForm B (m.markedPoint v) u = 0 →
      (AutomorphismModel.coordinateAction (Or.inl rfl)).representation x u - u ∈ m.markedSpace W := by
  intro x u hu
  obtain ⟨x,rfl⟩ := (m.actorEquiv X).surjective x
  obtain ⟨u,rfl⟩ := m.spaceEquiv.surjective u
  rw [markedPoint,m.markedForm_apply] at hu
  rw [m.actor_restriction,← map_sub]
  exact Submodule.mem_map_of_mem (hd x u hu)

end WholeActionModel

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- Apply the whole-action reconstruction to the existing exchanged branch. -/
theorem exchanged_full_four_model
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V} (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hfour : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ (componentOrbit L ⊤)
        (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (Section06.binaryLinearAction 4)) :
    ∃ x : X, Nonempty (WholeActionModel ρ (componentOrbit L ⊤) I (I.map (ρ x))) := by
  obtain ⟨x,hx,hcompl,_,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  exact ⟨x,whole_action_model ρ h.faithful hi B h.alternating h.nondegenerate h.preserves
    (componentOrbit L ⊤) X hL.componentOrbit_top_ne_bot I hI
    (hI.isIrrPlus.irreducible_of_normal_restriction ρ hi _) x hx hcompl hfour⟩

end CFSG.Quasithin.ChapterG.Section11.FullLinearFour
