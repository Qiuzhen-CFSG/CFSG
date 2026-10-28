module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.VertexAction

public import Theory.Representation.NormalElementaryQuotient.FixedQuotient

/-!
# The full central omega quotient on the characteristic replacement

Construct X-alpha/C_X-alpha(L-alpha) with its literal conjugation action.
The vertex kernel centralizes all of X, and perfectness of the residual
excludes new fixed vectors in the quotient. The initial-layer identification
also gives [X-alpha,L-alpha] = U-alpha at every original-group vertex.
These are the full-layer inputs to MS93 (5.3), printed p.915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
universe u v w

/-- The full central omega layer modulo its residual-fixed subgroup, with the full
vertex quotient action and its original coordinate map. -/
structure CentralOmegaQuotient {M : Type u} [Group M] (R : Subgroup M)
    (a : Vertex R) (J : Type v) [Group J] where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [moduleInst : Module (ZMod 2) Carrier]
  [finite : Finite Carrier]
  quotient : stabilizer R a →* J
  quotient_surjective : Function.Surjective quotient
  quotient_kernel : quotient.ker.map (stabilizer R a).subtype = Q R a
  action : Representation (ZMod 2) J Carrier
  sectionData : BinaryConjugationSection (stabilizer R a)
    (X R a) (X R a ⊓ fixedCore R a)
    (action.comp quotient)
  fixed_eq_bot : fixedSpace action
    (((Ltilde R a).subgroupOf (stabilizer R a)).map quotient) = ⊥

attribute [instance] CentralOmegaQuotient.addCommGroup CentralOmegaQuotient.moduleInst
  CentralOmegaQuotient.finite

variable {H : Type u} {F : Type w} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full central omega layer has the same residual commutator as Z. -/
theorem Input.replacement_X_commutator_eq_U
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ⁅X d.radical a,Ltilde d.radical a⁆ = U d.radical a := by
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
    d.radical (h.replacement_two_group d) (h.replacement_core_le d) ha
  have hX : (omegaCenterIn (pCore 2 d.overgroup)).map i = X d.radical a := by
    change (omegaCenter (pCore 2 d.overgroup)).map i = omegaCenter (Q d.radical a)
    rw [←hiQ,omegaCenter_map _ _ hi]
  rw [←hX,←hiL,←map_commutator,h.replacement_residual d,
    ←h.replacement_initialCore_eq d]
  simpa only [LocalPackage.initialLayer,h.replacement_residual d] using hiU

omit [Finite F] [CharP F 2] in
/-- The whole central omega layer has its actual fixed quotient action, with zero residual fixed space. -/
theorem Input.exists_replacement_centralOmegaQuotient_over
    {a : Vertex d.radical} (ha : color d.radical a = false)
    {J : Type v} [Group J] (κ : stabilizer d.radical a →* J)
    (hκ : Function.Surjective κ)
    (hκQ : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a) :
    ∃ s : CentralOmegaQuotient d.radical a J, s.quotient = κ := by
  let S := stabilizer d.radical a
  have hXS : X d.radical a ≤ S := (omegaCenter_le (Q d.radical a)).trans
    (show Q d.radical a ≤ S from fun _ hx => hx.1)
  let A := (X d.radical a).subgroupOf S
  let L₀ := pResidual 2 S
  let : Finite S := finite_stabilizer _ _
  let : A.Normal := normal_subgroupOf_of_le_normalizer (X_normalized _ _)
  let : IsElementaryAbelian 2 (X d.radical a) :=
    X_elementary _ _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hXS
  let e := subgroupOfEquivOfLe hXS
  have hL : (Ltilde d.radical a).subgroupOf S = L₀ :=
    comap_map_eq_self_of_injective S.subtype_injective _
  let : Group.IsPerfect (K.subgroupOf d.overgroup) := (h.replacement_component d).perfect
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
    d.radical (h.replacement_two_group d) (h.replacement_core_le d) ha
  let : Group.IsPerfect (Ltilde d.radical a) := by
    rw [←hiL,h.replacement_residual d]
    exact Group.IsPerfect.map _
  let eL : L₀ ≃* Ltilde d.radical a :=
    L₀.equivMapOfInjective S.subtype S.subtype_injective
  let : Group.IsPerfect L₀ := Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hcomm : ⁅A,κ.ker⁆ ≤ centralizer (L₀ : Set S) := by
    have hzero : ⁅A,κ.ker⁆ = ⊥ := by
      apply (map_injective S.subtype_injective)
      rw [map_commutator,map_subgroupOf_eq_of_le
        hXS,hκQ,Subgroup.map_bot]
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (Q_le_centralizer_X _ _))
    rw [hzero]
    exact bot_le
  obtain ⟨σ,hσ⟩ := exists_fixedQuotientAction_descent A L₀ κ hκ hcomm
  let π := (fixedQuotientProjection A L₀).comp e.symm.toMonoidHom
  have hAQ := omegaCenter_le (Q d.radical a)
  have hπker : π.ker =
      (X d.radical a ⊓ fixedCore d.radical a).subgroupOf
        (X d.radical a) := by
    ext a
    change fixedQuotientProjection A L₀ (e.symm a) = 1 ↔ _
    change e.symm a ∈ (fixedQuotientProjection A L₀).ker ↔ _
    rw [fixedQuotientProjection_kernel]
    constructor
    · intro ha
      refine ⟨a.property,hAQ a.property,?_⟩
      rintro l ⟨l,hl,rfl⟩
      exact congrArg Subtype.val (ha l hl)
    · intro ha l hl
      exact Subtype.ext (ha.2.2 l.val (mem_map_of_mem S.subtype hl))
  let sec : BinaryConjugationSection S (X d.radical a)
      (X d.radical a ⊓ fixedCore d.radical a) (σ.comp κ) := {
    section_le := hXS
    kernel_le := inf_le_left
    normalized := X_normalized _ _
    coordinates := π
    onto := (fixedQuotientProjection_surjective A L₀).comp e.symm.surjective
    kernel_eq := hπker
    equivariant := by
      intro g a
      change _ = σ (κ g) (π a).toAdd
      rw [hσ]
      exact fixedQuotientProjection_equivariant A L₀ g (e.symm a) }
  have hfixed : fixedSpace σ
      (((Ltilde d.radical a).subgroupOf S).map κ) = ⊥ := by
    rw [hL]
    apply bot_unique
    intro v hv
    apply (fixedQuotientAction_fixed_eq_bot A L₀).le
    intro l
    change fixedQuotientAction A L₀ l.val v = v
    rw [←hσ]
    exact hv ⟨κ l.val,mem_map_of_mem κ l.property⟩
  let : Finite (FixedQuotient A L₀) :=
    Finite.of_surjective (fun a : A => (fixedQuotientProjection A L₀ a).toAdd) (by
      intro w
      obtain ⟨a,ha⟩ := fixedQuotientProjection_surjective A L₀ (Multiplicative.ofAdd w)
      exact ⟨a,congrArg Multiplicative.toAdd ha⟩)
  exact ⟨{
    Carrier := FixedQuotient A L₀
    quotient := κ
    quotient_surjective := hκ
    quotient_kernel := hκQ
    action := σ
    sectionData := sec
    fixed_eq_bot := hfixed },rfl⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
