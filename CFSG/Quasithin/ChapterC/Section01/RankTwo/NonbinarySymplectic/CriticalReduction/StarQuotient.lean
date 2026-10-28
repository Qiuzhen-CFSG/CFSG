module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarLayer

public import Theory.Representation.NormalElementaryQuotient.FixedQuotient

/-!
# The actual source star modulo its full fixed core

Core displacement makes the vertex two-core trivial on the elementary star
modulo its full residual-fixed subgroup. The resulting action descends through
the specified vertex quotient with the original conjugation projection and
exact kernel. Perfectness of the residual makes its section fixed-point-free.
Normality is used only inside the finite vertex stabilizer.

Source: MS93 (3.4), printed p.869. This constructs the quotient used by the dual
cover argument on the characteristic replacement of Section 7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
universe u v w

/-- The actual star modulo its full residual-fixed subgroup, with the full
vertex quotient action and its original coordinate map. -/
structure SourceStarQuotient {M : Type u} [Group M] (R : Subgroup M)
    (Y : Subgroup R) (J : Type v) [Group J] where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [moduleInst : Module (ZMod 2) Carrier]
  [finite : Finite Carrier]
  quotient : stabilizer R (alpha R) →* J
  quotient_surjective : Function.Surjective quotient
  quotient_kernel : quotient.ker.map (stabilizer R (alpha R)).subtype = Q R (alpha R)
  action : Representation (ZMod 2) J Carrier
  sectionData : BinaryConjugationSection (stabilizer R (alpha R))
    (sourceStarAlpha R Y) (sourceStarAlpha R Y ⊓ fixedCore R (alpha R))
    (action.comp quotient)
  fixed_eq_bot : fixedSpace action
    (((Ltilde R (alpha R)).subgroupOf (stabilizer R (alpha R))).map quotient) = ⊥

attribute [instance] SourceStarQuotient.addCommGroup SourceStarQuotient.moduleInst
  SourceStarQuotient.finite

variable {H : Type u} {F : Type w} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Core displacement constructs the genuine full-vertex quotient action on
the star modulo the fixed core. Its component fixed space is zero. -/
theorem Input.exists_replacement_sourceStarQuotient_over
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {J : Type v} [Group J] (κ : stabilizer d.radical (alpha d.radical) →* J)
    (hκ : Function.Surjective κ)
    (hκQ : κ.ker.map (stabilizer d.radical (alpha d.radical)).subtype =
      Q d.radical (alpha d.radical)) :
    ∃ s : SourceStarQuotient d.radical Y J, s.quotient = κ := by
  let S := stabilizer d.radical (alpha d.radical)
  let A := (sourceStarAlpha d.radical Y).subgroupOf S
  let L₀ := pResidual 2 S
  let : Finite S := finite_stabilizer _ _
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sourceStarAlpha_normalized _ _)
  let : IsElementaryAbelian 2 (sourceStarAlpha d.radical Y) :=
    h.replacement_sourceStarAlpha_elementary d geometry hb Y P hY hn
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (sourceStarAlpha_le_stabilizer _ _)
  let e := subgroupOfEquivOfLe (sourceStarAlpha_le_stabilizer d.radical Y)
  have hL : (Ltilde d.radical (alpha d.radical)).subgroupOf S = L₀ :=
    comap_map_eq_self_of_injective S.subtype_injective _
  let : Group.IsPerfect (K.subgroupOf d.overgroup) := (h.replacement_component d).perfect
  let : Group.IsPerfect (Ltilde d.radical (alpha d.radical)) := by
    rw [Ltilde_alpha,h.replacement_residual d]
    exact Group.IsPerfect.map _
  let eL : L₀ ≃* Ltilde d.radical (alpha d.radical) :=
    L₀.equivMapOfInjective S.subtype S.subtype_injective
  let : Group.IsPerfect L₀ := Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry (by omega)
  have hbound := h.replacement_sourceStarAlpha_core_displacement d geometry (by omega)
    path hfirst Y P hY hn
  have hcomm : ⁅A,κ.ker⁆ ≤ centralizer (L₀ : Set S) := by
    intro x hx l hl
    have hh := mem_map_of_mem S.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le (sourceStarAlpha_le_stabilizer _ _),hκQ] at hh
    exact Subtype.ext ((hbound hh).2 l.val (mem_map_of_mem S.subtype hl))
  obtain ⟨σ,hσ⟩ := exists_fixedQuotientAction_descent A L₀ κ hκ hcomm
  let π := (fixedQuotientProjection A L₀).comp e.symm.toMonoidHom
  have hAQ := h.replacement_sourceStarAlpha_le_own_core d geometry (by omega) Y P hY hn
  have hπker : π.ker =
      (sourceStarAlpha d.radical Y ⊓ fixedCore d.radical (alpha d.radical)).subgroupOf
        (sourceStarAlpha d.radical Y) := by
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
  let sec : BinaryConjugationSection S (sourceStarAlpha d.radical Y)
      (sourceStarAlpha d.radical Y ⊓ fixedCore d.radical (alpha d.radical)) (σ.comp κ) := {
    section_le := sourceStarAlpha_le_stabilizer _ _
    kernel_le := inf_le_left
    normalized := sourceStarAlpha_normalized _ _
    coordinates := π
    onto := (fixedQuotientProjection_surjective A L₀).comp e.symm.surjective
    kernel_eq := hπker
    equivariant := by
      intro g a
      change _ = σ (κ g) (π a).toAdd
      rw [hσ]
      exact fixedQuotientProjection_equivariant A L₀ g (e.symm a) }
  have hfixed : fixedSpace σ
      (((Ltilde d.radical (alpha d.radical)).subgroupOf S).map κ) = ⊥ := by
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
