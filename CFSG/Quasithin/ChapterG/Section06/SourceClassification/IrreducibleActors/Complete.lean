module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleActors.ScalarDegree
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.QuasisimpleRows
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.AmbientPlacement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Rank-one selection from the complete B.4 actor list

A nontrivial rank-one action forces every scalar-restricted natural field to
have degree one. The full Sylow normalizer of the original cubic then excludes
binary linear actors of degree at least three and all symmetric degrees other
than seven. The remaining exceptional action rows have larger offender rank or
a nontrivial center. This checks every constructor of the genuine B.4 list.

For the original G.6 normal closure, the centralizer is trivial by displacement
generation. Its faithful moved quotient has displacement rank at most one and
retains the same Sylow-normalized cubic. Thus the quasisimple B.5.1 branch is
S7, and the already proved inner-automorphism placement makes the full ambient
actor S7 as well. No classification-output hypothesis is added to G.6.
Source: Aschbacher–Smith, G.6.4, pp.345–346, and C.5.12, p.163.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u v w z

private noncomputable def action_of_top
    {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    {L : Subgroup D} (hL : L = ⊤) (e : ActionEquiv (ρ.comp L.subtype) σ) :
    ActionEquiv ρ σ where
  groupEquiv := (topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ⟨g, by rw [hL]; trivial⟩ v

private theorem action_displacement_eq
    {D E V W : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ) (t : D) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (σ (e.groupEquiv t) - LinearMap.id)) := by
  have he := fixedCodim_map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.linearEquiv e.intertwines (zpowers t)
  simpa only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    fixedCodim_zpowers_eq_displacement_rank] using he

private theorem model_field_degree_one (F : BinaryField)
    {D E V W : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module F.Carrier W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F.Carrier W] [FiniteDimensional F.Carrier W]
    {ρ : Representation (ZMod 2) D V} (hf : Function.Injective ρ)
    (t : D) (ht : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1)
    (σ : Representation F.Carrier E W)
    (e : ActionEquiv ρ (restrictScalars (k := ZMod 2) σ)) : F.degree = 1 := by
  let : FiniteDimensional (ZMod 2) W := Module.Finite.equiv e.linearEquiv
  have hne : σ (e.groupEquiv t) ≠ 1 := by
    intro he
    apply ht
    apply hf
    ext v
    apply e.linearEquiv.injective
    have hh := e.intertwines t v
    change e.linearEquiv (ρ t v) = σ (e.groupEquiv t) (e.linearEquiv v) at hh
    simpa only [he, Module.End.one_apply, map_one] using hh
  have hb := scalar_degree_le_displacement F σ (e.groupEquiv t) hne
  rw [← action_displacement_eq e t] at hb
  have hp := F.degree_pos
  omega

private theorem symmetric_three_not_perfect : ¬ Group.IsPerfect (Equiv.Perm (Fin 3)) := by
  intro h
  let := h
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  have hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.IsPerfect.not_isSolvable _ hs

private theorem klein_seven_rank :
    rank (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
      ChapterB.Offenders.kleinSecond 7 (by decide)}) = 2 := by
  let A := Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
    ChapterB.Offenders.kleinSecond 7 (by decide)}
  let : IsKleinFour A := isKleinFour_closure_pair _ _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by change _ * _ = _ * _; decide)
  rw [rank, IsKleinFour.card_four]
  decide

section IrreducibleActor
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

theorem irreducible_actor_of_rank_one_normalized_cubic
    (L : Subgroup D) (hq : IsQuasisimple L) (hz : center D = ⊥)
    (hf : Function.Injective ρ) (t : D) (htp : t ^ 2 = 1) (htne : t ≠ 1)
    (hcost : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1)
    (S : Sylow 2 D) (c : D) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup D) ≤ normalizer (zpowers c : Set D))
    (hcase : ProjectiveLine.IrreducibleActionCase ρ L ⊤) :
    Nonempty (D ≃* Equiv.Perm (Fin 7)) := by
  classical
  have hb := bestOffender_of_involution_displacement_le_one ρ t htp htne hcost
  have htr : rank (zpowers t) = 1 := by
    rw [rank, Nat.card_zpowers, orderOf_eq_prime htp htne]
    decide
  have binary_exclusion {n : ℕ} (hn3 : 3 ≤ n) (e : D ≃* SL(n,ZMod 2)) : False := by
    have he := binary_actor_degree_of_normalized_cubic S c hc hcne hn (by omega : 2 ≤ n)
      (e.trans (BinaryLinear.OuterCyclic.slEquivLinear n))
    omega
  have symmetric_degree {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (e : D ≃* Equiv.Perm (Fin n)) : n = 7 :=
    (symmetric_model_degree_of_normalized_cubic S c hc hcne hn hlo hhi e).1
  cases hcase with
  | linearTwo F whole e _ _ =>
    let E := action_of_top whole.symm e
    have hF := model_field_degree_one F hf t htne hcost (specialLinearNatural 2) E
    let B := E.groupEquiv.trans
      ((ChapterB.QuasisimpleSource.ExtensionConsequences.degreeOneNaturalEquiv F hF 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsPerfect L := hq.toIsPerfect
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := ((MulEquiv.subgroupCongr whole.symm).trans topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr whole.symm).trans topEquiv).surjective
    exact (symmetric_three_not_perfect
      (Group.IsPerfect.ofSurjective (f := B.toMonoidHom) B.surjective)).elim
  | linearThree F whole e _ =>
    let E := action_of_top whole.symm e
    have hF := model_field_degree_one F hf t htne hcost (specialLinearNatural 3) E
    exact (binary_exclusion (by decide : 3 ≤ 3) (E.groupEquiv.trans
      (ChapterB.QuasisimpleSource.ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv)).elim
  | symplectic F large whole e _ =>
    have hF := model_field_degree_one F hf t htne hcost (symplecticNatural 2)
      (action_of_top whole.symm e)
    omega
  | symplecticTwo e _ =>
    let E := (action_of_top rfl e.action).groupEquiv.trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    have := symmetric_degree (by decide : 5 ≤ 6) (by decide) E
    omega
  | g2 F _ _ _ hoff _ => have := hoff (zpowers t) hb; have := F.degree_pos; omega
  | g2Two _ hoff _ => have := hoff (zpowers t) hb; omega
  | symmetric n hn' e _ _ =>
    let E := (action_of_top rfl e.action).groupEquiv
    have he := symmetric_degree (by rcases hn' with rfl | rfl <;> decide)
      (by rcases hn' with rfl | rfl <;> decide) E
    subst n
    exact ⟨E⟩
  | alternatingSix _ _ hoff _ => have := (hoff (zpowers t) hb).1; omega
  | alternatingSeven whole _ e _ hoff _ =>
    obtain ⟨g, hg⟩ := hoff (zpowers t) hb
    have he := congrArg rank hg
    have hfi : Function.Injective ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom) := by
      intro x y hh
      exact e.injective (Subtype.ext hh)
    rw [rank_map_injective _ hfi,
      rank_subgroupOf (show zpowers t ≤ L by rw [← whole]; exact le_top), htr,
      rank_map_injective _ (MulAut.conj (g : Equiv.Perm (Fin 7))).injective, klein_seven_rank] at he
    omega
  | tripleSix whole action _ =>
    have he := Nat.card_congr (Subgroup.centerCongr
      ((MulEquiv.subgroupCongr whole.symm).trans topEquiv)).toEquiv
    rw [Nat.card_congr action.centerEquiv.toEquiv, hz] at he
    norm_num at he
  | binaryLinear n hn' whole e _ =>
    exact (binary_exclusion (by rcases hn' with rfl | rfl <;> decide)
      (action_of_top whole.symm e).groupEquiv).elim
  | orthogonalSix _ _ _ hoff _ => have := hoff (zpowers t) hb; omega
  | symmetricEight _ e _ =>
    have he := symmetric_degree (by decide : 5 ≤ 8) le_rfl (action_of_top rfl e.action).groupEquiv
    omega
  | exteriorFive whole _ e _ _ _ =>
    exact (binary_exclusion (by decide : 3 ≤ 5)
      ((topEquiv.symm.trans (MulEquiv.subgroupCongr whole)).trans e)).elim

end IrreducibleActor

section OriginalSource
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalClosure_center_eq_bot
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    center (normalClosure ({a} : Set G)) = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hm : (x : G) ∈ centralizer (normalClosure ({a} : Set G) : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
  have he : (x : G) = 1 := by
    simpa only [h.rank_one_centralizer_normalClosure_eq_bot hr, mem_bot] using hm
  exact Subtype.ext he

theorem Hypotheses.quasisimple_actor_of_normalized_inverted_cubic
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    (hq : IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))))
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G)))) :
    Nonempty (G ≃* Equiv.Perm (Fin 7)) := by
  let := h.finite_group
  let := h.finite_module
  let K := normalClosure ({a} : Set G)
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  let c' : K := ⟨c, inverted_element_mem_normalClosure a c hi⟩
  obtain ⟨P, _, hp⟩ := sylow_normalizes_cubic_in_normal S K c' hn
  obtain ⟨_, _, hf, _, hcase⟩ :=
    h.quasisimple_irreducible_of_normalized_cubic ht S c hc hcne hi hn hq d
  have hcost : Module.finrank (ZMod 2)
      (LinearMap.range (d.sectionData.central.quotientRepresentation t - LinearMap.id)) ≤ 1 :=
    (subquotient_displacement_rank_le (ρ.comp K.subtype)
      d.sectionData.space d.sectionData.central t).trans ht.le
  obtain ⟨e⟩ := irreducible_actor_of_rank_one_normalized_cubic
    (generalizedFitting K) hq (h.normalClosure_center_eq_bot ht) hf t
    (Subtype.ext h.involution) (fun he => h.nonidentity (congrArg Subtype.val he)) hcost
    P c' (Subtype.ext hc) (fun he => hcne (congrArg Subtype.val he)) hp hcase
  exact h.ambient_symmetric_seven_of_normalClosure ht e
end OriginalSource
end CFSG.Quasithin.ChapterG.Section06
