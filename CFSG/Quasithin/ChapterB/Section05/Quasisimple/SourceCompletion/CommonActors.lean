module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefNaturality
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.DoubleNaturalFF
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCohomology
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.Representation.BinaryOffender.Embedding

/-!
# Common actors and mixed natural-constituent exclusion

The proved inner/graph automorphism theorem aligns each binary natural
constituent with one fixed group marking, giving an actual intertwiner to
the marked natural module or its contragredient. Two independent natural
markings therefore yield genuinely isomorphic or dual modules.

The first-coordinate submodule of their product and its literal quotient
form a DoubleNatural object. The complete B.4.9 theorem gives ratio one
in dimension four and five sixths in dimension five for a mixed pair.
An actual equivariant embedding of disjoint summands transfers the original
quadratic actor's ratio bound, excluding mixed pairs at the chief bound.

A separate same-actor restriction argument retains the original best offender
on each constituent. Its B.4.2 generation equality can therefore put this
same subgroup inside the original component.

Source: Aschbacher--Smith B.5.1, pp.100–101, the homogeneity step following
(++); B.4.9(2)(iii)–(iv), pp.94–95. A.1.42 and chief irreducibility follow.
-/

@[expose] public noncomputable section
open Representation Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v w

private theorem binary_inner_graph {d : ℕ} (hd : d = 4 ∨ d = 5)
    (a : MulAut SL(d,ZMod 2)) :
    ∃ g, a = MulAut.conj g ∨ a = BinaryLinear.OuterCyclic.graphSL d * MulAut.conj g := by
  open BinaryLinear.OuterCyclic in
  obtain ⟨g, hg⟩ := inner_graph hd (MulAut.congr (slEquivLinear d) a)
  refine ⟨(BinaryLinear.OuterCyclic.slEquivLinear d).symm g, ?_⟩
  rcases hg with hg | hg
  · left
    apply (MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear d)).injective
    simpa only [MulAut.congr_conj, MulEquiv.apply_symm_apply] using hg
  · right
    apply (MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear d)).injective
    simpa only [map_mul, MulAut.congr_conj, MulEquiv.apply_symm_apply,
      BinaryLinear.OuterCyclic.graphLinear] using hg

private def inner_untwist {D E X Y : Type*} [Group D] [Group E]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) D X} {σ : Representation (ZMod 2) E Y}
    (a : ActionEquiv ρ σ) (mark : D ≃* E) (g : E)
    (ha : ∀ x, a.groupEquiv x = g * mark x * g⁻¹) :
    ρ.Equiv (σ.comp mark.toMonoidHom) :=
  .mk (a.linearEquiv.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom g⁻¹))) (by
    intro x
    apply LinearMap.ext
    intro v
    change σ g⁻¹ (a.linearEquiv (ρ x v)) = σ (mark x) (σ g⁻¹ (a.linearEquiv v))
    rw [a.intertwines, ha]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left, mul_assoc])

/-- An arbitrary natural action has a genuine linear intertwiner to the
fixed marked natural action or its literal contragredient. -/
theorem binary_natural_fixed_mark {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hρ : IsLinearNatural ρ BinaryField.two d) (mark : G ≃* SL(d,ZMod 2)) :
    Nonempty (ρ.Equiv ((linearNatural BinaryField.two d).comp mark.toMonoidHom)) ∨
    Nonempty (ρ.Equiv ((linearNatural BinaryField.two d).dual.comp mark.toMonoidHom)) := by
  obtain ⟨a⟩ := hρ
  let α : MulAut SL(d,ZMod 2) := mark.symm.trans a.groupEquiv
  obtain ⟨g, hg | hg⟩ := binary_inner_graph hd α
  · left
    refine ⟨inner_untwist a mark g ?_⟩
    intro x
    have hh := congrArg (fun z : MulAut SL(d,ZMod 2) => z (mark x)) hg
    change a.groupEquiv (mark.symm (mark x)) = g * mark x * g⁻¹ at hh
    rw [mark.symm_apply_apply] at hh
    exact hh
  · right
    let graph := BinaryLinear.OuterCyclic.graphSL d
    let σ := linearNatural BinaryField.two d
    have ha : ∀ x, a.groupEquiv x = graph (g * mark x * g⁻¹) := by
      intro x
      have hh := congrArg (fun z : MulAut SL(d,ZMod 2) => z (mark x)) hg
      change a.groupEquiv (mark.symm (mark x)) = graph (g * mark x * g⁻¹) at hh
      simpa only [mark.symm_apply_apply] using hh
    let e : ρ.Equiv (σ.comp (mark.trans graph).toMonoidHom) :=
      inner_untwist a (mark.trans graph) (graph g) (by
        intro x
        rw [ha, map_mul, map_mul, map_inv]
        rfl)
    let de : Representation.Equiv (σ.comp (mark.trans graph).toMonoidHom) (σ.dual.comp mark.toMonoidHom) :=
      .mk (dualNaturalEquiv d).linearEquiv.symm (by
        intro x
        apply LinearMap.ext
        intro v
        apply (dualNaturalEquiv d).linearEquiv.injective
        change (dualNaturalEquiv d).linearEquiv
          ((dualNaturalEquiv d).linearEquiv.symm (σ (graph (mark x)) v)) =
          (dualNaturalEquiv d).linearEquiv (σ.dual (mark x) ((dualNaturalEquiv d).linearEquiv.symm v))
        rw [(dualNaturalEquiv d).linearEquiv.apply_symm_apply]
        have hh := ((dualNaturalEquiv d).intertwines (mark x)
          ((dualNaturalEquiv d).linearEquiv.symm v)).symm
        rw [(dualNaturalEquiv d).linearEquiv.apply_symm_apply] at hh
        rw [show (dualNaturalEquiv d).groupEquiv = graph from rfl] at hh
        exact hh)
    exact ⟨e.trans de⟩

private def dual_equiv {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) G X} {σ : Representation (ZMod 2) G Y}
    (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  .mk e.symm.toLinearEquiv.dualMap (by
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro w
    change f (ρ g⁻¹ (e.symm w)) = f (e.symm (σ g⁻¹ w))
    exact congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' g⁻¹) w).symm)

private theorem dual_comp_eq {G H X : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) H X) (f : G →* H) :
    Representation.dual (σ.comp f) = σ.dual.comp f := by
  ext g l v
  change l (σ (f g⁻¹) v) = l (σ ((f g)⁻¹) v)
  rw [map_inv]

/-- For the same binary linear actor two independently marked natural
modules are actually isomorphic or contragredient, with explicit intertwiners. -/
theorem binary_naturals_same_or_dual {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hρ : IsLinearNatural ρ BinaryField.two d) (hσ : IsLinearNatural σ BinaryField.two d) :
    Nonempty (ρ.Equiv σ) ∨ Nonempty (ρ.Equiv σ.dual) := by
  obtain ⟨a⟩ := hσ
  let e : σ.Equiv ((linearNatural BinaryField.two d).comp a.groupEquiv.toMonoidHom) :=
    .mk a.linearEquiv (by intro g; apply LinearMap.ext; intro v; exact a.intertwines g v)
  rcases binary_natural_fixed_mark ρ hd hρ a.groupEquiv with h | h
  · obtain ⟨h⟩ := h
    exact Or.inl ⟨h.trans e.symm⟩
  · obtain ⟨h⟩ := h
    have he := (dual_equiv e).symm
    rw [dual_comp_eq] at he
    exact Or.inr ⟨h.trans he⟩

/-- A best offender remains best on an invariant subrepresentation with the
same actor. This retains the original subgroup rather than replacing it by
a subgroup selected anew inside its action image. -/
theorem bestOffender_on_subrepresentation {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (W : Subrepresentation ρ)
    {B : Subgroup G} (hB : IsBestOffender ρ B) : IsBestOffender W.toRepresentation B := by
  refine ⟨hB.1, fun D hD => ?_⟩
  have hh := hB.restriction_weight_le ρ hD W.toSubmodule
  have hdb := (subrepresentationFixedEquiv ρ W D).finrank_eq
  have hbb := (subrepresentationFixedEquiv ρ W B).finrank_eq
  unfold weight
  rwa [hdb, hbb]

/-- The common original best offender lies inside the component whenever
the full earlier constituent conclusion generates precisely that component. -/
theorem constituent_generation_contains_offender {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (C : Subgroup G) [IsQuasisimple C]
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : IsBestOffender ρ B)
    (W : Subrepresentation (ρ.comp C.subtype))
    (hs : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule)
    (hgen : offenderSubgroup
      (invariantSubspace ρ (C ⊔ B) W.toSubmodule hs).toRepresentation =
        generalizedFitting ↥(C ⊔ B)) : B ≤ C := by
  let H := C ⊔ B
  let J := invariantSubspace ρ H W.toSubmodule hs
  have hb := bestOffender_on_subrepresentation (ρ.comp H.subtype) J
    (hB.subgroupOf ρ (show B ≤ H from le_sup_right))
  have hbf : B.subgroupOf H ≤ generalizedFitting H :=
    hb.le_offenderSubgroup J.toRepresentation |>.trans_eq hgen
  intro b hb
  have hbh : b ∈ H := (show B ≤ H from le_sup_right) hb
  have hmem : (⟨b, hbh⟩ : H) ∈ generalizedFitting H := hbf hb
  exact ((local_component_equiv ρ C hfit hcore hB) ⟨⟨b, hbh⟩, hmem⟩).property

namespace NaturalPair
variable {G X Y : Type*} [Group G]
  [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
  (ρ : Representation (ZMod 2) G X) (σ : Representation (ZMod 2) G Y)

private def first : Subrepresentation (ρ.prod σ) where
  toSubmodule := LinearMap.ker (LinearMap.snd (ZMod 2) X Y)
  apply_mem_toSubmodule g v hv := by
    change σ g v.2 = 0
    rw [show v.2 = 0 from hv, map_zero]

private def firstEquiv : (first ρ σ).toRepresentation.Equiv ρ where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), rfl⟩
  left_inv v := by apply Subtype.ext; exact Prod.ext rfl v.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

private def quotientEquiv : (first ρ σ).quotientRepresentation.Equiv σ :=
  .mk ((LinearMap.snd (ZMod 2) X Y).quotKerEquivOfSurjective LinearMap.snd_surjective) (by
    intro g
    apply LinearMap.ext
    intro v
    refine Submodule.Quotient.induction_on _ v ?_
    intro w
    rfl)

/-- The actual product of a natural module and its contragredient is a
DoubleNatural object with its literal first-coordinate submodule. -/
private def dualDoubleNatural {F : BinaryField} {n : ℕ}
    (hf : Function.Injective ρ) (a : ActionEquiv ρ (linearNatural F n))
    (e : σ.Equiv ρ.dual) : NaturalExtensions.DoubleNatural F n (ρ.prod σ) where
  faithful := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro x
    exact congrArg Prod.fst (LinearMap.congr_fun he (x, 0))
  space := first ρ σ
  natural := {
    groupEquiv := a.groupEquiv
    linearEquiv := (firstEquiv ρ σ).toLinearEquiv.trans a.linearEquiv
    intertwines := by intro g v; exact a.intertwines g v.val.1 }
  quotient := Or.inr ⟨(quotientEquiv ρ σ).trans (e.trans (dual_equiv (firstEquiv ρ σ)).symm)⟩

/-- B.4.9 excludes a mixed natural/dual pair at the binary chief-factor
ratio bounds. No splitting premise is needed on the actual product. -/
theorem three_quarters_lt_dual_ratio [Finite G]
    [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) Y]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hf : Function.Injective ρ)
    (a : ActionEquiv ρ (linearNatural BinaryField.two d))
    (e : σ.Equiv ρ.dual) (hff : IsFFModule (ρ.prod σ)) :
    (3 / 4 : ℝ≥0∞) < quadraticRatio (ρ.prod σ) := by
  let D := dualDoubleNatural ρ σ hf a e
  let de : D.space.quotientRepresentation.Equiv D.space.toRepresentation.dual :=
    (quotientEquiv ρ σ).trans (e.trans (dual_equiv (firstEquiv ρ σ)).symm)
  obtain ⟨A, hA⟩ := hff
  obtain ⟨B, _, hB⟩ := hA.exists_bestOffender (ρ.prod σ)
  obtain ⟨T, hT⟩ := (show IsPGroup 2 B from hB.1.2.isPGroup 2 B).exists_le_sylow
  rcases hd with rfl | rfl
  · rw [(doubleNatural_four_dual_ff D rfl de T hT hB).2.2.2]
    apply (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (by norm_num)).mp
    norm_num [ENNReal.toReal_div]
  · rw [(doubleNatural_five_dual_ff D rfl de T hT hB).2.1]
    apply (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
end NaturalPair

/-- Disjoint invariant summands give an actual injective equivariant product
map. Their quadratic ratio is bounded by the same original quadratic actor. -/
theorem pair_ratio_le_actionRatio {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)
    (hd : Disjoint U.toSubmodule W.toSubmodule) {B : Subgroup G}
    (hb : IsElementaryTwo B) (hq : IsQuadratic ρ B) :
    quadraticRatio (U.toRepresentation.prod W.toRepresentation) ≤ actionRatio ρ B := by
  let π := U.toRepresentation.prod W.toRepresentation
  let e : U.toSubmodule × W.toSubmodule →ₗ[ZMod 2] V :=
    U.toSubmodule.subtype.coprod W.toSubmodule.subtype
  have hei : Function.Injective e := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    rintro ⟨u, w⟩ h
    change u.val + w.val = 0 at h
    have hu : u.val ∈ W.toSubmodule := by
      rw [eq_neg_of_add_eq_zero_left h]
      exact W.toSubmodule.neg_mem w.property
    have hu0 : u.val = 0 := (Submodule.disjoint_def.mp hd) u.val u.property hu
    have hw0 : w.val = 0 := by simpa only [hu0, zero_add] using h
    change (u, w) = (0, 0)
    exact Prod.ext (Subtype.ext hu0) (Subtype.ext hw0)
  have he (g : G) (v : U.toSubmodule × W.toSubmodule) : ρ g (e v) = e (π g v) :=
    map_add (ρ g) v.1.val v.2.val
  have hp : IsQuadratic π B := by
    intro a ha b hb v
    apply hei
    simpa only [← he, map_sub] using hq a ha b hb (e v)
  have hcod : fixedCodim π B ≤ fixedCodim ρ B := by
    simpa only [Subgroup.map_id] using
      fixedCodim_map_le_of_embedding ρ π (MonoidHom.id G) e hei he B
  apply (iInf_le_of_le B (iInf_le_of_le ⟨hb, hp⟩ le_rfl)).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast hcod

/-- At the source chief bound, two disjoint faithful binary natural
constituents cannot be contragredient. The excluded product is a concrete
B.4.9 double-natural section, not an assumed module-shape conclusion. -/
theorem no_binary_dual_pair {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)
    (hdis : Disjoint U.toSubmodule W.toSubmodule) {B : Subgroup G}
    (hb : IsElementaryTwo B) (hq : IsQuadratic ρ B)
    (hr : actionRatio ρ B ≤ 3 / 4) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hf : Function.Injective U.toRepresentation)
    (hn : IsLinearNatural U.toRepresentation BinaryField.two d)
    (e : W.toRepresentation.Equiv U.toRepresentation.dual) : False := by
  have hp := pair_ratio_le_actionRatio ρ U W hdis hb hq
  have hff : IsFFModule (U.toRepresentation.prod W.toRepresentation) :=
    isFFModule_of_quadraticRatio_le_one _ ((hp.trans hr).trans (by
      apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (by norm_num)).mp
      norm_num [ENNReal.toReal_div]))
  obtain ⟨a⟩ := hn
  exact (not_le_of_gt (NaturalPair.three_quarters_lt_dual_ratio _ _ hd hf a e hff)) (hp.trans hr)

/-- Under the actual chief-factor offender bound all disjoint binary natural
constituents have the same module type for their original actor. -/
theorem binary_disjoint_naturals_same {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)
    (hdis : Disjoint U.toSubmodule W.toSubmodule) {B : Subgroup G}
    (hb : IsElementaryTwo B) (hq : IsQuadratic ρ B)
    (hr : actionRatio ρ B ≤ 3 / 4) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hf : Function.Injective U.toRepresentation)
    (hnU : IsLinearNatural U.toRepresentation BinaryField.two d)
    (hnW : IsLinearNatural W.toRepresentation BinaryField.two d) :
    Nonempty (W.toRepresentation.Equiv U.toRepresentation) := by
  rcases binary_naturals_same_or_dual W.toRepresentation U.toRepresentation hd hnW hnU with h | h
  · exact h
  · obtain ⟨h⟩ := h
    exact (no_binary_dual_pair ρ U W hdis hb hq hr hd hf hnU h).elim

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
