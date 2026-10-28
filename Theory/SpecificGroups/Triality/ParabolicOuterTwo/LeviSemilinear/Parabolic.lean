module

public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Stabilizer
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Inner actions of the actual triality parabolics on their local quotients

Relative normality of the embedded prime-to-two residual defines conjugation
from the actual parabolic into its local stabilizer. The existing root-word
calculation splits the full split Levi into the subsystem and a centralizing
torus: characteristic-two square roots realize the diagonal action internally.
Uniqueness of those factors makes both graph-field fixed, and the fixed torus
words are elementary. Their descent therefore gives the same conjugation on
the root Levi as an actual Levi element.

The root Levi surjects onto the intrinsic local two-core quotient. Thus the
torus action on that quotient is inner. Generation of the full parabolic by
its local factor and torus proves innerness for every parabolic element.

Sources: GLS3 §§2.4 and 2.6, especially Theorem 2.6.5(f,g),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith F.1.12, printed p.264,
`refs/quasithin.pdf`. No ambient normality or automorphism classification is used.
-/

@[expose] public section
open scoped Pointwise
noncomputable section
namespace Triality.Standard.ParabolicOuterTwo
open Parabolics OuterOdd RadicalCoordinates ConcreteBruhat

def parabolicInner (P : Parameters) (a : Node) :
    parabolic P a →* localStabilizer P a :=
  (MulAut.conj.comp (parabolic P a).subtype).codRestrict _ (by
    intro g
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (localFactor_le_parabolic P a)).mp (localFactor_normal P a) g.property)

@[simp] theorem parabolicInner_val (P : Parameters) (a : Node) (g : parabolic P a) :
    (parabolicInner P a g).val = MulAut.conj g.val := rfl

theorem parabolicInner_local (P : Parameters) (a : Node) (g : localFactor P a) :
    parabolicInner P a (Subgroup.inclusion (localFactor_le_parabolic P a) g) =
      localInner P a g := rfl

private theorem quotient_levi_surjective (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Function.Surjective ((QuotientGroup.mk' (pCore 2 (localFactor P a))).comp
      (Subgroup.inclusion (RadicalCoordinates.levi_le_localFactor P hp a))) := by
  intro z
  refine ⟨localFactorQuotientEquivLevi P hp a z, ?_⟩
  apply (localFactorQuotientEquivLevi P hp a).injective
  exact localLeviProjection_inclusion P hp a _

theorem localQuotientAction_parabolicInner_of_levi (P : Parameters) (hp : P.prime = 2)
    (a : Node) (g : parabolic P a) (l : levi P a)
    (h : ∀ x : levi P a, g.val * x.val * g.val⁻¹ = l.val * x.val * l.val⁻¹) :
    localQuotientAction P a (parabolicInner P a g) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 (localFactor P a))
        (Subgroup.inclusion (RadicalCoordinates.levi_le_localFactor P hp a) l)) := by
  ext z
  obtain ⟨x, rfl⟩ := quotient_levi_surjective P hp a z
  rw [MonoidHom.comp_apply, localQuotientAction_mk]
  simp only [MulAut.conj_apply, ← map_inv, ← map_mul]
  apply congrArg (QuotientGroup.mk' (pCore 2 (localFactor P a)))
  apply Subtype.ext
  exact h x

private theorem central_torus_descends (P : Parameters) (a : Node) (t : ElementaryGroup P)
    (ht : elementaryInclusion P t ∈ splitCentralTorus P a) :
    toCarrier P t ∈ Subgroup.centralizer (levi P a : Set (Carrier P)) := by
  apply Subgroup.mem_centralizer_iff.mpr
  rintro x ⟨xe, hxe, rfl⟩
  have hc : xe * t = t * xe := by
    apply LeviCommutators.elementaryInclusion_injective P
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp ht.2
      (elementaryInclusion P xe) hxe
  exact (map_mul (toCarrier P) xe t).symm.trans
    ((congrArg (toCarrier P) hc).trans (map_mul (toCarrier P) t xe))

private theorem conjugate_mul_central {G : Type*} [Group G] (l t x : G)
    (hx : x * t = t * x) : (l * t) * x * (l * t)⁻¹ = l * x * l⁻¹ := by
  calc
    _ = l * (t * x) * t⁻¹ * l⁻¹ := by group
    _ = _ := by rw [← hx]; group

theorem descended_fullLevi_inner_on_levi (P : Parameters) (hp : P.prime = 2)
    (a : Node) (g : Carrier P) (hg : g ∈ descendSubgroup P (splitFullLevi P a)) :
    ∃ l : levi P a, ∀ x : levi P a,
      g * x.val * g⁻¹ = l.val * x.val * l.val⁻¹ := by
  obtain ⟨y, hy, rfl⟩ := hg
  have hy' : elementaryInclusion P y ∈
      (splitLevi P a : Set (SplitGroup P)) * splitCentralTorus P a :=
    (Set.ext_iff.mp (splitFullLevi_eq_mul_centralTorus P hp a)
      (elementaryInclusion P y)).mp hy
  obtain ⟨l, hl, t, ht, he⟩ := hy'
  have hfix : graphFieldAutomorphism P (l * t) = l * t :=
    (congrArg (graphFieldAutomorphism P) he).trans (y.val.property.trans he.symm)
  have htf := (splitFullLevi_central_factors_fixed P hp a l t hl ht hfix).2
  let tf : fixedSubgroup P := ⟨t, htf⟩
  let te : ElementaryGroup P := ⟨tf, TorusCoordinates.fixedTorus_le_elementary P hp ht.1⟩
  let le : ElementaryGroup P := y * te⁻¹
  have hle : elementaryInclusion P le = l := by
    change elementaryInclusion P y * t⁻¹ = l
    rw [← he, mul_inv_cancel_right]
  have hlc : toCarrier P le ∈ levi P a := by
    refine ⟨le, ?_, rfl⟩
    change elementaryInclusion P le ∈ splitLevi P a
    rw [hle]
    exact hl
  have hprod : toCarrier P le * toCarrier P te = toCarrier P y :=
    (map_mul (toCarrier P) le te).symm.trans
      (congrArg (toCarrier P) (inv_mul_cancel_right y te))
  refine ⟨⟨toCarrier P le, hlc⟩, ?_⟩
  intro x
  have hc : x.val * toCarrier P te = toCarrier P te * x.val :=
    Subgroup.mem_centralizer_iff.mp (central_torus_descends P a te ht) x.val x.property
  exact (congrArg (fun z => z * x.val * z⁻¹) hprod.symm).trans
    (conjugate_mul_central (toCarrier P le) (toCarrier P te) x.val hc)

theorem localQuotientAction_parabolicInner_torus (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : torus P) :
    localQuotientAction P a (parabolicInner P a
      (Subgroup.inclusion ((torus_le_borel P).trans (borel_le_parabolic P a)) t)) ∈
        MulAut.innerSubgroup (LocalTwoQuotient P a) := by
  obtain ⟨l, hl⟩ := descended_fullLevi_inner_on_levi P hp a t.val
    (descendSubgroup_mono P (show splitTorus P ≤ splitFullLevi P a from le_sup_right)
      t.property)
  exact ⟨_, (localQuotientAction_parabolicInner_of_levi P hp a _ l hl).symm⟩

theorem localQuotientAction_parabolicInner (P : Parameters) (hp : P.prime = 2)
    (a : Node) (g : parabolic P a) :
    localQuotientAction P a (parabolicInner P a g) ∈
      MulAut.innerSubgroup (LocalTwoQuotient P a) := by
  have htop : (localFactor P a).subgroupOf (parabolic P a) ⊔
      (torus P).subgroupOf (parabolic P a) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (localFactor_le_parabolic P a)
      ((torus_le_borel P).trans (borel_le_parabolic P a)),
      ← parabolic_eq_localFactor_sup_torus P hp a, Subgroup.subgroupOf_self]
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp
    (htop.symm ▸ Subgroup.mem_top g)
  rw [← hlt, map_mul, map_mul]
  apply Subgroup.mul_mem
  · change localQuotientAction P a (localInner P a ⟨l.val, hl⟩) ∈ _
    rw [localQuotientAction_localInner]
    exact ⟨_, rfl⟩
  · exact localQuotientAction_parabolicInner_torus P hp a ⟨t.val, ht⟩

end Triality.Standard.ParabolicOuterTwo
