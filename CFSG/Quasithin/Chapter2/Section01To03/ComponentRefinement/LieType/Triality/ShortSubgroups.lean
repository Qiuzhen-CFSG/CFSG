module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.ParabolicTransport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.BlockNumerics
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Arms
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Central
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.CentralCover
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Triality.ShortSubgroups.CoreAction

/-!
# Short-subgroup obstructions in relative triality parabolics

For either root node, every subnormal two-perfect actor whose full radical
commutator has exponent two is trivial. The proved arms and central root
calculations place it in the radical, and two-perfection then kills it.
These calculations use the genuine graph-field carrier and full parabolics;
the local Levi quotients are PSL₂(q³) at the arms node and PSL₂(q) at the
central node. At q = 2 the central calculation still detects order-three
actors on the first cubic-field root layer, so no perfectness assertion for
PSL₂(2) or exclusion merely from its order six is used.

The actual Sylow-conjugates of the transported parabolic form a normal base
in its join with S, with two-group quotient. The component-orbit theorem,
applied relative to H, maps this base onto a finite power of the full
parabolic with two-group kernel. Two-perfection places each proposed short
subgroup B in this base. Every coordinate maps the base's two-core onto the
parabolic radical, and subnormality forces the entire radical commutator
into the image of U(B). The root obstruction kills all coordinates; the
common two-group kernel then kills B, contradicting its nonzero module.

Thus neither overgroup contains any short subnormal subgroup, a stronger
conclusion than the required moved χ₀-block obstruction. S may permute
components, and no unknown block is identified with a full local factor.
Only the supplied N_S(L)-invariance is needed from the geometric hypotheses.
Construction of that invariance and the final 2.3.9(7) exclusion remain with
the parent source assembly.

Sources: Aschbacher–Smith C.1.7/C.1.12, F.1.11–12, and the proof of
2.3.9(7), printed pp.123–124, 262–264 and 526 (`refs/quasithin.pdf`);
GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

open Subgroup ChapterC Theory.GroupTheory
open _root_.Triality.Standard

/-- Every two-perfect subnormal parabolic actor with elementary radical
commutator is trivial. The full radical-square rigidity includes q = 2
and its order-three actors, without asserting PSL₂(2) is perfect. -/
theorem parabolic_actor_eq_bot (P : Parameters) (hp : P.prime = 2)
    (a : Parabolics.Node) (X : Subgroup (Parabolics.parabolic P a))
    (hsub : X.IsSubnormal) (hperfect : IsPPerfect 2 X)
    (hsq : ∀ x ∈ ⁅pCore 2 (Parabolics.parabolic P a), X⁆,
      (x : Parabolics.parabolic P a) ^ 2 = 1) : X = ⊥ := by
  rw [Parabolics.parabolic_twoCore_eq P hp a] at hsq
  have hR : X ≤ (Parabolics.radical P a).subgroupOf (Parabolics.parabolic P a) := by
    cases a with
    | arms => exact Parabolics.arms_subnormal_radical_le_of_commutator_squares P hp X hsub hsq
    | central => exact Parabolics.central_subnormal_radical_le P hp X hsub hperfect hsq
  have htwo : IsPGroup 2 X :=
    (RadicalCoordinates.radical_isPGroup P hp a).comap_subtype.to_le hR
  have hone := hperfect.hom_eq_one_of_isPGroup htwo (MonoidHom.id X)
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun hone ⟨x, hx⟩)

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem center_eq_bot_of_equiv {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (hz : center D = ⊥) : center A = ⊥ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [center_map_equiv, Subgroup.map_bot, hz]

private theorem component_center_eq_bot {P : Parameters} (hp : P.prime = 2)
    (e : L ≃* Carrier P) : center L = ⊥ := by
  let ec : ElementaryGroup P ≃* Carrier P :=
    MulEquiv.ofBijective (toCarrier P)
      ⟨ElementaryCentralKernel.toCarrier_injective P hp, toCarrier_surjective P⟩
  exact center_eq_bot_of_equiv (e.trans ec.symm) (ElementaryCentralKernel.center_eq_bot P hp)

/-- The literal pullback-and-embedding parabolic is equivalent to the
full root parabolic, including its torus. -/
def componentParabolicEquiv {P : Parameters} (e : L ≃* Carrier P)
    (a : Parabolics.Node) : componentParabolic e a ≃* Parabolics.parabolic P a :=
  (((Parabolics.parabolic P a).comap e.toMonoidHom).equivMapOfInjective
    L.subtype L.subtype_injective).symm.trans
    ((MulEquiv.subgroupCongr (comap_equiv_eq_map_symm' e _)).trans
      (e.symm.subgroupMap (Parabolics.parabolic P a)).symm)

/-- No short subnormal subgroup occurs in either relative parabolic
overgroup. The actual Sylow subgroup may permute components. -/
theorem parabolicOvergroup_not_short (h : LocalSetup H L M S z)
    {P : Parameters} (hp : P.prime = 2) (e : L ≃* Carrier P)
    (a : Parabolics.Node)
    (hinv : ((S : Subgroup H).map H.subtype) ⊓ normalizer L ≤
      normalizer (componentParabolic e a))
    (B : Subgroup (parabolicOvergroup e ((S : Subgroup H).map H.subtype) a))
    (hsub : B.IsSubnormal) : ¬ IsShort B := by
  let := h.finite
  let A := (S : Subgroup H).map H.subtype
  let K := componentParabolic e a
  let ef := componentParabolicEquiv e a
  have hk : IsPGroup 2 ef.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr ef.injective]
    exact IsPGroup.of_bot
  have hz (x : K) (hx : (⟨x.val, componentParabolic_le e a x.property⟩ : L) ∈ center L) :
      ef x = 1 := by
    rw [component_center_eq_bot hp e, mem_bot] at hx
    have hx1 : x = 1 := Subtype.ext (congrArg (fun t : L => (t : G)) hx)
    rw [hx1, map_one]
  obtain ⟨n, F, hF, hFk⟩ := h.component.local_orbit_surjection_power_in
    h.component_le (map_subtype_le _) (componentParabolic_le e a) hinv
    ef.toMonoidHom ef.surjective hk hz
  let N := (componentOrbit K A).subgroupOf (parabolicOvergroup e A a)
  let en : N ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let : N.Normal := componentOrbit_normal_subgroupOf_sup K A
  exact ShortSubgroups.not_short_of_power_cover N
    (local_orbit_quotient_isPGroup K A (S.isPGroup'.map H.subtype)) n
    (F.comp en.toMonoidHom) (hF.comp en.surjective)
    (hFk.comap_of_injective en.toMonoidHom en.injective)
    (parabolic_actor_eq_bot P hp a) B hsub

/-- The relative χ₀-block obstruction for one specified node. -/
theorem parabolicOvergroup_blockObstruction (h : LocalSetup H L M S z)
    {P : Parameters} (hp : P.prime = 2) (e : L ≃* Carrier P)
    (a : Parabolics.Node)
    (hinv : ((S : Subgroup H).map H.subtype) ⊓ normalizer L ≤
      normalizer (componentParabolic e a)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (parabolicOvergroup e ((S : Subgroup H).map H.subtype) a) := by
  intro B hb _
  exact (parabolicOvergroup_not_short h hp e a hinv B hb.1.subnormal hb.1.short).elim

/-- Both source obstructions, under only the needed parabolic-invariance
premises. The unipotent marking, inner action and He membership can be
supplied by the source assembly but are unnecessary for this stronger result. -/
theorem parabolicOvergroup_blockObstructions (h : LocalSetup H L M S z)
    {P : Parameters} (hp : P.prime = 2) (e : L ≃* Carrier P)
    (hinv : ∀ a, ((S : Subgroup H).map H.subtype) ⊓ normalizer L ≤
      normalizer (componentParabolic e a)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (parabolicOvergroup e ((S : Subgroup H).map H.subtype) .arms) ∧
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (parabolicOvergroup e ((S : Subgroup H).map H.subtype) .central) :=
  ⟨parabolicOvergroup_blockObstruction h hp e .arms (hinv .arms),
    parabolicOvergroup_blockObstruction h hp e .central (hinv .central)⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.TrialityCase

end
