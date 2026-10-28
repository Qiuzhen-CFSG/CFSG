module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.Geometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Transport

/-!
# The actual component quotient for parabolic recognition

The component map supplies the Sylow subgroup and the genuine model
equivalences in the action quotient. Simple components map isomorphically;
the central two-covers instead use the canonical central-quotient equivalence.
The field-degree hypothesis removes precisely the degree-one alternatives.
No larger-field Lie family is removed by this reduction.

Source: Aschbacher--Smith, 1.1.5(3)(a)--(c), pp.501--502, A.2.3--4,
p.33, and 15.3.43(e), p.1140.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

omit [Finite G] in
theorem quotient_generated :
    c.toComponentAction.image L ⊔ c.toComponentAction.image S = ⊤ := by
  have hSI : S ≤ I := (sylow_le_local c).trans inf_le_right
  change (L.subgroupOf I).map c.toComponentAction.quotientMap ⊔
    (S.subgroupOf I).map c.toComponentAction.quotientMap = ⊤
  rw [← Subgroup.map_sup, ← subgroupOf_sup c.component_le hSI, ← c.generated,
    subgroupOf_self, map_top_of_surjective _ c.toComponentAction.quotientMap_surjective]

theorem quotient_component_sylow :
    ∃ P : Sylow 2 (c.toComponentAction.image L),
      (P : Subgroup (c.toComponentAction.image L)).map
        (c.toComponentAction.image L).subtype =
          c.toComponentAction.image S ⊓ c.toComponentAction.image L := by
  obtain ⟨P, hP⟩ := component_sylow c
  have he : (P : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  refine ⟨P.mapSurjective c.toComponentAction.componentMap_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, he]
  exact componentMap_sylow_image c

omit [Finite G] in
theorem quotient_component_nonabelian :
    ¬ IsMulCommutative (c.toComponentAction.image L) := by
  let : IsQuasisimple (L.subgroupOf I) := c.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le)
  let : Group.IsPerfect (c.toComponentAction.image L) :=
    Group.IsPerfect.ofSurjective c.toComponentAction.componentMap_surjective
  let : IsSimpleGroup (c.toComponentAction.image L) := c.quotient.simple
  exact Group.IsPerfect.not_isMulCommutative _

/-- For a simple incoming component the actual action map is an isomorphism. -/
noncomputable def simpleComponentEquiv [IsSimpleGroup L] :
    L ≃* c.toComponentAction.image L := by
  let : IsQuasisimple (L.subgroupOf I) := c.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le)
  have hc : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp h)).elim
  exact MulEquiv.ofBijective c.toComponentAction.componentMap
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (c.toComponentAction.componentMap_ker.trans hc),
      c.toComponentAction.componentMap_surjective⟩

omit [Finite G] in
/-- Exhaustive transport of the larger-field alternatives. The two exceptional
central covers use `L/Z(L)`, without identifying that quotient with `L`. -/
theorem quotient_model {z : G} {n : ℕ} (hn : 1 < n) (hm : Model L z n) :
    ClassicalGroup.IsPSL (c.toComponentAction.image L) 2 (2 ^ n) ∨
    ClassicalGroup.IsPSU (c.toComponentAction.image L) 3 (2 ^ n) ∨
    ChapterA.Section02.IsTheoremCRankTwoModel (c.toComponentAction.image L) n := by
  cases hm with
  | simple hs hm _ =>
    let : IsSimpleGroup L := hs
    let e := (simpleComponentEquiv c).symm
    cases hm with
    | linearTwo _ hi => exact .inl (hi.of_mulEquiv e)
    | unitaryThree _ hi => exact .inr (.inl (hi.of_mulEquiv e))
    | rankTwo hi =>
      cases hi with
      | linear hf hi => exact .inr (.inr (.linear hf (hi.of_mulEquiv e)))
      | symplectic hf hi => exact .inr (.inr (.symplectic hf (hi.of_mulEquiv e)))
      | g2 hf hi => exact .inr (.inr (.g2 hf (hi.of_mulEquiv e)))
      | triality hf hi => exact .inr (.inr (.triality hf (hi.of_mulEquiv e)))
      | ree_f4 m hm he hi => exact .inr (.inr (.ree_f4 m hm he (hi.map (e.trans ·))))
      | symplectic_derived he _ => omega
      | g2_derived he _ => omega
      | tits he _ => omega
    | binaryLinear he _ _ _ => omega
  | linearThreeCover he _ hi _ =>
    subst n
    exact .inr (.inr (.linear (by decide)
      (hi.of_mulEquiv c.toComponentAction.centerQuotientEquiv.symm)))
  | g2Cover he _ hi _ =>
    subst n
    exact .inr (.inr (.g2 (by decide)
      (hi.of_mulEquiv c.toComponentAction.centerQuotientEquiv.symm)))
  | alternatingSix he _ _ => omega

/-- Final recognition from the two independent geometric producers, specialized
to the literal images in `I/C_I(L)`. -/
theorem quotientParabolic_of_geometry
    (hhull : InvariantHull (c.toComponentAction.image L) (c.toComponentAction.image S)
      (c.toComponentAction.image M))
    (hcores : ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S)) :
    QuotientParabolic c := by
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T, hT⟩ := c.toComponentAction.image_sylow P hP
  exact maximalInvariantParabolic_of_geometry _ _ _ (quotient_generated c)
    (hT ▸ T.isPGroup') (map_mono (fun _ hx => c.sylow_le_M hx))
    c.quotient.maximal hhull hcores

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
