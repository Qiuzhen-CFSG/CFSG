module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Components
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Transfer
public import Theory.GroupAction.OddInvolutionFrattini

/-!
# Solvability of the radical section centralizer

Write X = Ξ_p(L). The A.3.6 alternatives make X/O₂(X) noncyclic, hence
its Frattini quotient is noncyclic. The authorized radical structural input,
irreducibility of N_L(P) on P/Φ(P), therefore gives a nontrivial L-action
on X/O₂,Φ(X). In particular L does not centralize X/O₂(X).

The section centralizer C is normal in LT, whose solvable residual is the
C-component L. If C were nonsolvable, its nontrivial perfect residual would
be subnormal in LT and contained in L; minimality of L would force L ≤ C.
This proves solvability without any assumption about Y = N_L(O₂(XT))^∞.
The existing Components leaf then supplies the C-component conclusions.

The universal A.3.6 and A.3.8 implications and the original normalizer-action
witness remain explicit inputs, as authorized for this task. The ambient
Chapter 1 application supplies the displayed local SQTK hypothesis.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.512–513; A.3.3 and A.3.6, pp.42–45.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.ChapterA.Section04

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers

private theorem action_nontrivial {A Q : Type*} [Group A] [Group Q]
    (hn : ¬ IsCyclic Q) (f : A →* MulAut Q)
    (hi : ∀ B : Subgroup Q, (∀ a, ∀ b ∈ B, f a b ∈ B) → B = ⊥ ∨ B = ⊤) :
    ∃ a, f a ≠ 1 := by
  by_contra! ht
  have hB (B : Subgroup Q) : B = ⊥ ∨ B = ⊤ := hi B (by simp [ht])
  have hnt : Nontrivial Q := not_subsingleton_iff_nontrivial.mp (by
    intro hs
    let := hs
    exact hn inferInstance)
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  exact hn (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x,
    (hB (zpowers x)).resolve_left (by
      intro he
      exact hx (mem_bot.mp (he ▸ (mem_zpowers x))))⟩)

private theorem normal_solvable_of_component_residual
    {H : Type*} [Group H] [Finite H] (L C : Subgroup H) [C.Normal]
    (hL : L.IsCComponent) (hres : solvableResidual H = L) (hne : ¬ L ≤ C) :
    Group.IsSolvable C := by
  have hb : solvableResidual C = ⊥ := by
    by_contra hb
    let D := (solvableResidual C).map C.subtype
    have hD : D ≠ ⊥ := by
      intro hd
      exact hb (((solvableResidual C).map_eq_bot_iff_of_injective C.subtype_injective).mp hd)
    have hDL : D ≤ L := (map_solvableResidual_le C.subtype).trans_eq hres
    have hsub : D.IsSubnormal :=
      (inferInstance : (solvableResidual C).Normal).isSubnormal.trans'
        (inferInstance : C.Normal).isSubnormal
    exact hne ((hL.minimal D hDL hD (Group.IsPerfect.map C.subtype) hsub).trans
      (map_subtype_le _))
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := C)
  exact ⟨n, hn.trans hb⟩

private theorem solvable_of_nontrivial_L_action {G : Type*} [Group G] [Finite G] (p : ℕ) (L T : Subgroup G)
    (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hn : ∃ l : L, xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l ≠ 1) :
    Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T)) := by
  let H := L ⊔ T
  let C := twoSectionCentralizer (XiP p L) H
  let L' := L.subgroupOf H
  let C' := C.subgroupOf H
  have hCH : C ≤ H := twoSectionCentralizer_le _ _
  let : C'.Normal := normal_subgroupOf_of_le_normalizer
    (twoSectionCentralizer_normalized _ _
      ((sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_XiP p L)))
  have hres : solvableResidual H = L' := by
    let := mem_L_isPerfect hL
    have hh := localNormalizer_residual_eq L T (⊥ : Subgroup G) hL.2.1 hT
    unfold normalizerResidual at hh
    rw [(⊥ : Subgroup G).normalizer_eq_top, inf_top_eq, inf_top_eq,
      solvableResidual_eq_top (G := L), ← MonoidHom.range_eq_map, range_subtype] at hh
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)]
    exact hh
  have hnLC : ¬ L' ≤ C' := by
    intro hLC
    obtain ⟨l, hl⟩ := hn
    apply hl
    have hk := sectionCentralizer_le_action_ker p L T hT
      (hLC (show (⟨l, (show L ≤ H from le_sup_left) l.property⟩ : H) ∈ L' from l.property))
    have hh := congrArg (quotientAut (frattini (XiQuotient (XiP p L)))) hk
    have he : xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer) l =
        (quotientAut (frattini (XiQuotient (XiP p L))))
          (localXiQuotientAction p L T hT ⟨l, (show L ≤ H from le_sup_left) l.property⟩) := by
      apply MulEquiv.ext
      intro z
      induction z using QuotientGroup.induction_on with | H z =>
        induction z using QuotientGroup.induction_on with | H x =>
          rfl
    exact he.trans (by simpa only [map_one] using hh)
  let : Group.IsSolvable C' := normal_solvable_of_component_residual L' C' hL.1 hres hnLC
  exact Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hCH).toMonoidHom)
    (subgroupOfEquivOfLe hCH).surjective

universe u
/-- The section centralizer is solvable from the earlier A.3 structure and
irreducibility of the original N_L(P)-action. No residual input is used. -/
theorem sectionCentralizer_solvable_of_source
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L : Subgroup G} (hL : L ∈ LStar G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (P : Sylow p (XiP p L))
    (hirr : ∀ A : Subgroup
        (((P : Subgroup (XiP p L)).map (XiP p L).subtype) ⧸
          frattini ((P : Subgroup (XiP p L)).map (XiP p L).subtype)),
      (∀ g : (L ⊓ normalizer
          ((P : Subgroup (XiP p L)).map (XiP p L).subtype : Set G) : Subgroup G),
        ∀ a ∈ A, frattiniConjugationAction _ _ inf_le_right g a ∈ A) →
        A = ⊥ ∨ A = ⊤) :
    Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T)) := by
  have hT := radicalLocal_invariant_of_A38 hA38 hL.1 hQ hn
  have hshape := (XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn ho hd).2
  let e := RadicalActions.sylowFrattiniEquiv ho hshape.isPGroup P
  have hnc : ¬ IsCyclic
      (((P : Subgroup (XiP p L)).map (XiP p L).subtype) ⧸
        frattini ((P : Subgroup (XiP p L)).map (XiP p L).subtype)) := by
    intro hc
    let := hc
    exact OddInvolutionFrattini.noncyclic_frattini_quotient hshape.not_isCyclic
      (isCyclic_of_surjective e.toMonoidHom e.surjective)
  obtain ⟨g, hg⟩ := action_nontrivial hnc (frattiniConjugationAction _ _ inf_le_right) hirr
  apply solvable_of_nontrivial_L_action p L T hL.1 hT
  refine ⟨⟨g, g.property.1⟩, ?_⟩
  intro he
  apply hg
  apply MulEquiv.ext
  intro v
  apply e.injective
  rw [RadicalActions.sylowFrattiniEquiv_equivariant
    (XiP_invariant p L.le_normalizer), he]
  rfl

end CFSG.Quasithin.Chapter1.RadicalNormalizers
