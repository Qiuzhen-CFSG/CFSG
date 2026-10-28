module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.InnerGeometry
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The solvable subgroup in the recognized larger-field parabolic

The literal O₂,Φ quotient makes Y₊S solvable, by the already proved
Frattini extension argument. Restrict that group to the normal component.
It contains the component's actual Sylow intersection and lies in the
recognized proper parabolic. Thus a model calculation about solvable Sylow
overgroups in that parabolic gives containment in the intrinsic normalizer.

`ParabolicSolvableControl` is an explicit intermediate obligation, not a
recognition assertion or a source theorem. It retains the proper overgroup
of the actual Sylow normalizer, so its producers can use parabolic geometry.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41(2),
printed p.1138, and the first paragraph of the final proof of 15.3.35, p.1139.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel

/-- A solvable Sylow overgroup lying in a proper overgroup of its normalizer
normalizes that Sylow subgroup. Each model must establish this separately. -/
def ParabolicSolvableControl (D : Type*) [Group D] : Prop :=
  ∀ (U : Sylow 2 D) (P H : Subgroup D),
    normalizer (U : Set D) ≤ P → P ≠ ⊤ → H ≤ P →
    Group.IsSolvable H → (U : Subgroup D) ≤ H →
    H ≤ normalizer (U : Set D)

/-- Transport the intrinsic control through an actual group equivalence. -/
theorem control_of_mulEquiv {D E : Type*} [Group D] [Finite D] [Group E]
    (e : D ≃* E) (h : ParabolicSolvableControl E) : ParabolicSolvableControl D := by
  intro U P H hNP hP hHP hsol hUH
  let V := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hN : normalizer (V : Set E) ≤ P.map e.toMonoidHom := by
    change normalizer (((U : Subgroup D).map e.toMonoidHom) : Set E) ≤ _
    rw [← map_equiv_normalizer_eq]
    exact map_mono hNP
  have hproper : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using he
  let : Group.IsSolvable H := hsol
  have hsol' : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hh := h V (P.map e.toMonoidHom) (H.map e.toMonoidHom)
    hN hproper (map_mono hHP) hsol' (map_mono hUH)
  change H.map e.toMonoidHom ≤
    normalizer (((U : Subgroup D).map e.toMonoidHom) : Set E) at hh
  rw [← map_equiv_normalizer_eq] at hh
  exact (map_le_map_iff_of_injective e.injective).mp hh

variable {G : Type*} [Group G] [Finite G]

/-- Restrict the source solvable join and its Sylow subgroup to the normal
component, apply the model calculation inside the recognized parabolic, and
map its intrinsic normalizer back to the ambient group. -/
theorem local_borel_containment {D M Y T : Subgroup G} [D.Normal]
    (c : LocalConfiguration D M Y T)
    (hp : MaximalInvariantParabolic D T (M ⊓ D))
    (hc : ParabolicSolvableControl D) : Y ≤ sylowBorel D T := by
  obtain ⟨U, hU⟩ := c.sylow
  obtain ⟨V, hV⟩ := U.exists_subgroupOf_eq_of_normal D
  rw [hU] at hV
  let H := (Y ⊔ T).subgroupOf D
  let P := (M ⊓ D).subgroupOf D
  let : Group.IsSolvable (Y ⊔ T : Subgroup G) :=
    BinaryRecognition.InnerGeometry.shadow_join_solvable c.shadow
  let j : H →* (Y ⊔ T : Subgroup G) :=
    (D.subtype.comp H.subtype).codRestrict _ (fun x => x.property)
  have hj : Function.Injective j := fun x y he =>
    Subtype.ext (Subtype.ext (congrArg (fun x : (Y ⊔ T : Subgroup G) => (x : G)) he))
  have hsol : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective hj
  have hNP : normalizer (V : Set D) ≤ P := by
    change normalizer ((V : Subgroup D) : Set D) ≤ P
    rw [hV]
    intro x hx
    exact hp.contains_borel ⟨x, hx, rfl⟩
  have hproper : P ≠ ⊤ := by
    intro he
    exact hp.proper.not_ge (subgroupOf_eq_top.mp he)
  have hHP : H ≤ P := by
    intro x hx
    exact ⟨(sup_le (c.yplus_le.trans inf_le_left) c.sylow_le) hx, x.property⟩
  have hVH : (V : Subgroup D) ≤ H := by
    rw [hV]
    exact comap_mono le_sup_right
  have hHN := hc V P H hNP hproper hHP hsol hVH
  intro y hy
  have hyD : y ∈ D := (c.yplus_le hy).2
  have hyH : (⟨y, hyD⟩ : D) ∈ H := (show Y ≤ Y ⊔ T from le_sup_left) hy
  have hyN := hHN hyH
  change (⟨y, hyD⟩ : D) ∈ normalizer ((V : Subgroup D) : Set D) at hyN
  rw [hV] at hyN
  exact ⟨⟨y, hyD⟩, hyN, rfl⟩

/-- The reduction specialized to the actual centralizer quotient. The
source action has already served to select the model; no extra action
condition is needed for this subgroup-containment step. -/
theorem quotient_borel_containment {L MI Yplus S : Subgroup G} [L.Normal]
    (d : Setup L MI Yplus S) (hp : QuotientParabolic L MI S)
    (hc : ParabolicSolvableControl (centralizerQuotientComponent L)) :
    Yplus.map (centralizerQuotientMap L) ≤
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) := by
  let : (centralizerQuotientComponent L).Normal :=
    (inferInstance : L.Normal).map (centralizerQuotientMap L)
      (QuotientGroup.mk'_surjective _)
  exact local_borel_containment d.quotient_local hp hc

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.LargerFieldBorel
