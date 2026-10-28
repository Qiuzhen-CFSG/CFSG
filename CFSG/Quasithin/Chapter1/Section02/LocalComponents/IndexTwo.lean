module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Projections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Noncentral

/-!
# The conditional index-two local-component lemma

Distinct C-components intersect inside the solvable radical, so a
nonsolvable subgroup has at most one containing C-component. If its
commutator with `R ∩ K` is nonsolvable, A.3.3(7), with its full universal
statement retained as an input, forces containment in `K`. The normalizer
bound comes from membership in the component layer, itself deduced from
the earlier A.3.9 generation result with its SQTK hypotheses.

The noncentral-commutator construction selects an actual nontrivial
coordinate modulo the solvable radical and lifts its Sylow subgroup
inside an ambient C-component. Intersecting with `R` preserves the
index-at-most-two bound. A.1.38 and the proved odd-order theorem exclude
the resulting commutator being solvable, discharging the witness needed
for containment and uniqueness.

The final deduction of Aschbacher–Smith, Lemma 1.2.5, printed p.505
(1 March 2004 manuscript), retains only the universally quantified earlier
results A.3.3(7) and A.3.9(1), with their full hypotheses, and the SQTK
property of the quotient by the two-core. The Chapter 1 assembly owner
must supply these inputs from the source's ambient QTKE setup. No
containing component, projection witness, or extra parity premise is assumed.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.IndexTwo
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Distinct C-components intersect only inside the ambient solvable radical. -/
theorem cComponent_inf_le_radical {K J : Subgroup G}
    (hK : K.IsCComponent) (hJ : J.IsCComponent) (hne : K ≠ J) :
    K ⊓ J ≤ solvableRadical G := by
  let q := QuotientGroup.mk' (solvableRadical G)
  have hfree := solvableRadical_quotient_solvableRadical (G := G)
  have hk := hK.map_quotient (solvableRadical G)
  have hj := hJ.map_quotient (solvableRadical G)
  have hcomm := hk.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hfree hj
    (fun he => hne (hK.eq_of_map_quotient_eq hJ _ he))
  have hcenter := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hfree hk.subnormal
  intro x hx
  have hxk : q x ∈ K.map q := mem_map.mpr ⟨x, hx.1, rfl⟩
  have hxj : q x ∈ J.map q := mem_map.mpr ⟨x, hx.2, rfl⟩
  have hz : (⟨q x, hxk⟩ : K.map q) ∈ center (K.map q) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((commutator_eq_bot_iff_le_centralizer.mp hcomm y.2) (q x) hxj).symm
  have he : (⟨q x, hxk⟩ : K.map q) = 1 := mem_bot.mp (hcenter ▸ hz)
  exact (QuotientGroup.eq_one_iff (N := solvableRadical G) x).mp
    (congrArg Subtype.val he)

/-- A nonsolvable subgroup lies in at most one C-component. -/
theorem cComponent_unique_over_nonsolvable {B K J : Subgroup G}
    (hB : ¬ Group.IsSolvable B) (hK : K.IsCComponent) (hJ : J.IsCComponent)
    (hBK : B ≤ K) (hBJ : B ≤ J) : K = J := by
  by_contra hne
  have hBR := (le_inf hBK hBJ).trans (cComponent_inf_le_radical hK hJ hne)
  exact hB (Group.isSolvable_of_isSolvable_injective (inclusion_injective hBR))

/-- A.3.3(7) turns a nonsolvable component commutator into containment. -/
theorem local_component_le_of_nonsolvable_commutator
    (hA337 : ∀ (X : Type u) [Group X] [Finite X] (B D : Subgroup X),
      B.IsCComponent → ⁅B, D⁆ ≤ solvableRadical X ∨
        ⁅B, D⁆ = ⨆ d : D, B.map (MulAut.conj (d : X)).toMonoidHom)
    {L R K : Subgroup G} (hL : L ∈ Chapter1.L G R) (hK : K.IsCComponent)
    (hLLayer : L ≤ cComponentLayer G)
    (hn : ¬ Group.IsSolvable (⁅L, R ⊓ K⁆ : Subgroup G)) : L ≤ K := by
  let M := L ⊔ R
  let B := L.subgroupOf M
  let D := (R ⊓ K).subgroupOf M
  have hDM : R ⊓ K ≤ M := inf_le_left.trans le_sup_right
  have he : ⁅B, D⁆.map M.subtype = ⁅L, R ⊓ K⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le hDM]
  have hBD : B ≤ ⁅B, D⁆ := by
    rcases hA337 M B D hL.1 with hs | hc
    · have hsol : Group.IsSolvable (⁅B, D⁆ : Subgroup M) :=
        Group.isSolvable_of_isSolvable_injective (inclusion_injective hs)
      let := hsol
      have hm : Group.IsSolvable (⁅B, D⁆.map M.subtype) :=
        Group.isSolvable_of_surjective (M.subtype.subgroupMap_surjective ⁅B, D⁆)
      exact (hn (he ▸ hm)).elim
    · rw [hc]
      exact le_iSup_conjugates B D
  have hLC : L ≤ ⁅L, R ⊓ K⁆ := by
    have hm := map_mono (f := M.subtype) hBD
    rwa [map_subgroupOf_eq_of_le le_sup_left, he] at hm
  exact hLC.trans ((commutator_mono le_rfl inf_le_right).trans
    (le_normalizer_iff_commutator_le_right.mp
      (hLLayer.trans (cComponentLayer_le_normalizer hK))))

/-- Final containment and uniqueness once the nonsolvable commutator is constructed. -/
theorem unique_containment_of_nonsolvable_component_commutator
    (hA337 : ∀ (X : Type u) [Group X] [Finite X] (B D : Subgroup X),
      B.IsCComponent → ⁅B, D⁆ ≤ solvableRadical X ∨
        ⁅B, D⁆ = ⨆ d : D, B.map (MulAut.conj (d : X)).toMonoidHom)
    {L R : Subgroup G} (hL : L ∈ Chapter1.L G R)
    (hLLayer : L ≤ cComponentLayer G)
    (hcomm : ∃ K : Subgroup G, K.IsCComponent ∧
      ¬ Group.IsSolvable (⁅L, R ⊓ K⁆ : Subgroup G)) :
    ∃! K : Subgroup G, K.IsCComponent ∧ L ≤ K := by
  obtain ⟨K, hK, hn⟩ := hcomm
  have hLK := local_component_le_of_nonsolvable_commutator hA337 hL hK hLLayer hn
  refine ⟨K, ⟨hK, hLK⟩, ?_⟩
  intro J hJ
  exact cComponent_unique_over_nonsolvable (mem_L_not_isSolvable hL)
    hJ.1 hK hJ.2 hLK

/-- The full earlier SQTK generation theorem places a local component in the layer. -/
theorem local_component_le_layer_of_A_3_9 {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    {L R : Subgroup G} (hL : L ∈ Chapter1.L G R) : L ≤ cComponentLayer G := by
  let := mem_L_isPerfect hL
  rw [proposition_1_2_1_one_of_A_3_9 hA39 hQ]
  exact le_solvableResidual_of_isPerfect L

end CFSG.Quasithin.Chapter1.Section02.IndexTwo

namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Lemma 1.2.5, conditional on the universal earlier results A.3.3(7) and
A.3.9(1) and the SQTK quotient hypothesis supplied by the Chapter 1 setup.
The projection, Sylow-index, commutator, containment, and uniqueness steps
are all discharged here. -/
theorem lemma_1_2_5_of_A_3_3_7_of_A_3_9 {𝒦 : GroupClass.{u}}
    (hA337 : ∀ (X : Type u) [Group X] [Finite X] (B D : Subgroup X),
      B.IsCComponent → ⁅B, D⁆ ≤ solvableRadical X ∨
        ⁅B, D⁆ = ⨆ d : D, B.map (MulAut.conj (d : X)).toMonoidHom)
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {R L : Subgroup G}
    (hRS : R ≤ S) (hidx : R.relIndex (S : Subgroup G) = 2)
    (hL : L ∈ Chapter1.L G R) :
    ∃! K : Subgroup G, K.IsCComponent ∧ L ≤ K := by
  have hLayer := IndexTwo.local_component_le_layer_of_A_3_9 hA39 hQ hL
  exact IndexTwo.unique_containment_of_nonsolvable_component_commutator hA337 hL hLayer
    (IndexTwo.exists_nonsolvable_component_commutator_of_index_two S hRS hidx hL hLayer)

end CFSG.Quasithin.Chapter1.Section02
