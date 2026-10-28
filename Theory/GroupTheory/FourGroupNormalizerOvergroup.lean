module
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.ElementaryAbelian.Basic
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# Enlarging normalizers of Sylow-normal four-groups

This criterion separates finite model geometry from a maximality argument.
For each normal elementary subgroup of order four in a Sylow two-subgroup,
its full ambient normalizer must lie strictly in a subgroup whose generalized
Fitting subgroup is its two-core. A subgroup maximal for that intrinsic
characteristic-two property therefore cannot normalize the four-group.

The criterion is transported along actual group isomorphisms, including the
normalizer, Sylow condition, and intrinsic generalized Fitting subgroup.
It does not assert the existence of the geometric overgroups in any model.
The motivating source use is Aschbacher--Smith, combined manuscript of
1 March 2004, the sporadic paragraph of 15.3.43, printed p.1140.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Every normal four-group of a Sylow two-subgroup has a normalizer contained
strictly in a subgroup of characteristic two. -/
def FourNormalizerOvergroups (G : Type*) [Group G] : Prop :=
  ∀ (P : Sylow 2 G) (V : Subgroup G), V ≤ (P : Subgroup G) →
    (P : Subgroup G) ≤ normalizer (V : Set G) →
    IsElementaryAbelian 2 V → Nat.card V = 4 →
    ∃ H : Subgroup G, normalizer (V : Set G) < H ∧
      generalizedFitting H = pCore 2 H

/-- The corresponding restricted calculation when the four-group is known to
lie in a specified normal component. This does not require four-groups outside
that component to satisfy the same geometry. -/
def FourNormalizerOvergroupsIn (B : Subgroup G) : Prop :=
  ∀ (P : Sylow 2 G) (V : Subgroup G), V ≤ B → V ≤ (P : Subgroup G) →
    (P : Subgroup G) ≤ normalizer (V : Set G) →
    IsElementaryAbelian 2 V → Nat.card V = 4 →
    ∃ H : Subgroup G, normalizer (V : Set G) < H ∧
      generalizedFitting H = pCore 2 H

/-- The intrinsic characteristic-two condition respects actual group isomorphisms. -/
theorem characteristicTwo_of_mulEquiv (e : G ≃* H)
    (h : generalizedFitting H = pCore 2 H) :
    generalizedFitting G = pCore 2 G := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_generalizedFitting_equiv, pCore_map_iso, h]

/-- Pull back an actual strict characteristic-two overgroup of the full normalizer. -/
theorem normalizer_overgroup_of_mulEquiv (e : G ≃* H) (V : Subgroup G)
    (h : ∃ D : Subgroup H, normalizer (V.map e.toMonoidHom : Set H) < D ∧
      generalizedFitting D = pCore 2 D) :
    ∃ E : Subgroup G, normalizer (V : Set G) < E ∧
      generalizedFitting E = pCore 2 E := by
  obtain ⟨D, hVD, hD⟩ := h
  let E := D.map e.symm.toMonoidHom
  have hNV : (normalizer (V.map e.toMonoidHom : Set H)).map e.symm.toMonoidHom =
      normalizer (V : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  refine ⟨E, ?_, ?_⟩
  · have hs := (MulEquiv.mapSubgroup e.symm).strictMono hVD
    change (normalizer (V.map e.toMonoidHom : Set H)).map e.symm.toMonoidHom < E at hs
    rwa [hNV] at hs
  · exact characteristicTwo_of_mulEquiv (e.symm.subgroupMap D).symm hD

/-- The normalizer-overgroup criterion is independent of the chosen carrier. -/
theorem FourNormalizerOvergroups.of_mulEquiv [Finite G] (e : G ≃* H)
    (h : FourNormalizerOvergroups H) : FourNormalizerOvergroups G := by
  intro P V hVP hPV hV hcard
  let W := V.map e.toMonoidHom
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hVQ : W ≤ (Q : Subgroup H) := Subgroup.map_mono hVP
  have hQW : (Q : Subgroup H) ≤ normalizer (W : Set H) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPV
  let : IsElementaryAbelian 2 V := hV
  have hW : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hWcard : Nat.card W = 4 :=
    (Subgroup.card_map_of_injective e.injective).trans hcard
  exact normalizer_overgroup_of_mulEquiv e V (h Q W hVQ hQW hW hWcard)

/-- Transport the component marking together with the full normalizer geometry. -/
theorem FourNormalizerOvergroupsIn.of_mulEquiv [Finite G] (e : G ≃* H)
    (B : Subgroup G) (h : FourNormalizerOvergroupsIn (B.map e.toMonoidHom)) :
    FourNormalizerOvergroupsIn B := by
  intro P V hVB hVP hPV hV hcard
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hVQ : V.map e.toMonoidHom ≤ (Q : Subgroup H) := Subgroup.map_mono hVP
  have hQV : (Q : Subgroup H) ≤ normalizer (V.map e.toMonoidHom : Set H) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPV
  let : IsElementaryAbelian 2 V := hV
  exact normalizer_overgroup_of_mulEquiv e V (h Q _ (Subgroup.map_mono hVB) hVQ hQV
    (IsElementaryAbelian.map e.toMonoidHom)
    ((Subgroup.card_map_of_injective e.injective).trans hcard))

/-- A calculation in one actual Sylow subgroup suffices; conjugacy supplies
coverage for every Sylow subgroup. -/
theorem FourNormalizerOvergroups.of_fixed_sylow [Finite G] (P : Sylow 2 G)
    (h : ∀ V : Subgroup G, V ≤ (P : Subgroup G) →
      (P : Subgroup G) ≤ normalizer (V : Set G) →
      IsElementaryAbelian 2 V → Nat.card V = 4 →
      ∃ D : Subgroup G, normalizer (V : Set G) < D ∧
        generalizedFitting D = pCore 2 D) : FourNormalizerOvergroups G := by
  intro Q V hVQ hQV hV hc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  let e := MulAut.conj g
  have hQP : (Q : Subgroup G).map e.toMonoidHom = (P : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hWP : V.map e.toMonoidHom ≤ (P : Subgroup G) :=
    hQP ▸ Subgroup.map_mono hVQ
  have hPW : (P : Subgroup G) ≤ normalizer (V.map e.toMonoidHom : Set G) := by
    rw [← hQP, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hQV
  let : IsElementaryAbelian 2 V := hV
  exact normalizer_overgroup_of_mulEquiv e V (h _ hWP hPW
    (IsElementaryAbelian.map e.toMonoidHom)
    ((Subgroup.card_map_of_injective e.injective).trans hc))

/-- A maximal characteristic-two subgroup cannot normalize such a four-group. -/
theorem FourNormalizerOvergroups.not_normalized_by_maximal
    (h : FourNormalizerOvergroups G) (P : Sylow 2 G) (M V : Subgroup G)
    (hPM : (P : Subgroup G) ≤ M)
    (hVP : V ≤ (P : Subgroup G))
    (hVM : M ≤ normalizer (V : Set G))
    (hV : IsElementaryAbelian 2 V) (hcard : Nat.card V = 4)
    (hmax : Maximal (fun X : Subgroup G => generalizedFitting X = pCore 2 X) M) :
    False := by
  obtain ⟨D, hD, hf⟩ := h P V hVP (hPM.trans hVM) hV hcard
  exact hD.not_ge ((hmax.2 hf (hVM.trans hD.le)).trans hVM)

end Theory.GroupTheory
