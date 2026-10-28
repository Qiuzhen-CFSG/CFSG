module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallNormality
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ContainedNormalizer
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.ComponentNormalizerDescent

/-!
# Removing the small component from the actual radical normalizer

For a PSL3(3) or M11 component D, the source rank argument gives D normal in H.
In the contained-normalizer branch the radical R is the quaternion core of
M∩D or its original Sylow subgroup, so N_H(R) contains that Sylow subgroup.
The intersection D∩N_H(R) lies in the actual GL2(3) intersection and is
solvable. The proved finite two-Schreier theorem makes every component of
the replacement centralize D, and normal-centralizer descent makes it a
component of H distinct from D.

Source: Aschbacher--Smith 2.5.3(4), printed p.553. The actual earlier GL2(3)
intersection isomorphism and chosen Sylow position are retained; no Schreier,
rank, radical or component-descent premise remains.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- Components of the literal replacement survive in H and centralize the
removed small component; in particular none is that removed component. -/
theorem small_normalizer_components_remain
    (hG : IsQuasithin G) (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M)
    (P : Sylow 2 D) (hPM : (P : Subgroup D) ≤ (M.subgroupOf H).subgroupOf D)
    (hQP : ((twoCore HU).subgroupOf H).subgroupOf D ≤ (P : Subgroup D))
    (e : ((M.subgroupOf H).subgroupOf D) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    let R := D ⊓ (twoCore HU).subgroupOf H
    let X := normalizer (R : Set H)
    ∀ K : Subgroup X, IsComponent X K →
      IsComponent H (K.map X.subtype) ∧ K.map X.subtype ≤ centralizer (D : Set H) ∧
        K.map X.subtype ≠ D := by
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  let R₀ := Q.subgroupOf D
  let I := (M.subgroupOf H).subgroupOf D
  let X := normalizer (R : Set H)
  let : D.Normal := small_component_normal hG hH D hD hm
  have hRmap : R₀.map D.subtype = R := by rw [subgroupOf_map_subtype, inf_comm]
  have hPnorm : (P : Subgroup D) ≤ normalizer (R₀ : Set D) := by
    rcases contained_component_radical_eq_core_or_sylow hpair hsat D hD hinside
        P hPM hQP e with he | he
    · change R₀ = I.pCoreIn 2 at he
      rw [he]
      exact hPM.trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
    · change R₀ = (P : Subgroup D) at he
      rw [he]
      exact (P : Subgroup D).le_normalizer
  have hPX : (P : Subgroup D).map D.subtype ≤ X := by
    have hh := (map_mono (f := D.subtype) hPnorm).trans (R₀.le_normalizer_map D.subtype)
    rwa [hRmap] at hh
  have hCX : centralizer (D : Set H) ≤ X :=
    (centralizer_le (show R ≤ D from inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hsolv : Group.IsSolvable (D.subgroupOf X) := by
    let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
      Matrix.GeneralLinearGroup.three_isSolvable
    let : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    let f : D.subgroupOf X →* I := {
      toFun x := ⟨⟨x.val.val, x.property⟩,
        hinside (mem_map_of_mem H.subtype ⟨x.property, x.val.property⟩)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply Group.isSolvable_of_isSolvable_injective (f := f)
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : I => ((z : D) : H)) he
  change ∀ K : Subgroup X, IsComponent X K →
    IsComponent H (K.map X.subtype) ∧ K.map X.subtype ≤ centralizer (D : Set H) ∧
      K.map X.subtype ≠ D
  intro K hK
  obtain ⟨hc, hz⟩ := component_descends_of_normal_component_solvable_intersection
    (ChapterI.SylowAutomorphisms.hasTwoSchreier H) hD P X hCX hPX hsolv K hK
  refine ⟨hc, hz, ?_⟩
  intro he
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isMulCommutative D
    (le_centralizer_iff_isMulCommutative.mp (he ▸ hz))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
