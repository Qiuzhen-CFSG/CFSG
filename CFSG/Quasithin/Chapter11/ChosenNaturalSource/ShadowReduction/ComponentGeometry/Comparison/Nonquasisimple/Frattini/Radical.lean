module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Preparation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.PrimeContainment
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The radical in the actual point-component join

The normalizer core of R₁ in KzR₁ is R₁. Indeed T normalizes this
relative normalizer; adjoining T lets us compare its two-core with
O₂(L₁T), using the common Sylow subgroup. This does not assert that a
radical two-subgroup of a solvable group is Sylow.

The prime-field signalizer theorem also places R₁ in O∞(KzR₁), by
restricting the solvable radical of KzT along the literal inclusion.
The original rank-one seed model makes O∞(L₁T) = O₂(L₁T). Restriction
then identifies T ∩ O∞(KzT) with R₁, proving the required Sylow assertion.
The prime-field model remains an input of the separate complete-catalogue
reduction. The Frattini product is treated separately.

Source: Aschbacher--Smith, 11.4.2, printed p.777, using the signalizer
argument in the proof of 11.4.1(3), printed p.776.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The source's KR₁, where K is the point component, not the line component. -/
@[expose] def pointRadicalJoin (E : Closure.Geometry D) : Subgroup G := E.Kz ⊔ E.R₁

private theorem radical_le_sylow : E.R₁ ≤ (T : Subgroup G) := by
  change (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

private theorem seedJoin_normalizes_radical :
    E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
  (E.L₁ ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

private theorem sylow_normalizes_point (h : EarlierGeometry E) :
    (T : Subgroup G) ≤ normalizer (E.Kz : Set G) :=
  h.sylow_le_pointCentralizer.trans (le_normalizer_conjugateSpanBy _ _)

/-- The actual relative normalizer has two-core R₁. No radicality is assumed. -/
theorem relative_normalizer_core (h : EarlierGeometry E) :
    (pointRadicalJoin E ⊓ normalizer (E.R₁ : Set G)).pCoreIn 2 = E.R₁ := by
  let J := pointRadicalJoin E
  let N := J ⊓ normalizer (E.R₁ : Set G)
  have hTR : (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
    le_sup_right.trans seedJoin_normalizes_radical
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf (sylow_normalizes_point h) hTR).trans
      (normalizer_inf_normalizer_le_normalizer_sup E.Kz E.R₁)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf hTJ (hTR.trans (normalizer (E.R₁ : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hAN : E.L₁ ≤ N := le_inf
    ((le_conjugateSpanBy _ _).trans le_sup_left)
    (le_sup_left.trans seedJoin_normalizes_radical)
  apply le_antisymm
  · exact (pCoreIn_mono_of_normalizes (show N ≤ N ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le N.le_normalizer hTN)).trans
      (pCoreIn_le_of_sylow_le T le_sup_right (sup_le_sup_right hAN _))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      (le_inf le_sup_right E.R₁.le_normalizer) inf_le_right

/-- Relative radicality in KR₁ follows from the flag, including nontriviality. -/
theorem ofFlag_relative_radical (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) :
    IsPRadical 2 ((ofFlag S f X z H).R₁.subgroupOf
      (pointRadicalJoin (ofFlag S f X z H))) := by
  let E := ofFlag S f X z H
  let J := pointRadicalJoin E
  have hRJ : E.R₁ ≤ J := le_sup_right
  have hRne : E.R₁ ≠ ⊥ := by
    intro he
    apply f.V_ne_bot 0
    exact le_bot_iff.mp (he ▸ ((show f.Vi 0 ≤ V from E.V₁_le).trans
      (f.seed_le_Ri S 0)))
  refine ⟨?_, ?_⟩
  · intro he
    change E.R₁.subgroupOf J = ⊥ at he
    apply hRne
    simpa only [map_subgroupOf_eq_of_le hRJ, Subgroup.map_bot] using
      congrArg (map J.subtype) he
  · change (normalizer (E.R₁.subgroupOf J : Set J)).pCoreIn 2 = E.R₁.subgroupOf J
    apply map_injective J.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      ← subgroupOf_normalizer_eq hRJ, subgroupOf_map_subtype, inf_comm,
      relative_normalizer_core h, map_subgroupOf_eq_of_le hRJ]

private theorem radical_comap_le {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (i : A →* B) (hi : Function.Injective i) :
    (solvableRadical B).comap i ≤ solvableRadical A := by
  let C := (solvableRadical B).comap i
  let j : C →* solvableRadical B := (i.comp C.subtype).codRestrict _ (fun x => x.property)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun a b hab => Subtype.ext (hi (congrArg Subtype.val hab)))
  exact le_solvableRadical C inferInstance inferInstance

/-- The prime-field model gives containment in the solvable radical of KR₁
itself. The restriction is along the original inclusion into KT. -/
theorem ofFlag_le_join_radical_of_prime_model (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL
      ((ofFlag S f X z H).Kz ⧸ solvableRadical (ofFlag S f X z H).Kz) 2 p) :
    (ofFlag S f X z H).R₁ ≤
      (solvableRadical (pointRadicalJoin (ofFlag S f X z H))).map
        (pointRadicalJoin (ofFlag S f X z H)).subtype := by
  let E := ofFlag S f X z H
  let J := pointRadicalJoin E
  let W := E.Kz ⊔ (T : Subgroup G)
  have hJW : J ≤ W := sup_le le_sup_left (radical_le_sylow.trans le_sup_right)
  have hr := Radical.ofFlag_radical_containment_of_prime_model S f X z H E.Kz hA
    (le_conjugateSpanBy _ _) (sylow_normalizes_point h) hp hm
  intro r hrR
  have hrJ : r ∈ J := mem_sup_right hrR
  obtain ⟨rW, hrW, he⟩ := hr hrR
  change rW ∈ solvableRadical W at hrW
  have hi : inclusion hJW (⟨r, hrJ⟩ : J) ∈ solvableRadical W := by
    simpa only [show rW = inclusion hJW (⟨r, hrJ⟩ : J) from Subtype.ext he] using hrW
  exact mem_map_of_mem J.subtype
    (radical_comap_le (inclusion hJW) (inclusion_injective hJW) hi)

/-- The earlier rank-one seed model identifies the radical of L₁T. -/
theorem ofFlag_seedJoin_radical_eq_core (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree)) :
    solvableRadical (f.Li 0 ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (f.Li 0 ⊔ (T : Subgroup G) : Subgroup G) := by
  let A := f.Li 0
  let Y := A ⊔ (T : Subgroup G)
  let B := A.subgroupOf Y
  let e : B ≃* A := subgroupOfEquivOfLe (show A ≤ Y from le_sup_left)
  let : Group.IsPerfect A := LocalGeometry.localResidual_perfect _
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hF]
      exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
        (Nat.pow_le_pow_right (by decide) S.nonbinary))
  let : IsSimpleGroup (A ⧸ pCore 2 A) := a.isSimpleGroup
  have hA : solvableRadical A = pCore 2 A :=
    radical_eq_core_of_perfect_simple_core_quotient
  have hB : solvableRadical B = pCore 2 B := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_solvableRadical_equiv e, pCore_map_iso, hA]
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer (f.sylow_normalizes_Li 0))
  have hq : IsPGroup 2 (Y ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B ((T : Subgroup G).subgroupOf Y)
      T.isPGroup'.comap_subtype (by
        rw [← subgroupOf_sup (show A ≤ Y from le_sup_left)
          (show (T : Subgroup G) ≤ Y from le_sup_right), subgroupOf_self])
  exact radical_eq_core_of_normal_two_quotient B
    (hB ▸ (pCore_isPGroup : IsPGroup 2 (pCore 2 B))) hq

/-- R₁ is Sylow in the radical of the literal point-component join.
The proof uses both actual quotient models, not an assumed Sylow assertion. -/
theorem ofFlag_sylow_in_join_radical_of_prime_model (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL
      ((ofFlag S f X z H).Kz ⧸ solvableRadical (ofFlag S f X z H).Kz) 2 p) :
    Chapter1.IsSylowIn 2 (ofFlag S f X z H).R₁
      ((solvableRadical (pointRadicalJoin (ofFlag S f X z H))).map
        (pointRadicalJoin (ofFlag S f X z H)).subtype) := by
  let E := ofFlag S f X z H
  let W := E.Kz ⊔ (T : Subgroup G)
  let Y := E.L₁ ⊔ (T : Subgroup G)
  let J := pointRadicalJoin E
  let B := (solvableRadical W).map W.subtype
  have hYW : Y ≤ W := sup_le_sup_right (le_conjugateSpanBy _ _) _
  have hr : E.R₁ ≤ B := Radical.ofFlag_radical_containment_of_prime_model S f X z H
    E.Kz hA (le_conjugateSpanBy _ _) (sylow_normalizes_point h) hp hm
  have hint : (T : Subgroup G) ⊓ B = E.R₁ := by
    apply le_antisymm ?_ (le_inf radical_le_sylow hr)
    rintro r ⟨hrT, rW, hrW, he⟩
    have hrY : r ∈ Y := mem_sup_right hrT
    have hi : inclusion hYW (⟨r, hrY⟩ : Y) ∈ solvableRadical W := by
      change rW ∈ solvableRadical W at hrW
      exact (show rW = inclusion hYW (⟨r, hrY⟩ : Y) from Subtype.ext he) ▸ hrW
    have hri := radical_comap_le (inclusion hYW) (inclusion_injective hYW) hi
    have hy : solvableRadical Y = pCore 2 Y := ofFlag_seedJoin_radical_eq_core S f hseed
    rw [hy] at hri
    exact mem_map_of_mem Y.subtype hri
  have hn : (B.subgroupOf W).Normal := by
    change ((solvableRadical W).map W.subtype |>.comap W.subtype).Normal
    rw [comap_map_eq_self_of_injective W.subtype_injective]
    infer_instance
  have ht : Chapter1.IsSylowIn 2 (T : Subgroup G) W :=
    ⟨T.subtype le_sup_right, by
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ W from le_sup_right)]⟩
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal ht
    (show B ≤ W from map_subtype_le _) hn.isSubnormal
  rw [hint] at hs
  have hJW : J ≤ W := sup_le le_sup_left (radical_le_sylow.trans le_sup_right)
  have hWJ : W ≤ normalizer (J : Set G) := by
    have hKJ : E.Kz ≤ normalizer (J : Set G) := le_sup_left.trans J.le_normalizer
    have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
      (le_inf (sylow_normalizes_point h)
        (le_sup_right.trans seedJoin_normalizes_radical)).trans
        (normalizer_inf_normalizer_le_normalizer_sup E.Kz E.R₁)
    exact sup_le hKJ hTJ
  let : (J.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hWJ
  have hrad : (solvableRadical J).map J.subtype ≤ B := by
    let e : (J.subgroupOf W) ≃* J := subgroupOfEquivOfLe hJW
    have hm' := map_mono (f := W.subtype)
      (map_solvableRadical_subtype_le_of_normal (J.subgroupOf W))
    rw [map_map] at hm'
    rw [← map_solvableRadical_equiv e, map_map]
    exact hm'
  exact hs.restrict (ofFlag_le_join_radical_of_prime_model S f X z H h hA hp hm) hrad

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
