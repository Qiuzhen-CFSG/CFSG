module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.PGroupCore

/-!
# The split-torus elementary eight in ternary G₂

For the elementary eight constructed in `TernaryLocals`, its ambient centralizer
is itself, and its actual normalizer has a self-centralizing intrinsic two-core.
The normalizer order divides 1344, so its three-part has order at most three.
However, its order is at most 512 and therefore is **not** 1344. This embedding
cannot supply the elementary-eight local configuration described in §I.4(G2).

Here `u = e₀ + e₇`, `v = e₁ + e₆`, and `w = e₃ - e₄` generate the octonion
algebra. The three elementary generators act diagonally on the Cayley basis
formed from `1, u, v, uv, w, uw, vw, (uv)w`. Of its sixteen signed vectors,
eight have norm one and eight have norm two. Every normalizer element sends
each of `u, v, w` into its eight-element norm class. Their images determine the
automorphism, giving the bound `8³`. An element of the centralizer preserves
each character line, and its three signs are realized by the elementary group.
Normality inside the normalizer then gives the intrinsic core assertion.

The finite checks use kernel reduction. The longest-element eigenvalue first
expresses the last four coordinates in terms of the first four, reducing the
candidate check to 243 cases. No enumeration of the full ambient group is used.

Source context: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 (repeated as Theorem 0.1.1 on pp.481–482),
and §I.4(G2), printed p.417. The latter describes an elementary-eight local
with full automizer L₃(2); it does not identify the present embedding with it.
The concrete multiplication, torus and Weyl maps are from the ATLAS port,
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors, under the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

open Atlas.SplitOctonion
namespace Atlas.G2.TernaryLocals.ElementaryEight
set_option maxRecDepth 100000

private def u : Carrier (ZMod 3) := ![1,0,0,0,0,0,0,1]
private def v : Carrier (ZMod 3) := ![0,1,0,0,0,0,1,0]
private def w : Carrier (ZMod 3) := ![0,0,0,1,-1,0,0,0]
private def generators : Fin 3 → Carrier (ZMod 3) := ![u,v,w]

private theorem ext_generators {g h : Model (ZMod 3)}
    (he : ∀ i, g.val (generators i) = h.val (generators i)) : g = h := by
  have hu : g.val u = h.val u := he 0
  have hv : g.val v = h.val v := he 1
  have hw : g.val w = h.val w := he 2
  have hb : ∀ i : Fin 8, (basisVector i : Carrier (ZMod 3)) =
      ![mul u w - u, -(v + mul v w), mul u v + mul (mul u v) w,
        -(unit + w), w - unit, mul u v - mul (mul u v) w,
        mul v w - v, -(u + mul u w)] i := by decide +kernel
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext
  intro i
  simp only [LinearEquiv.coe_coe]
  rw [hb]
  fin_cases i <;> simp [hu, hv, hw, automorphism_mul]

private def actions : Fin 3 → Carrier (ZMod 3) → Carrier (ZMod 3) :=
  ![fun x => ![-x 0,x 1,-x 2,x 3,x 4,-x 5,x 6,-x 7],
    fun x => ![x 0,-x 1,-x 2,x 3,x 4,-x 5,-x 6,x 7],
    fun x => ![x 7,x 6,x 5,x 4,x 3,x 2,x 1,x 0]]

private def testEigenvector (x : Carrier (ZMod 3)) : Prop :=
  ∀ i, ∃ r : ZMod 3, actions i x = r • x
private instance (x : Carrier (ZMod 3)) : Decidable (testEigenvector x) :=
  inferInstanceAs (Decidable (∀ i, ∃ r : ZMod 3, actions i x = r • x))

private def candidates : Finset (Carrier (ZMod 3)) :=
  {unit, -unit, u, -u, v, -v, mul u v, -(mul u v),
    w, -w, mul u w, -(mul u w), mul v w, -(mul v w),
    mul (mul u v) w, -(mul (mul u v) w)}

private def candidatesOfNorm (r : ZMod 3) : Finset (Carrier (ZMod 3)) :=
  candidates.filter (fun x => norm x = r)

private def reflected (r x0 x1 x2 x3 : ZMod 3) : Carrier (ZMod 3) :=
  ![x0,x1,x2,x3,r*x3,r*x2,r*x1,r*x0]

private theorem reflection_form {x : Carrier (ZMod 3)} {r : ZMod 3}
    (hr : actions 2 x = r • x) : x = reflected r (x 0) (x 1) (x 2) (x 3) := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact congrFun hr 3
  · exact congrFun hr 2
  · exact congrFun hr 1
  · exact congrFun hr 0

set_option maxHeartbeats 4000000 in
private theorem reflected_mem_candidates : ∀ (r x0 x1 x2 x3 : ZMod 3),
    testEigenvector (reflected r x0 x1 x2 x3) →
      norm (reflected r x0 x1 x2 x3) ≠ 0 →
        reflected r x0 x1 x2 x3 ∈ candidates := by decide +kernel

private theorem eigen_mem_candidates {x : Carrier (ZMod 3)} (hx : testEigenvector x)
    (hn : norm x ≠ 0) : x ∈ candidates := by
  obtain ⟨r, hr⟩ := hx 2
  have he := reflection_form hr
  rw [he] at hx hn ⊢
  exact reflected_mem_candidates r _ _ _ _ hx hn

private def generatingParameters : Fin 3 → Parameters :=
  ![Multiplicative.ofAdd ![1,0,0], Multiplicative.ofAdd ![0,1,0],
    Multiplicative.ofAdd ![0,0,1]]

private def actionsLinear (i : Fin 3) : Carrier (ZMod 3) →ₗ[ZMod 3] Carrier (ZMod 3) where
  toFun := actions i
  map_add' x y := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [actions, neg_add_rev, add_comm]
  map_smul' r x := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp [actions]

private theorem actions_eq (i : Fin 3) (x : Carrier (ZMod 3)) :
    actions i x = (embedding (generatingParameters i)).val x := by
  have he : actionsLinear i = (embedding (generatingParameters i)).val.toLinearMap := by
    apply linearMap_ext
    intro k
    apply funext
    exact (by decide +kernel : ∀ i k j,
      actions i (basisVector k) j =
        (embedding (generatingParameters i)).val (basisVector k) j) i k
  exact congrArg (fun f : Carrier (ZMod 3) →ₗ[ZMod 3] Carrier (ZMod 3) => f x) he

private def simultaneousEigenvector (x : Carrier (ZMod 3)) : Prop :=
  ∀ a : Parameters, ∃ r : ZMod 3, (embedding a).val x = r • x

private instance (x : Carrier (ZMod 3)) : Decidable (simultaneousEigenvector x) :=
  inferInstanceAs (Decidable (∀ a : Parameters, ∃ r : ZMod 3, (embedding a).val x = r • x))

private theorem eigen_generators : ∀ i, simultaneousEigenvector (generators i) := by decide +kernel

private theorem eigen_image (g : localSubgroup true) {x : Carrier (ZMod 3)}
    (hx : simultaneousEigenvector x) : simultaneousEigenvector (g.val.val x) := by
  intro a
  have hmem : g.val⁻¹ * embedding a * g.val ∈ elementary := by
    have hg : g.val⁻¹ ∈ Subgroup.normalizer (elementary : Set (Model (ZMod 3))) :=
      (localSubgroup true).inv_mem g.property
    have hm := (Subgroup.mem_normalizer_iff.mp hg (embedding a)).mp
      (show embedding a ∈ elementary from ⟨a, rfl⟩)
    rwa [inv_inv] at hm
  obtain ⟨b, hb⟩ := hmem
  obtain ⟨r, hr⟩ := hx b
  refine ⟨r, ?_⟩
  have he : embedding a * g.val = g.val * embedding b := by rw [hb]; group
  calc
    (embedding a).val (g.val.val x) = g.val.val ((embedding b).val x) :=
      congrArg (fun t : Model (ZMod 3) => t.val x) he
    _ = r • g.val.val x := by rw [hr, map_smul]

private theorem eigen_test {x : Carrier (ZMod 3)} (hx : simultaneousEigenvector x) :
    testEigenvector x := by
  intro i
  rw [actions_eq]
  exact hx (generatingParameters i)

private def generatorNorm : Fin 3 → ZMod 3 := ![1,1,2]

private theorem norm_generators : ∀ i, norm (generators i) = generatorNorm i := by decide +kernel

private theorem generatorNorm_ne_zero : ∀ i, generatorNorm i ≠ 0 := by decide +kernel

private theorem card_candidatesOfNorm : ∀ i,
    (candidatesOfNorm (generatorNorm i)).card = 8 := by decide +kernel

private def normalizerImages (g : localSubgroup true) :
    ∀ i : Fin 3, ↥(candidatesOfNorm (generatorNorm i)) := fun i =>
  ⟨g.val.val (generators i), Finset.mem_filter.mpr ⟨
    eigen_mem_candidates (eigen_test (eigen_image g (eigen_generators i))) (by
      rw [automorphism_norm, norm_generators]
      exact generatorNorm_ne_zero i),
    (automorphism_norm g.val (generators i)).trans (norm_generators i)⟩⟩

private theorem normalizerImages_injective : Function.Injective normalizerImages := by
  intro g h he
  apply Subtype.ext
  apply ext_generators
  intro i
  exact congrArg Subtype.val (congrFun he i)

/-- The split-torus/Weyl elementary eight has a normalizer of order at most 512. -/
public theorem card_localSubgroup_true_le_512 : Nat.card (localSubgroup true) ≤ 512 := by
  have hc := Nat.card_le_card_of_injective normalizerImages normalizerImages_injective
  have he : Nat.card (∀ i : Fin 3, ↥(candidatesOfNorm (generatorNorm i))) = 512 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    simp only [Fintype.card_coe, card_candidatesOfNorm]
    decide
  exact hc.trans_eq he

/-- This particular elementary-eight embedding does not have the order-1344 normalizer. -/
public theorem card_localSubgroup_true_ne_1344 : Nat.card (localSubgroup true) ≠ 1344 := by
  have := card_localSubgroup_true_le_512
  omega

private def characters : Fin 3 → Fin 3 → ZMod 3 :=
  ![![-1,1,1], ![1,-1,1], ![1,1,-1]]

private theorem generator_characters : ∀ i j,
    actions j (generators i) = characters i j • generators i := by decide +kernel

private theorem candidate_same_character : ∀ (x : candidates) (i : Fin 3),
    (∀ j, actions j x.val = characters i j • x.val) →
    norm x.val = generatorNorm i →
    ∃ r : ZMod 3, r ≠ 0 ∧ x.val = r • generators i := by decide +kernel

private theorem signs_realized : ∀ r : Fin 3 → ZMod 3, (∀ i, r i ≠ 0) →
    ∃ a : Parameters, ∀ i, (embedding a).val (generators i) = r i • generators i := by
  decide +kernel

private theorem centralizer_generator_character (g : Model (ZMod 3))
    (hg : g ∈ Subgroup.centralizer (elementary : Set (Model (ZMod 3)))) (i j : Fin 3) :
    actions j (g.val (generators i)) = characters i j • g.val (generators i) := by
  have hc : embedding (generatingParameters j) * g = g * embedding (generatingParameters j) :=
    Subgroup.mem_centralizer_iff.mp hg _ ⟨generatingParameters j, rfl⟩
  have he : (embedding (generatingParameters j)).val (generators i) =
      characters i j • generators i := by
    rw [← actions_eq]
    exact generator_characters i j
  rw [actions_eq]
  calc
    (embedding (generatingParameters j)).val (g.val (generators i)) =
        g.val ((embedding (generatingParameters j)).val (generators i)) :=
      congrArg (fun t : Model (ZMod 3) => t.val (generators i)) hc
    _ = characters i j • g.val (generators i) := by rw [he, map_smul]

/-- The ambient centralizer of the embedded elementary eight is exactly itself. -/
public theorem centralizer_elementary :
    Subgroup.centralizer (elementary : Set (Model (ZMod 3))) = elementary := by
  apply le_antisymm
  · intro g hg
    have hs (i : Fin 3) : ∃ r : ZMod 3, r ≠ 0 ∧ g.val (generators i) = r • generators i := by
      have hx : testEigenvector (g.val (generators i)) :=
        fun j => ⟨characters i j, centralizer_generator_character g hg i j⟩
      have hn : norm (g.val (generators i)) = generatorNorm i :=
        (automorphism_norm g _).trans (norm_generators i)
      have hm := eigen_mem_candidates hx (hn ▸ generatorNorm_ne_zero i)
      exact candidate_same_character ⟨g.val (generators i), hm⟩ i
        (centralizer_generator_character g hg i) hn
    choose r hr he using hs
    obtain ⟨a, ha⟩ := signs_realized r hr
    exact ⟨a, ext_generators (fun i => (ha i).trans (he i).symm)⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    change embedding b * embedding a = embedding a * embedding b
    rw [← map_mul, ← map_mul, mul_comm]

/-- The actual normalizer has a self-centralizing intrinsic two-core. -/
public theorem localSubgroup_true_centralizer_pCore :
    Subgroup.centralizer (pCore 2 (localSubgroup true) : Set (localSubgroup true)) ≤
      pCore 2 (localSubgroup true) := by
  let E := elementary.subgroupOf (localSubgroup true)
  have hEN : elementary ≤ localSubgroup true := elementary.le_normalizer
  have hnormal : E.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 elementary).comap_subtype
  have hcore : E ≤ pCore 2 (localSubgroup true) := le_sSup ⟨hnormal, hp⟩
  intro g hg
  apply hcore
  change g.val ∈ elementary
  rw [← centralizer_elementary]
  intro a ha
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg
    ⟨a, hEN ha⟩ (hcore ha))

/-- The normalizer order divides eight times the full elementary-eight automorphism order. -/
public theorem card_localSubgroup_true_dvd_1344 : Nat.card (localSubgroup true) ∣ 1344 := by
  have hker : Nat.card elementary.normalizerMonoidHom.ker = 8 := by
    rw [Subgroup.normalizerMonoidHom_ker, centralizer_elementary]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe elementary.le_normalizer).toEquiv).trans
      card_elementary
  have hd : Nat.card elementary.normalizerMonoidHom.range ∣ 168 := by
    rw [← card_mulAut_of_elementary_eight elementary card_elementary]
    exact elementary.normalizerMonoidHom.range.card_subgroup_dvd_card
  change Nat.card (Subgroup.normalizer (elementary : Set (Model (ZMod 3)))) ∣ 1344
  rw [← elementary.normalizerMonoidHom.ker.card_mul_index, Subgroup.index_ker, hker]
  exact Nat.mul_dvd_mul_left 8 hd

/-- The order bound needed for the local three-rank calculation. -/
public theorem three_cube_not_dvd_card_localSubgroup_true :
    ¬ 3^3 ∣ Nat.card (localSubgroup true) := by
  intro h
  exact (by decide : ¬ 3^3 ∣ 1344) (h.trans card_localSubgroup_true_dvd_1344)

end Atlas.G2.TernaryLocals.ElementaryEight
