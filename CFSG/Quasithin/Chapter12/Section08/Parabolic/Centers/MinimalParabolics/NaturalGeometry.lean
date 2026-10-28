module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.Residuals
public import Theory.GroupTheory.PResidual.MapInjectivity
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Natural-action transport for the ordered parabolic induction

The actual conjugation homomorphism from LT to Aut(V) identifies every
ordered parabolic with the preimage of its marked flag stabilizer. Its
kernel is C_LT(V), and the original ambient Sylow maps to a Sylow subgroup
fixing the same flag. The full-action input is precisely 12.8.3(1) in the
source dimensions three through five.

Ordinary stabilizer generation lifts because the kernel belongs to every
stabilizer. Residual conjugate generation requires more: the kernel fixes
each flag member, so it normalizes every initial residual join. With the
source two-core kernel identity, equality of natural images detects these
two-perfect subgroups. This preserves right conjugation and the embedded
O² convention throughout.

The final adapter supplies exactly the two geometric premises of
`center_centralized_of_ordered_generation`. Intrinsic natural-image
generation and the successive conjugators are still explicit obligations;
this module does not assert their existence or the completed book theorem.
The terminal-residual adapter applies the existing residual-generation
consumer without an additional terminal-equality premise.

Source: Aschbacher–Smith, Hypothesis 12.8.1 and Lemma 12.8.3(1), printed
pp.849–850, and the induction in Lemma 12.8.10(5), printed p.854
(PDF p.871), combined manuscript of 1 March 2004, `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Conjugation by the actual group LT on the seed V. -/
def naturalFlagAction (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) : (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (sup_le hL (by
    simpa only [F.last] using F.invariant n)))

@[simp] theorem naturalFlagAction_apply (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
    ((F.naturalFlagAction L hL x) v : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

/-- Stabilizer of the original flag member in the full automorphism group. -/
def naturalFlagStabilizer (F : InvariantFlag T V n) (i : ℕ) : Subgroup (MulAut V) where
  carrier := {a | ∀ v : V, (a v : G) ∈ F.Vi i ↔ (v : G) ∈ F.Vi i}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro a b ha hb v
    exact (ha (b v)).trans (hb v)
  inv_mem' := by
    intro a ha v
    simpa using (ha (a⁻¹ v)).symm

/-- The full natural minimal parabolic with the j-th marked cut deleted. -/
def naturalOrderedParabolic (F : InvariantFlag T V n) (j : ℕ) : Subgroup (MulAut V) :=
  ⨅ i : ℕ, ⨅ (_ : 1 ≤ i ∧ i < n ∧ i ≠ j), F.naturalFlagStabilizer i

/-- The initial join of natural-image two-residuals. -/
def naturalInitialResiduals (F : InvariantFlag T V n) (i : ℕ) : Subgroup (MulAut V) :=
  ⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j ≤ i),
    (pResidual 2 (F.naturalOrderedParabolic j)).map (F.naturalOrderedParabolic j).subtype

theorem naturalFlagAction_surjective (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) :
    Function.Surjective (F.naturalFlagAction L hL) := by
  intro a
  obtain ⟨x, hx, he⟩ := hfull a
  refine ⟨⟨x, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hx⟩, ?_⟩
  ext v
  exact he v

theorem naturalFlagAction_mem_stabilizer (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (i : ℕ) (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    F.naturalFlagAction L hL x ∈ F.naturalFlagStabilizer i ↔ (x : G) ∈ F.Gi i := by
  constructor
  · intro h
    rw [Gi, mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact (h ⟨a, F.le_seed i ha⟩).mpr ha
    · intro ha
      have hi := (F.naturalFlagStabilizer i).inv_mem h
      have hv := (hi ⟨_, F.le_seed i ha⟩).mpr ha
      change (((F.naturalFlagAction L hL x)⁻¹) ⟨_, F.le_seed i ha⟩ : G) ∈ F.Vi i at hv
      rw [← map_inv, naturalFlagAction_apply] at hv
      simpa [mul_assoc] using hv
  · intro h v
    exact (mem_normalizer_iff.mp h _).symm

theorem naturalOrderedParabolic_comap (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (j : ℕ) :
    (F.naturalOrderedParabolic j).comap (F.naturalFlagAction L hL) =
      (F.orderedParabolic L j).subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext x
  simp only [mem_comap, naturalOrderedParabolic, mem_iInf,
    naturalFlagAction_mem_stabilizer, mem_subgroupOf, orderedParabolic, mem_inf]
  exact (and_iff_right x.property).symm

theorem naturalOrderedParabolic_image (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) (j : ℕ) :
    ((F.orderedParabolic L j).subgroupOf (L ⊔ (T : Subgroup G))).map
      (F.naturalFlagAction L hL) = F.naturalOrderedParabolic j := by
  rw [← F.naturalOrderedParabolic_comap L hL j,
    map_comap_eq_self_of_surjective (F.naturalFlagAction_surjective L hL hfull)]

theorem naturalFlagAction_ker (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) :
    (F.naturalFlagAction L hL).ker =
      (centralizer (V : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext x
  change F.naturalFlagAction L hL x = 1 ↔ (x : G) ∈ centralizer (V : Set G)
  rw [mem_centralizer_iff]
  constructor
  · intro hx v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) hx
    change (x : G) * v * (x : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    ext v
    change (x : G) * (v : G) * (x : G)⁻¹ = v
    rw [← hx v v.property, mul_inv_cancel_right]

theorem naturalFlagAction_ker_isPGroup (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) : IsPGroup 2 (F.naturalFlagAction L hL).ker := by
  let K := (F.naturalFlagAction L hL).ker
  have he : K.map (L ⊔ (T : Subgroup G)).subtype = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [show K = _ from F.naturalFlagAction_ker L hL, subgroupOf_map_subtype, inf_comm, hcore]
  have hp : IsPGroup 2 (K.map (L ⊔ (T : Subgroup G)).subtype) := by
    rw [he]
    exact pCore_isPGroup.map _
  exact hp.of_equiv (K.equivMapOfInjective _ (L ⊔ (T : Subgroup G)).subtype_injective).symm

/-- Generation in the full natural action lifts to the literal ambient stabilizers.
The action kernel belongs to each stabilizer, so no residual hypothesis is used. -/
theorem orderedParabolic_generation_of_natural (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hgen : (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.naturalOrderedParabolic j) = ⊤) :
    (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.orderedParabolic L j) = L ⊔ (T : Subgroup G) := by
  let R := L ⊔ (T : Subgroup G)
  let f := F.naturalFlagAction L hL
  let A : Subgroup R := ⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n),
    (F.orderedParabolic L j).subgroupOf R
  have hA : A.map f = ⊤ := by
    simpa only [A, Subgroup.map_iSup, f, R, F.naturalOrderedParabolic_image L hL hfull] using hgen
  have hk : f.ker ≤ A := by
    suffices hp : f.ker ≤ (F.orderedParabolic L 1).subgroupOf R from
      hp.trans (le_iSup_of_le 1 (le_iSup_of_le (show 1 ≤ 1 ∧ 1 < n by omega) le_rfl))
    rw [← F.naturalOrderedParabolic_comap L hL 1]
    intro x hx
    change f x ∈ F.naturalOrderedParabolic 1
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have htop : A = ⊤ := by
    have he := congrArg (fun B : Subgroup (MulAut V) => B.comap f) hA
    simpa only [comap_map_eq, sup_eq_left.mpr hk, comap_top] using he
  have he := congrArg (fun B : Subgroup R => B.map R.subtype) htop
  have hP (j : ℕ) : F.orderedParabolic L j ≤ R := inf_le_left
  simpa only [A, Subgroup.map_iSup, map_subgroupOf_eq_of_le (hP _),
    ← MonoidHom.range_eq_map, range_subtype] using he

/-- Applying the ordinary generation transport supplies the terminal equality
required by the center induction, using the original Sylow T. -/
theorem initialResiduals_terminal_of_natural_generation (F : InvariantFlag T V n)
    [Finite G] (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hperfect : IsPPerfect 2 L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hgen : (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.naturalOrderedParabolic j) = ⊤) :
    F.initialResiduals L (n - 1) = L :=
  F.initialResiduals_terminal_of_parabolic_generation hn L hperfect hTL
    (F.orderedParabolic_generation_of_natural hn L hL hfull hgen)

private theorem initialResiduals_le_join (F : InvariantFlag T V n) (L : Subgroup G) (i : ℕ) :
    F.initialResiduals L i ≤ L ⊔ (T : Subgroup G) := by
  apply iSup_le; intro j; apply iSup_le; intro _
  exact (F.orderedResidual_le L j).trans inf_le_left

private theorem orderedResidual_subgroupOf (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (j : ℕ) :
    (F.orderedResidual L j).subgroupOf (L ⊔ (T : Subgroup G)) =
      (pResidual 2 ((F.orderedParabolic L j).subgroupOf (L ⊔ (T : Subgroup G)))).map
        ((F.orderedParabolic L j).subgroupOf (L ⊔ (T : Subgroup G))).subtype := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.orderedResidual_le L j).trans inf_le_left),
    map_embedded_pResidual, map_subgroupOf_eq_of_le (show F.orderedParabolic L j ≤
      L ⊔ (T : Subgroup G) from inf_le_left)]
  rfl

private theorem initialResiduals_subgroupOf (F : InvariantFlag T V n) (L : Subgroup G) (i : ℕ) :
    (F.initialResiduals L i).subgroupOf (L ⊔ (T : Subgroup G)) =
      ⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j ≤ i),
        (F.orderedResidual L j).subgroupOf (L ⊔ (T : Subgroup G)) := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  have hr (j : ℕ) : F.orderedResidual L j ≤ L ⊔ (T : Subgroup G) :=
    (F.orderedResidual_le L j).trans inf_le_left
  rw [map_subgroupOf_eq_of_le (F.initialResiduals_le_join L i)]
  simp only [Subgroup.map_iSup, map_subgroupOf_eq_of_le (hr _), initialResiduals]

/-- The natural initial residuals are exactly the images of the source H_i.
Every residual is taken inside its literal stabilizer before embedding. -/
theorem naturalInitialResiduals_image (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) (i : ℕ) :
    ((F.initialResiduals L i).subgroupOf (L ⊔ (T : Subgroup G))).map
      (F.naturalFlagAction L hL) = F.naturalInitialResiduals i := by
  rw [F.initialResiduals_subgroupOf]
  simp only [Subgroup.map_iSup, F.orderedResidual_subgroupOf, map_embedded_pResidual,
    naturalInitialResiduals]
  apply iSup_congr; intro j; apply iSup_congr; intro _
  rw [F.naturalOrderedParabolic_image L hL hfull]

/-- The kernel fixes the entire marked flag and hence normalizes every H_i.
This is stronger than merely saying that the kernel is normal in LT. -/
theorem naturalFlagAction_ker_normalizes (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) (i : ℕ) :
    (F.naturalFlagAction L hL).ker ≤
      normalizer ((F.initialResiduals L i).subgroupOf (L ⊔ (T : Subgroup G)) :
        Set (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  let R := L ⊔ (T : Subgroup G)
  let f := F.naturalFlagAction L hL
  have hn (j : ℕ) : f.ker ≤ normalizer
      ((F.orderedResidual L j).subgroupOf R : Set R) := by
    rw [F.orderedResidual_subgroupOf]
    have hP : f.ker ≤ (F.orderedParabolic L j).subgroupOf R := by
      rw [← F.naturalOrderedParabolic_comap L hL j]
      intro x hx
      change f x ∈ F.naturalOrderedParabolic j
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _
    exact hP.trans (((F.orderedParabolic L j).subgroupOf R).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))
  rw [F.initialResiduals_subgroupOf]
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  simp only [Subgroup.map_iSup]
  apply iSup_congr; intro j; apply iSup_congr; intro _
  exact mem_normalizer_iff_map_conj_eq.mp (hn j hx)

private theorem map_right_conjugate {A B : Type*} [Group A] [Group B]
    (f : A →* B) (U : Subgroup A) (k : A) :
    (conjugate U k).map f = conjugate (U.map f) (f k) := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp

private theorem perfect_sup {A : Type*} [Group A] (U W : Subgroup A)
    (hU : IsPPerfect 2 U) (hW : IsPPerfect 2 W) : IsPPerfect 2 (U ⊔ W : Subgroup A) := by
  let D := U ⊔ W
  have hh (J : Subgroup A) (hJ : IsPPerfect 2 J) (hJD : J ≤ D) :
      J ≤ (pResidual 2 D).map D.subtype := by
    have hp : IsPPerfect 2 (J.subgroupOf D) := hJ.of_surjective
      (subgroupOfEquivOfLe hJD).symm.toMonoidHom (subgroupOfEquivOfLe hJD).symm.surjective
    have he := map_mono (f := D.subtype) (le_pResidual_of_isPPerfect (J.subgroupOf D) hp)
    rwa [map_subgroupOf_eq_of_le hJD] at he
  apply (pResidual_eq_top_iff 2 D).mp
  apply map_injective D.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact le_antisymm (map_subtype_le _) (sup_le (hh U hU le_sup_left) (hh W hW le_sup_right))

private theorem perfect_conjugate {A : Type*} [Group A] (U : Subgroup A)
    (hU : IsPPerfect 2 U) (k : A) : IsPPerfect 2 (conjugate U k) :=
  hU.of_surjective ((MulAut.conj k⁻¹).toMonoidHom.subgroupMap U)
    ((MulAut.conj k⁻¹).toMonoidHom.subgroupMap_surjective U)

private theorem kernel_normalizes_conjugate {A B : Type*} [Group A] [Group B]
    (f : A →* B) (U : Subgroup A) (hn : f.ker ≤ normalizer (U : Set A)) (k : A) :
    f.ker ≤ normalizer (conjugate U k : Set A) := by
  have he : f.ker.map (MulAut.conj k⁻¹).toMonoidHom = f.ker :=
    mem_normalizer_iff_map_conj_eq.mp (show k⁻¹ ∈ normalizer (f.ker : Set A) by
      rw [normalizer_eq_top]; trivial)
  rw [conjugate, ← he]
  exact (map_mono hn).trans (le_normalizer_map _)

/-- Lift a genuine natural-image conjugator through the actual two-group kernel.
Both generated groups are two-perfect and normalized by the kernel, so equality
of images gives equality in LT and then in the original ambient group. -/
theorem initialResiduals_conjugator_of_natural (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (j : ℕ) (a : MulAut V) (ha : a ∈ F.naturalOrderedParabolic (j + 1))
    (he : F.naturalInitialResiduals (j + 1) =
      F.naturalInitialResiduals j ⊔ conjugate (F.naturalInitialResiduals j) a) :
    ∃ k ∈ F.orderedParabolic L (j + 1), F.initialResiduals L (j + 1) =
      F.initialResiduals L j ⊔ conjugate (F.initialResiduals L j) k := by
  let R := L ⊔ (T : Subgroup G)
  let f := F.naturalFlagAction L hL
  let A := (F.initialResiduals L j).subgroupOf R
  let B := (F.initialResiduals L (j + 1)).subgroupOf R
  obtain ⟨k, hk⟩ := F.naturalFlagAction_surjective L hL hfull a
  have hkP : (k : G) ∈ F.orderedParabolic L (j + 1) := by
    have hm : k ∈ (F.naturalOrderedParabolic (j + 1)).comap f := by
      change f k ∈ F.naturalOrderedParabolic (j + 1)
      simpa only [f, hk] using ha
    rwa [F.naturalOrderedParabolic_comap] at hm
  have hp (i : ℕ) : IsPPerfect 2 ((F.initialResiduals L i).subgroupOf R) :=
    (F.initialResiduals_isPPerfect L i).of_surjective
      (subgroupOfEquivOfLe (F.initialResiduals_le_join L i)).symm.toMonoidHom
      (subgroupOfEquivOfLe (F.initialResiduals_le_join L i)).symm.surjective
  have hnA : f.ker ≤ normalizer (A : Set R) := F.naturalFlagAction_ker_normalizes L hL j
  have hnD : f.ker ≤ normalizer ((A ⊔ conjugate A k : Subgroup R) : Set R) :=
    (le_inf hnA (kernel_normalizes_conjugate f A hnA k)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hBD : B = A ⊔ conjugate A k := by
    apply eq_of_map_eq_map_of_isPPerfect f (hp (j + 1))
      (perfect_sup A (conjugate A k) (hp j) (perfect_conjugate A (hp j) k))
      (F.naturalFlagAction_ker_isPGroup L hL hcore)
      (F.naturalFlagAction_ker_normalizes L hL (j + 1)) hnD
    simpa only [B, A, R, Subgroup.map_sup, map_right_conjugate, f,
      F.naturalInitialResiduals_image L hL hfull, hk] using he
  refine ⟨k, hkP, ?_⟩
  have hout := congrArg (fun D : Subgroup R => D.map R.subtype) hBD
  simpa only [B, A, R, Subgroup.map_sup, map_right_conjugate,
    map_subgroupOf_eq_of_le (F.initialResiduals_le_join L (j + 1)),
    map_subgroupOf_eq_of_le (F.initialResiduals_le_join L j), Subgroup.subtype_apply] using hout

/-- The image of the original ambient Sylow under the genuine action. -/
noncomputable def naturalFlagSylow (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) :
    Sylow 2 (MulAut V) :=
  (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).mapSurjective
    (F.naturalFlagAction_surjective L hL hfull)

/-- The marked image Sylow fixes each original flag member. -/
theorem naturalFlagSylow_le_stabilizer (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) (i : ℕ) :
    (F.naturalFlagSylow L hL hfull : Subgroup (MulAut V)) ≤ F.naturalFlagStabilizer i := by
  change ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map
    (F.naturalFlagAction L hL) ≤ _
  rintro a ⟨x, hx, rfl⟩
  exact (F.naturalFlagAction_mem_stabilizer L hL i x).mpr (F.invariant i hx)

/-- The two ambient obligations in the center induction follow from their
natural-image versions. Their unconditional geometric proofs are separate. -/
theorem ordered_generation_of_natural_geometry (F : InvariantFlag T V n) [Finite G]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hgen : (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.naturalOrderedParabolic j) = ⊤)
    (hstep : ∀ j, 1 ≤ j → j + 1 < n → ∃ a ∈ F.naturalOrderedParabolic (j + 1),
      F.naturalInitialResiduals (j + 1) =
        F.naturalInitialResiduals j ⊔ conjugate (F.naturalInitialResiduals j) a) :
    (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.orderedParabolic L j) = L ⊔ (T : Subgroup G) ∧
      ∀ j, 1 ≤ j → j + 1 < n → ∃ k ∈ F.orderedParabolic L (j + 1),
        F.initialResiduals L (j + 1) =
          F.initialResiduals L j ⊔ conjugate (F.initialResiduals L j) k := by
  refine ⟨F.orderedParabolic_generation_of_natural hn L hL hfull hgen, ?_⟩
  intro j hj hjn
  obtain ⟨a, ha, he⟩ := hstep j hj hjn
  exact F.initialResiduals_conjugator_of_natural L hL hfull hcore j a ha he

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
