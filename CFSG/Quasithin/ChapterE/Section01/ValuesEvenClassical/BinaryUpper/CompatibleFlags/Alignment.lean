module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.Flags
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.LocalStructure
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Sylow alignment and normalization of the binary flag pair

Sylow conjugacy chooses a model equivalence carrying the intersection of the
ambient Sylow subgroup with the normal binary linear group to the full
coordinate flag. The matrix entry definition of `Flags` is identified with
the existing geometric flag stabilizer on the same standard basis.

The proved inner/graph automorphism theorem then handles the entire ambient
Sylow action. Inner automorphisms preserving the full flag fix its cuts;
graph-times-inner automorphisms reverse them. Thus both diagram-stable
flags are normalized, and their joins with the Sylow subgroup meet the
original normal group in exactly the transported parabolics.

Solvability transfers from a model flag to its ambient join. The model Levi
calculations and the middle dimension-five quotient are separate obligations;
no local solvability or generalized-Fitting conclusion is assumed here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214, citing Aschbacher (1982), Lemma 4.7.
The reused binary automorphism theorem formalizes GLS3, Theorem 2.5.12.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
open Representation.OneCohomology.SLHigherNatural

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper

/-- The full coordinate flag is the actual binary unitriangular subgroup. -/
theorem parabolic_empty_eq_unipotent (d : ℕ) :
    parabolic d ∅ = Theory.SpecificGroups.LinearSylowNormalizers.unipotent d (ZMod 2) := by
  ext g
  rw [Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent,
    Theory.SpecificGroups.LinearSylowNormalizers.mem_borel]
  constructor
  · intro h
    have hu : g.val.IsUpperTriangular := by
      intro i j hji
      exact (h (j.val + 1) ⟨by omega, by have := i.isLt; change j.val < i.val at hji; omega,
        Set.notMem_empty _⟩).1 i j (by change j.val < i.val at hji; omega) (by omega)
    refine ⟨hu, fun i => ?_⟩
    have hd := g.property
    rw [Matrix.det_of_isUpperTriangular hu] at hd
    have hp : (∏ j, g.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _
      (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i))
  · intro h
    have hg : g ∈ Theory.SpecificGroups.LinearSylowNormalizers.borel d (ZMod 2) :=
      (Theory.SpecificGroups.LinearSylowNormalizers.mem_borel d (ZMod 2) g).mpr h.1
    have hi := (Theory.SpecificGroups.LinearSylowNormalizers.borel d (ZMod 2)).inv_mem hg
    rw [Theory.SpecificGroups.LinearSylowNormalizers.mem_borel] at hi
    intro k hk
    exact ⟨fun i j hik hjk => h.1 (show j < i from by change j.val < i.val; omega),
      fun i j hik hjk => hi (show j < i from by change j.val < i.val; omega)⟩

/-- The unitriangular Sylow subgroup in the same projective model as the flags. -/
noncomputable def projectiveSylow (d : ℕ) (hd : 0 < d) : Sylow 2 (PSL d) :=
  (Theory.SpecificGroups.LinearSylowNormalizers.standardSylow d (ZMod 2) hd).mapSurjective
    (f := (binaryProjectiveEquiv d).toMonoidHom) (binaryProjectiveEquiv d).surjective

/-- The chosen projective Sylow has exactly the full coordinate flag as its carrier. -/
theorem coe_projectiveSylow (d : ℕ) (hd : 0 < d) :
    (projectiveSylow d hd : Subgroup (PSL d)) = projectiveParabolic d ∅ := by
  change ((Theory.SpecificGroups.LinearSylowNormalizers.standardSylow d (ZMod 2) hd :
    Subgroup (SL d)).map (binaryProjectiveEquiv d).toMonoidHom) = _
  rw [Theory.SpecificGroups.LinearSylowNormalizers.coe_standardSylow]
  rw [projectiveParabolic, parabolic_empty_eq_unipotent]

/-- The given model equivalence sends the intrinsic intersection with `T` to the full coordinate flag. This condition contains no local-structure conclusion. -/
def SylowAligned {G : Type*} [Group G] {d : ℕ} (L T : Subgroup G)
    (e : L ≃* PSL d) : Prop :=
  (T.subgroupOf L).map e.toMonoidHom = projectiveParabolic d ∅

/-- Sylow conjugacy supplies a coordinate marking aligned with the ambient Sylow intersection. Only normality of the embedded group is needed. -/
theorem exists_sylowAligned {G : Type*} [Group G] [Finite G] {d : ℕ}
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* PSL d) (hd : 0 < d) :
    ∃ e' : L ≃* PSL d, SylowAligned L (T : Subgroup G) e' := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal L
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL d) U (projectiveSylow d hd)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  change ((T : Subgroup G).subgroupOf L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [← hS, ← Subgroup.map_map]
  change (g • U : Sylow 2 (PSL d)).toSubgroup = _
  rw [hg, coe_projectiveSylow]

/-- The literal SL-to-PSL comparison followed by the usual binary matrix action. -/
noncomputable def linearComparison (d : ℕ) : PSL d ≃* BinaryLinear.OuterCyclic.LinearGroup d :=
  (binaryProjectiveEquiv d).symm.trans (BinaryLinear.OuterCyclic.slEquivLinear d)

/-- The standard basis underlying the coordinate cuts in `Flags`. -/
noncomputable def coordinateBasis (m : ℕ) : BinaryLinear.InvariantNodeActions.Basis m :=
  Pi.basisFun (ZMod 2) (Fin (m + 1))

/-- Membership in the geometric cut is the same coordinate vanishing condition used by `PreservesCut`. -/
theorem mem_coordinateCut {m : ℕ} (i : Fin m) (v : Fin (m + 1) → ZMod 2) :
    v ∈ BinaryLinear.InvariantNodeActions.cutSpace (coordinateBasis m) i ↔
      ∀ j : Fin (m + 1), i.val < j.val → v j = 0 := by
  rw [BinaryLinear.InvariantNodeActions.cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin (m + 1), v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

/-- Identify the matrix flag with the geometric flag, retaining each omitted root index. -/
theorem mem_parabolic_linear {m : ℕ} (J : Set ℕ) (g : SL (m + 1)) :
    g ∈ parabolic (m + 1) J ↔
      BinaryLinear.OuterCyclic.slEquivLinear (m + 1) g ∈
        BinaryLinear.InvariantNodeActions.cutStabilizer (coordinateBasis m) {i | i.val ∉ J} := by
  constructor
  · intro h
    rw [BinaryLinear.InvariantNodeActions.mem_cutStabilizer_maps]
    intro i hi v hv
    have hv := (mem_coordinateCut i v).mp hv
    apply (mem_coordinateCut i _).mpr
    have hc := (preservesCut_iff (i.val + 1) g).mp
      (h (i.val + 1) ⟨by omega, by have := i.isLt; omega, by simpa using hi⟩).1
    simpa only [BinaryLinear.OuterCyclic.slEquivLinear_apply, Nat.lt_iff_add_one_le] using hc v hv
  · intro h k hk
    let i : Fin m := ⟨k - 1, by have := hk.2.1; have := hk.1; omega⟩
    have hik : i.val + 1 = k := by have := hk.1; dsimp [i]; omega
    have hi : i ∈ {i : Fin m | i.val ∉ J} := hk.2.2
    have hc (a : SL (m + 1))
        (ha : BinaryLinear.OuterCyclic.slEquivLinear (m + 1) a ∈
          BinaryLinear.InvariantNodeActions.cutStabilizer (coordinateBasis m) {i | i.val ∉ J}) :
        PreservesCut k a := by
      rw [← hik, preservesCut_iff]
      intro v hv
      have hv' : v ∈ BinaryLinear.InvariantNodeActions.cutSpace (coordinateBasis m) i :=
        (mem_coordinateCut i v).mpr (by simpa only [Nat.lt_iff_add_one_le] using hv)
      have hz := (BinaryLinear.InvariantNodeActions.mem_cutStabilizer_maps _ _ _).mp ha i hi v hv'
      simpa only [BinaryLinear.OuterCyclic.slEquivLinear_apply, Nat.lt_iff_add_one_le] using
        (mem_coordinateCut i _).mp hz
    refine ⟨hc g h, hc g⁻¹ ?_⟩
    rw [map_inv]
    exact (BinaryLinear.InvariantNodeActions.cutStabilizer _ _).inv_mem h

/-- Transport the actual projective flag to the geometric flag on the same coordinates. -/
theorem map_projectiveParabolic_linear {m : ℕ} (J : Set ℕ) :
    (projectiveParabolic (m + 1) J).map (linearComparison (m + 1)).toMonoidHom =
      BinaryLinear.InvariantNodeActions.cutStabilizer (coordinateBasis m) {i | i.val ∉ J} := by
  rw [projectiveParabolic, Subgroup.map_map]
  have he : (linearComparison (m + 1)).toMonoidHom.comp (binaryProjectiveEquiv (m + 1)).toMonoidHom =
      (BinaryLinear.OuterCyclic.slEquivLinear (m + 1)).toMonoidHom := by
    ext g : 1
    exact congrArg (BinaryLinear.OuterCyclic.slEquivLinear (m + 1))
      ((binaryProjectiveEquiv (m + 1)).symm_apply_apply g)
  rw [he]
  ext g
  obtain ⟨a, rfl⟩ := (BinaryLinear.OuterCyclic.slEquivLinear (m + 1)).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_parabolic_linear]

open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic

private theorem graph_inner_fixes_reversalInvariant {m : ℕ} (b : Basis m)
    (cuts : Set (Fin m)) (hcuts : ∀ i, i.rev ∈ cuts ↔ i ∈ cuts)
    (g : LinearGroup (m + 1))
    (hB : (cutStabilizer b Set.univ).map
      (graphLinear (m + 1) * MulAut.conj g).toMonoidHom = cutStabilizer b Set.univ) :
    (cutStabilizer b cuts).map (graphLinear (m + 1) * MulAut.conj g).toMonoidHom =
      cutStabilizer b cuts := by
  let a := graphLinear (m + 1) * MulAut.conj g
  have hp (j : Fin m) : (_root_.BinaryLinear.parabolic (cutSpace b j)).map a.toMonoidHom =
      _root_.BinaryLinear.parabolic (cutSpace b j.rev) := by
    rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g hB]
  ext s
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  have hm (j : Fin m) : a.symm s ∈ _root_.BinaryLinear.parabolic (cutSpace b j) ↔
      s ∈ _root_.BinaryLinear.parabolic (cutSpace b j.rev) := by
    rw [← hp j, Subgroup.mem_map_equiv]
  constructor
  · intro hs j hj
    have ht := (hm j.rev).mp (hs j.rev ((hcuts j).mpr hj))
    change s ∈ _root_.BinaryLinear.parabolic (cutSpace b j)
    simpa only [Fin.rev_rev] using ht
  · intro hs j hj
    exact (hm j).mpr (hs j.rev ((hcuts j).mpr hj))

private theorem automorphism_fixes_reversalInvariant {m : ℕ} (hm : m + 1 = 4 ∨ m + 1 = 5)
    (b : Basis m) (cuts : Set (Fin m)) (hcuts : ∀ i, i.rev ∈ cuts ↔ i ∈ cuts)
    (a : MulAut (LinearGroup (m + 1)))
    (hB : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ) :
    (cutStabilizer b cuts).map a.toMonoidHom = cutStabilizer b cuts := by
  obtain ⟨g, rfl | rfl⟩ := BinaryLinear.OuterCyclic.inner_graph hm a
  · exact inner_fixes_cutStabilizer b g hB cuts
  · exact graph_inner_fixes_reversalInvariant b cuts hcuts g hB

private theorem map_automorphism_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) (P : Subgroup A) :
    (P.map a.toMonoidHom).map e.toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x : 1
  change e (a x) = e (a (e.symm (e x)))
  rw [e.symm_apply_apply]

/-- The omitted roots are stable under reversal of the type-A diagram. -/
def DiagramStable (d : ℕ) (J : Set ℕ) : Prop :=
  ∀ r : ℕ, r + 1 < d → (d - 2 - r ∈ J ↔ r ∈ J)

/-- An automorphism preserving the full binary flag preserves each diagram-stable flag in dimensions four and five. The proof includes the graph coset. -/
theorem projectiveParabolic_map_of_fullFlag {d : ℕ} (hd : d = 4 ∨ d = 5)
    (J : Set ℕ) (hJ : DiagramStable d J) (a : MulAut (PSL d))
    (hB : (projectiveParabolic d ∅).map a.toMonoidHom = projectiveParabolic d ∅) :
    (projectiveParabolic d J).map a.toMonoidHom = projectiveParabolic d J := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 from by omega)
  apply Subgroup.map_injective (f := (linearComparison (m + 1)).toMonoidHom)
    (linearComparison (m + 1)).injective
  rw [map_automorphism_congr, map_projectiveParabolic_linear]
  apply automorphism_fixes_reversalInvariant hd (coordinateBasis m) {i | i.val ∉ J}
  · intro i
    have hi := hJ i.val (by have := i.isLt; omega)
    have hi' : m.succ - 2 - i.val = m - (i.val + 1) := by omega
    simpa only [Set.mem_ofPred_eq, Fin.val_rev, hi'] using not_congr hi
  · have h := congrArg (Subgroup.map (linearComparison (m + 1)).toMonoidHom) hB
    rw [map_automorphism_congr, map_projectiveParabolic_linear] at h
    simpa only [Set.notMem_empty, not_false_eq_true, Set.ofPred_true] using h

/-- The two end nodes are stable under diagram reversal. -/
theorem outerRoots_diagramStable (d : ℕ) : DiagramStable d (outerRoots d) := by
  intro r hr
  simp only [outerRoots, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- The nodes between the two ends are stable under diagram reversal. -/
theorem middleRoots_diagramStable (d : ℕ) : DiagramStable d (middleRoots d) := by
  intro r hr
  simp only [middleRoots, Set.mem_ofPred_eq]
  omega

/-- The flag inside `L`, before adjoining the ambient Sylow subgroup. -/
noncomputable def transportedParabolic {G : Type*} [Group G] {d : ℕ}
    (L : Subgroup G) (e : L ≃* PSL d) (J : Set ℕ) : Subgroup G :=
  (projectiveParabolic d J).map (L.subtype.comp e.symm.toMonoidHom)

/-- The transported flag lies in the original embedded group. -/
theorem transportedParabolic_le {G : Type*} [Group G] {d : ℕ}
    (L : Subgroup G) (e : L ≃* PSL d) (J : Set ℕ) : transportedParabolic L e J ≤ L := by
  rintro x ⟨y, _, rfl⟩
  exact (e.symm y).property

/-- Every coordinate parabolic contains the full flag stabilizer. -/
theorem projectiveFullFlag_le (d : ℕ) (J : Set ℕ) :
    projectiveParabolic d ∅ ≤ projectiveParabolic d J := by
  apply Subgroup.map_mono
  intro g hg k hk
  exact hg k ⟨hk.1, hk.2.1, Set.notMem_empty _⟩

/-- Alignment puts the entire ambient Sylow intersection in every transported flag. -/
theorem sylowAligned_inf_le {G : Type*} [Group G] {d : ℕ}
    (L T : Subgroup G) (e : L ≃* PSL d) (he : SylowAligned L T e) (J : Set ℕ) :
    T ⊓ L ≤ transportedParabolic L e J := by
  intro x hx
  have hb : e ⟨x, hx.2⟩ ∈ projectiveParabolic d ∅ := by
    rw [← he]
    exact mem_map_of_mem e.toMonoidHom hx.1
  refine ⟨e ⟨x, hx.2⟩, projectiveFullFlag_le d J hb, ?_⟩
  change (e.symm (e ⟨x, hx.2⟩) : G) = x
  rw [e.symm_apply_apply]

/-- Conjugation by the ambient Sylow preserves its intrinsic intersection, hence the full model flag. -/
theorem sylowAligned_action_fullFlag {G : Type*} [Group G] {d : ℕ}
    (L T : Subgroup G) [L.Normal] (e : L ≃* PSL d) (he : SylowAligned L T e)
    (t : G) (ht : t ∈ T) :
    (projectiveParabolic d ∅).map (componentAction L e t).toMonoidHom =
      projectiveParabolic d ∅ := by
  have hn : t ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨T.le_normalizer ht, by rw [L.normalizer_eq_top]; trivial⟩
  have h := componentAction_map_subgroup L e (T ⊓ L) inf_le_right t hn
  have hi : (T ⊓ L).subgroupOf L = T.subgroupOf L := by ext x; simp
  rw [hi] at h
  rwa [he] at h

/-- The ambient Sylow normalizes the transported diagram-stable flag, including graph extensions. -/
theorem sylowAligned_normalizes {G : Type*} [Group G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L T : Subgroup G) [L.Normal] (e : L ≃* PSL d)
    (he : SylowAligned L T e) (J : Set ℕ) (hJ : DiagramStable d J) :
    T ≤ normalizer (transportedParabolic L e J : Set G) := by
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq]
  have hP := projectiveParabolic_map_of_fullFlag hd J hJ (componentAction L e t)
    (sylowAligned_action_fullFlag L T e he t ht)
  change ((projectiveParabolic d J).map (L.subtype.comp e.symm.toMonoidHom)).map
    (MulAut.conj t).toMonoidHom = _
  have hc : (MulAut.conj t).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) =
      (L.subtype.comp e.symm.toMonoidHom).comp (componentAction L e t).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change (MulAut.conjNormal t (e.symm x) : L).val =
      (e.symm (e (MulAut.conjNormal t (e.symm x)))).val
    rw [e.symm_apply_apply]
  rw [Subgroup.map_map, hc, ← Subgroup.map_map, hP]
  rfl

/-- Normalization for the actual outer-root flag used in E.1.14(1). -/
theorem sylowAligned_outer_normalizes {G : Type*} [Group G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L T : Subgroup G) [L.Normal] (e : L ≃* PSL d)
    (he : SylowAligned L T e) :
    T ≤ normalizer (transportedParabolic L e (outerRoots d) : Set G) :=
  sylowAligned_normalizes hd L T e he _ (outerRoots_diagramStable d)

/-- Normalization for the actual middle-root flag used in E.1.14(1). -/
theorem sylowAligned_middle_normalizes {G : Type*} [Group G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L T : Subgroup G) [L.Normal] (e : L ≃* PSL d)
    (he : SylowAligned L T e) :
    T ≤ normalizer (transportedParabolic L e (middleRoots d) : Set G) :=
  sylowAligned_normalizes hd L T e he _ (middleRoots_diagramStable d)

/-- The transported parabolic is normal relative to its actual ambient flag overgroup. -/
theorem transportedParabolic_normal_in_ambientFlag {G : Type*} [Group G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L T : Subgroup G) [L.Normal] (e : L ≃* PSL d)
    (he : SylowAligned L T e) (J : Set ℕ) (hJ : DiagramStable d J) :
    ((transportedParabolic L e J).subgroupOf (ambientFlag L T e J)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (show transportedParabolic L e J ≤
    ambientFlag L T e J from le_sup_left)).mpr
  exact sup_le (transportedParabolic L e J).le_normalizer
    (sylowAligned_normalizes hd L T e he J hJ)

/-- Adjoining the aligned Sylow adds no further elements of the original embedded group. -/
theorem ambientFlag_inf_socle {G : Type*} [Group G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L T : Subgroup G) [L.Normal] (e : L ≃* PSL d)
    (he : SylowAligned L T e) (J : Set ℕ) (hJ : DiagramStable d J) :
    ambientFlag L T e J ⊓ L = transportedParabolic L e J := by
  apply le_antisymm
  · rintro x ⟨hx, hxL⟩
    have hp : x ∈ ((transportedParabolic L e J : Set G) * (T : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (sylowAligned_normalizes hd L T e he J hJ)]
      exact hx
    obtain ⟨p, hp, t, ht, rfl⟩ := hp
    have htL : t ∈ L := (L.mul_mem_cancel_left (transportedParabolic_le L e J hp)).mp hxL
    exact (transportedParabolic L e J).mul_mem hp (sylowAligned_inf_le L T e he J ⟨ht, htL⟩)
  · exact le_inf le_sup_left (transportedParabolic_le L e J)

/-- Solvability of the actual model flag passes to its ambient Sylow overgroup. The required normalization is proved, not assumed. -/
theorem ambientFlag_isSolvable_of_model {G : Type*} [Group G] [Finite G] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (e : L ≃* PSL d) (he : SylowAligned L (T : Subgroup G) e)
    (J : Set ℕ) (hJ : DiagramStable d J) (hs : Group.IsSolvable (projectiveParabolic d J)) :
    Group.IsSolvable (ambientFlag L (T : Subgroup G) e J) := by
  let := hs
  let f := L.subtype.comp e.symm.toMonoidHom
  let : Group.IsSolvable (transportedParabolic L e J) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap (projectiveParabolic d J))
      (f.subgroupMap_surjective (projectiveParabolic d J))
  let := T.isPGroup'.isNilpotent
  exact Group.isSolvable_sup_of_normalizes (transportedParabolic L e J) (T : Subgroup G)
    (sylowAligned_normalizes hd L (T : Subgroup G) e he J hJ)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper
