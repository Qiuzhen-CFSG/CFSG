module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.OddEscape
public import Theory.GroupTheory.IndexTwoIntersectionGeneration
public import Theory.GroupAction.RankTwoCosetGeometry.EvenPathKernels

/-!
# Kernel intersections in the original quintic path argument

Let X=YT and K=O₂(H)∩O₂(X). The cubic quotient and the already proved
normalizer N_H(K)=T show that K has index two in O₂(H). Its H-normal
core centralizes the entire elementary span U=⟨Vᴴ⟩. The faithful-action
bound therefore makes that normal core have index at least sixteen.
The index-two intersection lemma supplies two H-conjugates, both moved
by elements outside T, whose intersections with K generate K.

The pointwise fixers of four- and six-edge paths from H are exactly the
intersections of the cubic radius-one kernels along those paths. This
retains the literal graph maps and supplies the subgroups needed by the
remaining extension-actor argument. No Suzuki quotient or path
transitivity is assumed in these statements. The numerical four-path
consumer is in `EightPathAction`; the remaining actors and D₁₀ exclusion
stay with qt-e-quintic-sylow-lower.

Source: Aschbacher--Smith F.3.2--4 and F.7.3, pp.270,311--312;
14.2.6 and14.2.20--21, pp.982,988--989.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The common local-core intersection is a hyperplane in the quintic core. -/
theorem source_quintic_crossing_core_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    (H.pCoreIn 2 ⊓ X.pCoreIn 2).relIndex (H.pCoreIn 2) = 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let B := X.pCoreIn 2
  let K := Q ⊓ B
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  obtain ⟨_,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hBi : B.relIndex (T : Subgroup G) = 2 := by
    change (X.pCoreIn 2).relIndex (T : Subgroup G) = 2
    let S := T.subtype hTX
    have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
    rw [SymmetricThreeTwoCore.sylow_index_three eX S, SymmetricThreeTwoCore.core_index eX] at hm
    have hi' : (pCore 2 X).relIndex (S : Subgroup X) = 2 := by omega
    have hmap : (S : Subgroup X).map X.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hTX
    rw [←hmap,pCoreIn,relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hi'
  have hn : H ⊓ normalizer (K : Set G) = (T : Subgroup G) :=
    source_quintic_core_intersection_normalizer hG T hempty hM hu hmany hcard e H hH hi
  have hnot : ¬ Q ≤ B := by
    intro hqb
    have heq : K = Q := inf_eq_left.mpr hqb
    have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    rw [heq,inf_eq_left.mpr hHQ] at hn
    have hiOne : (T : Subgroup G).relIndex H = 1 := relIndex_eq_one.mpr hn.le
    omega
  change (Q ⊓ B).relIndex Q = 2
  rw [inf_relIndex_left]
  have hu' : B.relIndex Q ≤ 2 := by
    simpa only [hBi] using relIndex_le_of_le_right (H := B) hQT (by rw [hBi]; decide)
  have hp : B.relIndex Q ≠ 0 := index_ne_zero_of_finite
  have hne : B.relIndex Q ≠ 1 := fun hh => hnot (relIndex_eq_one.mp hh)
  omega

/-- Two genuinely moved conjugates supply intersections generating the common core. -/
theorem source_quintic_crossing_core_generation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let K := H.pCoreIn 2 ⊓ X.pCoreIn 2
    ∃ a b : H, (a : G) ∉ (T : Subgroup G) ∧ (b : G) ∉ (T : Subgroup G) ∧
      (K ⊓ K.map (MulAut.conj (a : G)).toMonoidHom) ⊔
        (K ⊓ K.map (MulAut.conj (b : G)).toMonoidHom) = K := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let K := Q ⊓ X.pCoreIn 2
  let KH := K.subgroupOf H
  have hKH : K ≤ H := inf_le_left.trans (pCoreIn_le 2 H)
  have hKQ : KH ≤ pCore 2 H := by
    intro k hk
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp hk.1
  have hidx : KH.relIndex (pCore 2 H) = 2 := by
    rw [←relIndex_map_map_of_injective KH (pCore 2 H) H.subtype_injective,
      map_subgroupOf_eq_of_le hKH]
    exact source_quintic_crossing_core_index hG T hempty hM hu hmany hcard e H hH hi
  let A (a : H) := KH.map (MulAut.conj a).toMonoidHom
  have hA (a : H) : A a ≤ pCore 2 H := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hKQ
    have hn : (pCore 2 H).map (MulAut.conj a).toMonoidHom = pCore 2 H :=
      Normal.map_conj_eq (pCore 2 H) a
    rwa [hn] at hh
  have hAi (a : H) : (A a).relIndex (pCore 2 H) = 2 := by
    have hn : (pCore 2 H).map (MulAut.conj a).toMonoidHom = pCore 2 H :=
      Normal.map_conj_eq (pCore 2 H) a
    change (KH.map (MulAut.conj a).toMonoidHom).relIndex (pCore 2 H) = 2
    rw [←hn, relIndex_map_map_of_injective _ _ (MulAut.conj a).injective]
    exact hidx
  let N := KH.normalCore.map H.subtype
  have hNK : N ≤ K := by
    have hh := map_mono (f := H.subtype) KH.normalCore_le
    rwa [map_subgroupOf_eq_of_le hKH] at hh
  have hNH : H ≤ normalizer (N : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,H.range_subtype] using
      KH.normalCore.le_normalizer_map H.subtype
  have hNC : N ≤ centralizer (localModule T M : Set G) := by
    have hB := (source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1
    exact (hNK.trans inf_le_right).trans (hB.le.trans inf_le_right)
  have hNU : N ≤ H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) :=
    le_inf (map_subtype_le _) (le_centralizer_conjugateSpanBy_of_normalizes _ _ _ hNH hNC)
  have hsmall : 4 * Nat.card (⨅ a, A a : Subgroup H) < Nat.card (pCore 2 H) := by
    have hInf : (⨅ a, A a) = KH.normalCore := KH.normalCore_eq_iInf_map_conj.symm
    rw [hInf]
    have hl := source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi
    have hc := card_le_of_le hNU
    have hNc : Nat.card N = Nat.card KH.normalCore := card_map_of_injective H.subtype_injective
    rw [hNc] at hc
    have hp : 0 < Nat.card KH.normalCore := Nat.card_pos
    omega
  obtain ⟨a,b,ha,hb,he⟩ := exists_pair_intersections_sup_of_small_iInf (pCore 2 H) A hA hAi hsmall 1
  have hAone : A 1 = KH := by
    have hf : (MulAut.conj (1 : H)).toMonoidHom = MonoidHom.id H := by ext x; simp
    change KH.map (MulAut.conj (1 : H)).toMonoidHom = KH
    rw [hf,map_id]
  have hmap (a : H) : (A a).map H.subtype = K.map (MulAut.conj (a : G)).toMonoidHom := by
    change (KH.map (MulAut.conj a).toMonoidHom).map H.subtype = _
    rw [map_map]
    have hf : H.subtype.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (a : G)).toMonoidHom.comp H.subtype := rfl
    rw [hf,←map_map,map_subgroupOf_eq_of_le hKH]
  have hout (a : H) (ha : A a ≠ A 1) : (a : G) ∉ (T : Subgroup G) := by
    intro hat
    have hn := source_quintic_core_intersection_normalizer hG T hempty hM hu hmany hcard e H hH hi
    have hnorm : (a : G) ∈ normalizer (K : Set G) := (hn.symm ▸ hat).2
    apply ha
    apply map_injective H.subtype_injective
    rw [hmap,hAone,map_subgroupOf_eq_of_le hKH]
    exact mem_normalizer_iff_map_conj_eq.mp hnorm
  refine ⟨a,b,hout a ha,hout b hb,?_⟩
  have hh := congrArg (map H.subtype) he
  rw [Subgroup.map_sup,map_inf _ _ _ H.subtype_injective,
    map_inf _ _ _ H.subtype_injective,hAone,map_subgroupOf_eq_of_le hKH,hmap,hmap] at hh
  exact hh
open ChapterF.Section07 Subgroup.CosetGeometry.RankTwo SimpleGraph

/-- The literal four-path fixer is the intersection of its two cubic star kernels. -/
theorem source_quintic_four_path_fixer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
      pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓
      ballKernel F (p.2.2.1 : Vertex F) 1 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hi' (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi'
  have hflip {a b : Vertex F} (hab : (graph F).Adj a b) : b.type = !a.type := by
    have hh := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all
  change ∀ p : BasedWalk (graph F) 4 (base F true), p.Nonbacktracking →
    pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓ ballKernel F (p.2.2.1 : Vertex F) 1
  intro p hp
  apply pathStabilizer_four_eq_cubic_kernels F p hp
  · rw [hdegree,hflip p.1.property]
    rfl
  · rw [hdegree,hflip p.2.2.1.property,hflip p.2.1.property,hflip p.1.property]
    rfl

/-- The literal six-path fixer is the intersection of its three cubic star kernels. -/
theorem source_quintic_six_path_fixer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ p : BasedWalk (graph F) 6 (base F true), p.Nonbacktracking →
      pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓
      (ballKernel F (p.2.2.1 : Vertex F) 1 ⊓
        ballKernel F (p.2.2.2.2.1 : Vertex F) 1) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  obtain ⟨hthree,hfive,_⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hi' (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hdegree := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi'
  have hflip {a b : Vertex F} (hab : (graph F).Adj a b) : b.type = !a.type := by
    have hh := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all
  change ∀ p : BasedWalk (graph F) 6 (base F true), p.Nonbacktracking →
    pathStabilizer F p = ballKernel F (p.1 : Vertex F) 1 ⊓ (ballKernel F (p.2.2.1 : Vertex F) 1 ⊓ ballKernel F (p.2.2.2.2.1 : Vertex F) 1)
  intro p hp
  apply pathStabilizer_six_eq_cubic_kernels F p hp
  · rw [hdegree,hflip p.1.property]
    rfl
  · rw [hdegree,hflip p.2.2.1.property,hflip p.2.1.property,hflip p.1.property]
    rfl
  · rw [hdegree,hflip p.2.2.2.2.1.property,hflip p.2.2.2.1.property,
      hflip p.2.2.1.property,hflip p.2.1.property,hflip p.1.property]
    rfl

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
