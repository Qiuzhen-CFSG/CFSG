module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Parabolic
public import Theory.GroupTheory.CentralizerPrimeKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Faithfulness and family membership for the rank-four selection

The literal plus images of K and Tᵥ generate G⁺. With the source two-reduced
W_K action and a binary linear marking, the normal subgroup K⁺ has trivial
centralizer: its centralizer is a normal two-group, so it vanishes in O₂(G⁺).
Thus membership in K⁺ detects inner component actions without an extra
faithfulness premise.

The star commutator calculation also converts 13.6.16(3), local-component
membership, invariance and movement of z into every clause of Y_z. This is
used for the rank-three parabolic residual and for the ambient containing
component. Their construction and star-quasisimplicity remain necessary.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, 13.6.16(3), and 13.6.23, printed pp.929–933.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G]

/-- The actual actor becomes KTᵥ after invariance and Lᵥ-containment. -/
theorem plusActor_eq_sup (K L T : Subgroup G) (v : G)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G)) :
    plusActor K L T v = K ⊔ Tv T v := by
  rw [plusActor, Kminus_eq_of_invariant K T v hK, sup_eq_left.mpr hLK]

/-- The two literal plus images generate the entire faithful quotient. -/
theorem plusImage_sup_eq_top (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G)) :
    plusImage K L T z v hL hz K ⊔ plusImage K L T z v hL hz (Tv T v) = ⊤ := by
  rw [plusImage, plusImage, ← Subgroup.map_sup,
    ← subgroupOf_sup (K_le_plusActor K L T v) le_sup_right,
    ← plusActor_eq_sup K L T v hLK hK, subgroupOf_self,
    map_top_of_surjective _ (plusMk_surjective K L T z v hL hz)]

/-- The source R₂ condition on W_K forces faithfulness of the K⁺ action. -/
theorem plusComponent_centralizer_eq_bot [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hT : IsPGroup 2 (Tv T v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {n : ℕ} (hn : 0 < n) (e : plusImage K L T z v hL hz K ≃* SL(n, ZMod 2)) :
    centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥ := by
  let C := plusImage K L T z v hL hz K
  let : C.Normal := plusComponent_normal K L T z v hL hz hLK hK
  have hZ : center C = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center SL(n, ZMod 2) := (centerCongr e ⟨x, hx⟩).property
    rw [binary_center_eq_bot hn, mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hCp : IsPGroup 2 (centralizer (C : Set (Gplus K L T z v hL hz))) := by
    apply isPGroup_centralizer_of_quotient C
    · exact isPGroup_quotient_of_sup_eq_top C _
        (hT.comap_subtype.map _) (plusImage_sup_eq_top K L T z v hL hz hLK hK)
    · rw [hZ]
      exact IsPGroup.of_card (n := 0) (by simp)
  apply eq_bot_iff.mpr
  exact (le_sSup ⟨inferInstance, hCp⟩ : centralizer (C : Set _) ≤ pCore 2 _).trans hR.le

/-- The star quotient preserves commutators of subgroups contained in Gᵥ. -/
theorem starImage_commutator (z v : G) (A B : Subgroup G)
    (hA : A ≤ Gv v) (hB : B ≤ Gv v) :
    starImage z v ⁅A, B⁆ = ⁅starImage z v A, starImage z v B⁆ := by
  have he : ⁅A, B⁆.subgroupOf (Gv v) = ⁅A.subgroupOf (Gv v), B.subgroupOf (Gv v)⁆ := by
    apply map_injective (Gv v).subtype_injective
    rw [map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup A B).trans (sup_le hA hB)),
      map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB]
  unfold starImage
  rw [he, map_commutator]

/-- All Y_z clauses from the invariant local component and its Thompson commutator. -/
theorem mem_Yz_of_invariant_generated [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hLN : Lv L v ≤ normalizer (K : Set G))
    (hq : Theory.GroupTheory.IsQuasisimple (starImage z v K ⧸ pCore 2 (starImage z v K)))
    (hmove : ¬ K ≤ centralizer ({z} : Set G))
    (hgen : ⁅K, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = K) : K ∈ Yz L T z v := by
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hlocal.2
  let : Group.IsPerfect (starImage z v K) :=
    Group.IsPerfect.ofSurjective (starImageMap_surjective z v K hlocal.1)
  have hres : pResidual 2 (starImage z v K) = ⊤ := by
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hNp
    let := hN
    let := hNp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hnorm : Lv L v ⊔ Tv T v ≤ normalizer (K : Set G) :=
    sup_le hLN hn
  have hstarNorm : starImage z v (Lv L v) ⊔ starImage z v (Tv T v) ≤
      normalizer (starImage z v K : Set _) := by
    rw [← starImage_sup z v (Lv L v) (Tv T v) (Lv_le_Gv L v) inf_le_right]
    apply le_trans (map_mono (f := starMk z v) ?_)
      ((K.subgroupOf (Gv v)).le_normalizer_map _)
    rw [← subgroupOf_normalizer_eq hlocal.1]
    exact comap_mono hnorm
  have hstarMove : ¬ starPreimage z v (starImage z v K) ≤ centralizer ({z} : Set G) :=
    fun h => hmove ((le_starPreimage_starImage z v K hlocal.1).trans h)
  have hJ : Stellmacher.elementaryAbelianMaxJ (Tv T v) ≤ Gv v :=
    (sSup_le fun _ h => h.1).trans inf_le_right
  refine ⟨hlocal, hq, ?_⟩
  rw [← starImage_Kminus K T z v hlocal.1, Kminus_eq_of_invariant K T v hn]
  refine ⟨⟨hstarNorm, ?_, ?_, ?_⟩, hstarMove⟩
  · rw [hres, ← MonoidHom.range_eq_map, range_subtype]
  · intro he
    exact hmove (((starImage_eq_bot_iff z v K hlocal.1).mp he).trans
      (centralizer_le (Set.singleton_subset_iff.mpr (z_mem_Uv z v))))
  · rw [← starImage_commutator z v K _ hlocal.1 hJ, hgen]

/-- Apply the genuine universal 13.6.16(3) to a local subgroup containing
Lᵥ. Movement of z is inherited from Lᵥ, not postulated for the new subgroup. -/
theorem mem_Yz_of_source_commutator [Finite G]
    (K L T : Subgroup G) (z v : G)
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      ⁅D, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = D)
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage z v K ⧸ pCore 2 (starImage z v K)))
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G)) : K ∈ Yz L T z v := by
  have hKmove : ¬ K ≤ centralizer ({z} : Set G) := fun h => hmove (hLK.trans h)
  exact mem_Yz_of_invariant_generated K L T z v hlocal hn
    (hLK.trans K.le_normalizer) hq hKmove
    (h16 K hlocal hn hKmove)

/-- The rank-three replacement contradicts the L₃(2) clause of genuine
13.6.22. The earlier source commutator proves Y_z membership for the
actual moving local subgroup; no family-membership tag is assumed. -/
theorem false_of_rankThree_source_replacement [Finite G]
    (D L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (h16 : ∀ K ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (K : Set G) → ¬ K ≤ centralizer ({z} : Set G) →
      ⁅K, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = K)
    (hsmall : ∀ K ∈ Yz L T z v,
      ¬ Nonempty (plusImage K L T z v hL hz K ≃* SL(3, ZMod 2)))
    (hlocal : D ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hn : Tv T v ≤ normalizer (D : Set G))
    (hLN : Lv L v ≤ normalizer (D : Set G))
    (hq : Theory.GroupTheory.IsQuasisimple (starImage z v D ⧸ pCore 2 (starImage z v D)))
    (hmove : ¬ D ≤ centralizer ({z} : Set G))
    (e : plusImage D L T z v hL hz D ≃* SL(3, ZMod 2)) : False :=
  hsmall D (mem_Yz_of_invariant_generated D L T z v hlocal hn hLN hq hmove
    (h16 D hlocal hn hmove)) ⟨e⟩

/-- The marked source parabolic and an outside actor force rank four.
The component-action faithfulness premise of the intrinsic flag theorem
is discharged from the actual W_K action here. -/
theorem rankFour_of_marked_sourceParabolic [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hT : IsPGroup 2 (Tv T v))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2))
    (b : Basis m) (i : Fin m)
    (hP : ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
      (plusImage K L T z v hL hz K)).map
      (e.trans (slEquivLinear (m + 1))).toMonoidHom = minimalParabolic b i)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    m = 3 ∧ i.val = 1 :=
  rankFour_of_outer_sourceParabolic K L T z v hL hz hLK hK hm e b i hP
    (plusComponent_centralizer_eq_bot K L T z v hL hz hLK hK hT hR (by omega) e) hout

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
