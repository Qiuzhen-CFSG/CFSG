module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.OrbitControl
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.NormalizerControlOrbit

/-!
# Aligning a moving conjugate and its point-normalizer core

The order-two kernel C_(V^g)(V) can be made exactly V₁^g by changing the
conjugator inside N_G(V), leaving the original conjugate subgroup unchanged.
Then V normalizes U^g and V_(n−1)=[V^g,V] lies in U^g. The point-normalizer
core displaces U only into V₁; the noncyclic-centralizer bound makes its
conjugate normalize V. Its intersection with V is exactly V_(n−1), so
[O₂(G₁)^g,V] lies in U^g.

The final action calculation uses the literal pointQuotientAction and
12.9.5(1) to show that V moves K₁^g/O₂(K₁)^g. No quotient, normality or
aligned-conjugator premise is added to the source hypotheses.

Source: Aschbacher--Smith, 12.9.9(1), printed p.863 of `refs/quasithin.pdf`.
The remaining component and final action steps belong to this source owner.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

theorem local_span_core_displacement
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (J : Subgroup G)
    (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ⁅J.pCoreIn 2, F.UH J⁆ ≤ F.Vi 1 := by
  let := h.chosen.elementary
  have hk := F.localKernel_core_le h.source.simpleQTKE L (normalizer (L : Set G)) J
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  apply commutator_le.mpr
  rintro x ⟨x,hx,rfl⟩ y hy
  exact (F.mem_localTildeAction_ker_iff J hJ.2.1 x).mp (hk hx) y hy

theorem point_span_core_displacement
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : ⁅F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1 :=
  local_span_core_displacement h earlier F F.H
    (F.H_mem_Hz (by have := h.rank; omega) L (normalizer (L : Set G))
      (h.flag_escape F earlier.alternatives))

/-- Once the moving-conjugate alignment places V_(n−1) in Uᵍ, the original
point-normalizer core conjugate normalizes V. -/
theorem conjugate_core_normalizes_seed
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (g : G) (hW : F.Vi (n - 1) ≤ conjugate F.U g) :
    conjugate (F.H.pCoreIn 2) g ≤ normalizer (V : Set G) := by
  apply normalizes_of_order_two_commutator_and_normalizer_control
    (B := F.Vi (n - 1)) (Z := conjugate (F.Vi 1) g) (F.le_seed _)
  · rw [F.card _ (by omega)]
    rcases hn with rfl | rfl <;> norm_num
  · change Nat.card ((F.Vi 1).map (MulAut.conj g⁻¹).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj _).injective, F.card 1 (by have := h.rank; omega)]
    norm_num
  · have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (point_span_core_displacement h earlier F)
    rw [map_commutator] at hm
    exact (commutator_mono le_rfl hW).trans hm
  · exact (source_intersections_of_local_geometry h earlier F hab control).2.2

omit [Finite G] in
private theorem right_conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Choose the conjugator without changing the conjugate subgroup so that its
order-two kernel is the conjugate of the original flag point. -/
theorem exists_aligned_conjugator
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (g : G) (hcard : Nat.card (conjugate V g ⊓ centralizer (V : Set G) : Subgroup G) = 2) :
    ∃ k : G, conjugate V k = conjugate V g ∧
      conjugate (F.Vi 1) k = conjugate V g ⊓ centralizer (V : Set G) := by
  let B := conjugate V g ⊓ centralizer (V : Set G)
  have hBV : conjugate B g⁻¹ ≤ V := by
    have hh : conjugate B g⁻¹ ≤ conjugate (conjugate V g) g⁻¹ :=
      map_mono (show B ≤ conjugate V g from inf_le_left)
    have he := conjugate_conjugate_inv V g⁻¹
    simp only [inv_inv] at he
    exact hh.trans he.le
  have hc : Nat.card (conjugate B g⁻¹) = Nat.card (F.Vi 1) := by
    rw [F.card 1 (by have := h.rank; omega)]
    change Nat.card (B.map (MulAut.conj _).toMonoidHom) = _
    rw [card_map_of_injective (MulAut.conj _).injective, hcard]
    rfl
  obtain ⟨l, hl, he⟩ := h.subspace_transitive _ _ hBV (F.le_seed 1) hc
  have hpoint : conjugate (F.Vi 1) l⁻¹ = conjugate B g⁻¹ := by
    rw [← he]
    simpa only [inv_inv] using conjugate_conjugate_inv (conjugate B g⁻¹) l⁻¹
  refine ⟨l⁻¹ * g, ?_, ?_⟩
  · rw [right_conjugate_mul,
      (conjugate_eq_iff V l⁻¹).mpr (h.chosen.normalizes (L.inv_mem hl))]
  · rw [right_conjugate_mul, hpoint, conjugate_conjugate_inv]

omit [Finite G] in
/-- Alignment makes V normalize the conjugate point normalizer and its span. -/
theorem aligned_seed_normalizes_span
    (F : InvariantFlag T V n) (g : G)
    (halign : conjugate (F.Vi 1) g = conjugate V g ⊓ centralizer (V : Set G)) :
    V ≤ conjugate F.H g ∧ V ≤ normalizer (conjugate F.U g : Set G) := by
  have hVH : V ≤ conjugate F.H g := by
    change V ≤ (normalizer (F.Vi 1 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact (le_centralizer_iff.mp (halign.le.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨hVH, hVH.trans ?_⟩
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (le_normalizer_conjugateSpanBy V F.H)
  rwa [map_equiv_normalizer_eq] at hm

/-- The abelian point span is contained in the actual point-normalizer core. -/
theorem point_span_le_core
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) : F.U ≤ F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  let : IsMulCommutative (conjugateSpanBy V F.H) := hab
  exact le_pCoreIn_of_normalizes
    (conjugateSpanBy_elementary_of_commutative V F.H).isPGroup F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)

/-- The aligned moving conjugate puts the flag hyperplane in U^g. -/
theorem aligned_hyperplane_le_span
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥)
    (halign : conjugate (F.Vi 1) g = conjugate V g ⊓ centralizer (V : Set G)) :
    F.Vi (n - 1) ≤ conjugate F.U g := by
  rw [← (moving_conjugate_flag_action h earlier F hab control g hAT hmove).2.2]
  exact (commutator_mono (map_mono (le_conjugateSpanBy V F.H)) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp (aligned_seed_normalizes_span F g halign).2)

/-- The conjugate two-core meets V in precisely the original flag hyperplane.
Its commutator with V is therefore contained in the conjugate abelian span. -/
theorem aligned_conjugate_core_geometry
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥)
    (halign : conjugate (F.Vi 1) g = conjugate V g ⊓ centralizer (V : Set G)) :
    conjugate (F.H.pCoreIn 2) g ≤ normalizer (V : Set G) ∧
      conjugate (F.H.pCoreIn 2) g ⊓ V = F.Vi (n - 1) ∧
      ⁅conjugate (F.H.pCoreIn 2) g, V⁆ ≤ conjugate F.U g := by
  let A := conjugate V g
  let Q := conjugate (F.H.pCoreIn 2) g
  let W := F.Vi (n - 1)
  have hWU : W ≤ conjugate F.U g :=
    aligned_hyperplane_le_span h earlier F hab control g hAT hmove halign
  have hUQ : conjugate F.U g ≤ Q := map_mono (point_span_le_core h F hab)
  have hQN : Q ≤ normalizer (V : Set G) :=
    conjugate_core_normalizes_seed h hn earlier F hab control g hWU
  have hVQ : V ≤ normalizer (Q : Set G) := by
    have hH := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
    rw [map_equiv_normalizer_eq] at hH
    exact (aligned_seed_normalizes_span F g halign).1.trans hH
  have hfixed := (moving_conjugate_flag_action h earlier F hab control g hAT hmove).1
  have hAV : A ⊓ V = ⊥ := by
    by_contra hne
    have hh := (source_intersections_of_local_geometry h earlier F hab control).2.1
      g (by rwa [inf_comm])
    exact hmove (by rwa [commutator_comm])
  have hAQ : ⁅A,Q⁆ ≤ conjugate (F.Vi 1) g := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (point_span_core_displacement h earlier F)
    rw [map_commutator] at hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl (map_mono (le_conjugateSpanBy V F.H))).trans hm
  have hcomm : ⁅A,Q ⊓ V⁆ = ⊥ := by
    apply bot_unique
    rw [← hAV]
    apply le_inf
    · exact ((commutator_mono le_rfl inf_le_left).trans hAQ).trans
        (map_mono (F.le_seed 1))
    · exact (commutator_mono le_rfl inf_le_right).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hAT.trans (h.sylow_normalizes_seed earlier.structural)))
  have hinter : Q ⊓ V = W := by
    apply le_antisymm ?_ (le_inf (hWU.trans hUQ) (F.le_seed _))
    change Q ⊓ V ≤ F.Vi (n - 1)
    rw [← hfixed]
    exact le_inf inf_le_right
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
  refine ⟨hQN, hinter, ?_⟩
  have hc : ⁅Q,V⁆ ≤ Q ⊓ V := le_inf
    (le_normalizer_iff_commutator_le_left.mp hVQ)
    (le_normalizer_iff_commutator_le_right.mp hQN)
  exact (hc.trans hinter.le).trans hWU

/-- The actual moving-conjugate application of alignment and core control. -/
theorem exists_aligned_moving_core
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) (control : LocalControl C)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥) :
    ∃ k : G, conjugate V k = conjugate V g ∧
      conjugate (F.Vi 1) k = conjugate V g ⊓ centralizer (V : Set G) ∧
      V ≤ conjugate F.H k ∧ F.Vi (n - 1) ≤ conjugate F.U k ∧
      conjugate (F.H.pCoreIn 2) k ≤ normalizer (V : Set G) ∧
      conjugate (F.H.pCoreIn 2) k ⊓ V = F.Vi (n - 1) ∧
      ⁅conjugate (F.H.pCoreIn 2) k, V⁆ ≤ conjugate F.U k := by
  obtain ⟨k, he, hk⟩ := exists_aligned_conjugator h F g
    (moving_conjugate_flag_action h earlier F hab control.normalizers g hAT hmove).2.1
  have hATk : conjugate V k ≤ (T : Subgroup G) := he ▸ hAT
  have hmovek : ⁅conjugate V k,V⁆ ≠ ⊥ := by rwa [he]
  have halign : conjugate (F.Vi 1) k = conjugate V k ⊓ centralizer (V : Set G) := by
    rwa [he]
  exact ⟨k, he, hk, (aligned_seed_normalizes_span F k halign).1,
    aligned_hyperplane_le_span h earlier F hab control.normalizers k hATk hmovek halign,
    aligned_conjugate_core_geometry h hn earlier F hab control.normalizers k hATk hmovek halign⟩

omit [Finite G] in
/-- Trivial commutators modulo the actual core lie in the kernel of the
literal point quotient action. -/
theorem le_pointQuotientCentralizer_of_commutator
    {F : InvariantFlag T V n} (C : ComponentGeometry F L)
    {A : Subgroup G} (hAH : A ≤ F.H) (hcomm : ⁅A,C.K1⁆ ≤ C.K1.pCoreIn 2) :
    A ≤ pointQuotientCentralizer C := by
  intro a ha
  refine ⟨⟨a,hAH ha⟩, ?_, rfl⟩
  change pointQuotientAction C ⟨a,hAH ha⟩ = 1
  apply MulEquiv.ext
  intro q
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C.K1) q
  change quotientAut (pCore 2 C.K1) _ (QuotientGroup.mk' (pCore 2 C.K1) k) =
    QuotientGroup.mk' (pCore 2 C.K1) k
  rw [quotientAut_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  have hc := hcomm (commutator_mem_commutator ha k.property)
  obtain ⟨x,hx,he⟩ := hc
  let aK : normalizer (C.K1 : Set G) := ⟨a,
    (normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal (hAH ha)⟩
  let d : C.K1 := C.K1.normalizerMonoidHom aK k / k
  change d ∈ pCore 2 C.K1
  have hed : x = d := by
    apply Subtype.ext
    change (x : G) = (C.K1.normalizerMonoidHom aK k : G) / (k : G)
    rw [normalizerMonoidHom_apply_apply_coe]
    simpa only [subtype_apply, div_eq_mul_inv, commutatorElement_def] using he
  exact hed ▸ hx

/-- The aligned seed acts nontrivially on the original conjugate component
quotient; otherwise 12.9.5(1) would make it normalize the moving conjugate. -/
theorem aligned_component_action_nontrivial
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L) (control : LocalControl C)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥)
    (halign : conjugate (F.Vi 1) g = conjugate V g ⊓ centralizer (V : Set G)) :
    ¬ ⁅conjugate C.K1 g,V⁆ ≤ conjugate (C.K1.pCoreIn 2) g := by
  intro hc
  have hVH := (aligned_seed_normalizes_span F g halign).1
  have hVHg : conjugate V g⁻¹ ≤ F.H := by
    have hm : conjugate V g⁻¹ ≤ conjugate (conjugate F.H g) g⁻¹ := map_mono hVH
    have he := conjugate_conjugate_inv F.H g⁻¹
    simp only [inv_inv] at he
    exact hm.trans he.le
  have hc' : ⁅conjugate V g⁻¹,C.K1⁆ ≤ C.K1.pCoreIn 2 := by
    have hm := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hc
    rw [map_commutator] at hm
    change ⁅conjugate (conjugate C.K1 g) g⁻¹,conjugate V g⁻¹⁆ ≤
      conjugate (conjugate (C.K1.pCoreIn 2) g) g⁻¹ at hm
    have hK := conjugate_conjugate_inv C.K1 g⁻¹
    have hQ := conjugate_conjugate_inv (C.K1.pCoreIn 2) g⁻¹
    simp only [inv_inv] at hK hQ
    rwa [hK,hQ,commutator_comm] at hm
  have hM := (le_pointQuotientCentralizer_of_commutator C hVHg hc').trans
    control.quotient_centralizer
  have hMN : normalizer (L : Set G) ⊓ F.H ≤ normalizer (V : Set G) :=
    (h.flag_normalizer_le earlier.structural F (by omega : 1 ≤ 1)
      (by have := h.rank; omega)).trans inf_le_right
  have hNg := (le_inf hM hVHg).trans hMN
  have hVN : V ≤ normalizer (conjugate V g : Set G) := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hNg
    rw [map_equiv_normalizer_eq] at hm
    change conjugate (conjugate V g⁻¹) g ≤ normalizer (conjugate V g : Set G) at hm
    rwa [conjugate_conjugate_inv] at hm
  have hAM : conjugate V g ≤ normalizer (L : Set G) :=
    hAT.trans (h.sylow_normalizes earlier.structural)
  have he : conjugate V g ⊓ normalizer (L : Set G) = conjugate V g := inf_eq_left.mpr hAM
  have hfix := (common_fixed_subgroups h earlier F hab control.normalizers g
    (inf_le_left.trans hAT) (by rwa [he])).2.1
  rw [he] at hfix
  have hVC := ((le_inf le_rfl hVN).trans hfix.le).trans inf_le_right
  exact hmove (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVC))

end CFSG.Quasithin.Chapter12.Section09.NaturalSource


