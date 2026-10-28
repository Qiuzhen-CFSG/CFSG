module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Normalizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeCore

/-!
# The source normalizer equality from component containment

Only the first assertion of A.3.12 is needed at the central-plane normalizer.
The complete known-simple containment-and-normality source
constructs the normal containing component. Reapplying the marked local cover
then identifies that component by its order and identifies both plane labels.

Source: Aschbacher–Smith 15.3.38, printed p.1136, using 1.2.4, p.505.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel GlobalGeometry Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem outside_sqtk_source {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (d : CharacteristicTwo.LocalData G) (H : Subgroup G) (hH : H ∈ d.Hplus) :
    IsSQTK κ (H ⧸ pCore 2 H) := by
  let R := H.pCoreIn 2
  have hHN : H ≤ normalizer (R : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal (normalizer (R : Set G)) := ⟨R, hH.1.1, isPGroup_pCoreIn 2 H, rfl⟩
  have hsq : IsSQTK κ H := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((hG.twoLocal_sqtk hN).subgroup (H.subgroupOf (normalizer (R : Set G))))
  refine ⟨?_, hsq.isKGroup.quotient _⟩
  intro p hp ho
  let _ : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hsq.stronglyQuasithin p hp ho)


/-- The actual normalizer contains a normal C-component containing L. -/
theorem normalizer_component_extension_knownSimple
    {Yplus S M I L V : Subgroup G} [IsKleinFour V]
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (hQ : ∀ H ∈ outsideFamily Yplus S M, IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H))
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V) :
    let N := normalizer (V : Set G)
    N ∈ outsideFamily Yplus S M ∧
      ∃ K : Subgroup N, K.IsCComponent ∧ L ≤ K.map N.subtype ∧ K.Normal := by
  let N := normalizer (V : Set G)
  obtain ⟨hIN, hN⟩ := normalizer_mem_outsideFamily hI hIL hZ
  obtain ⟨P, hP⟩ := hSylow N hN
  have hSI : S ≤ I := le_sup_right.trans hI.1.2
  have hSN : S ≤ N := hSI.trans hIN
  have hLN : L ≤ N := hLI.trans hIN
  have hlocal : L ∈ Chapter1.L G S :=
    mem_L_of_cComponent hI.1.1 (hSylow I hI) hLI hL
  have hLP : L.subgroupOf N ∈ Chapter1.L N (P : Subgroup N) := by
    have he : S.subgroupOf N = (P : Subgroup N) := by
      rw [← hP, subgroupOf, comap_map_eq_self_of_injective N.subtype_injective]
    rw [← he]
    exact (mem_LIn_iff_subgroupOf hSN hLN).mp ⟨hLN, hlocal⟩
  have hPN : (P : Subgroup N) ≤ normalizer (L.subgroupOf N : Set N) := by
    intro x hx
    have hxL : (x : G) ∈ normalizer (L : Set G) :=
      hIL (hSI (hP ▸ mem_map.mpr ⟨x, hx, rfl⟩))
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp hxL y
  obtain ⟨K, ⟨hK, hLK, hnormal⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source (hQ N hN) P hLP hPN
  refine ⟨hN, K, hK, ?_, hnormal⟩
  simpa only [map_subgroupOf_eq_of_le hLN] using map_mono (f := N.subtype) hLK



/-- The actual full central-plane normalizer, with all source containment inputs discharged. -/
theorem normalizer_eq_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) : I = normalizer (r.cover.borel.W₁ : Set G) := by
  let V := r.cover.borel.W₁
  obtain ⟨i, hi⟩ := r.plane
  let : IsElementaryAbelian 2 V := d.action.elementary_of_le (by simpa only [V, hi] using d.action.plane_le i)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card r.cover.borel.W₁
    rw [hi, d.action.card_plane]; decide)
  let : IsKleinFour V := ⟨by simpa only [V, hi] using d.action.card_plane i, IsElementaryAbelian.exponent_eq_prime⟩
  let N := normalizer (V : Set G)
  have hZ : (center L).map L.subtype = V := r.cover.center_plane
  obtain ⟨hN, K, hK, hLK, hKn⟩ := normalizer_component_extension_knownSimple h.outside
    s.earlier.sylow (outside_sqtk_source hG d) h.component_le (component_isCComponent h.component)
    (h.normalizes_component s.earlier) hZ
  let B := K.map N.subtype
  have hBN : B ≤ N := map_subtype_le _
  have hBK : B.subgroupOf N = K := comap_map_eq_self_of_injective N.subtype_injective _
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect B := Group.IsPerfect.map N.subtype
  have hYB : ¬ d.Yplus ≤ B := yplus_not_le_perfect_normalizer d.Yplus B V hBN (r.noncentral s)
  have hBM : ¬ B ≤ d.M := fun hb => h.outside_component s.earlier (hLK.trans hb)
  have hthree : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa only [pow_one] using s.earlier.quotient_exponent)
  have hBout : ¬ (B.subgroupOf N).map N.subtype ≤ d.M := by
    rwa [map_subgroupOf_eq_of_le hBN]
  have hBC : IsComponent N (B.subgroupOf N) :=
    (Candidates.ComponentStructure.cComponent_ordinary_iff_outside hN s.earlier.sylow
      s.earlier.exclusion s.earlier.odd (inf_le_left.trans d.sylow_le)
      (s.earlier.normalizer_eq N hN) hthree
      (s.earlier.intersection_characteristic_two N hN) (hBK ▸ hK)).mpr hBout
  have hB3 : primeRank 3 B = 2 := by
    have hBN3 : primeRank 3 B ≤ primeRank 3 N := by
      rw [← primeRank_congr 3 (subgroupOfEquivOfLe hBN)]
      exact primeRank_subgroup_le 3 _
    exact le_antisymm (hBN3.trans (s.earlier.rank N hN))
      (h.component_rank.ge.trans (primeRank_mono 3 hLK))
  obtain ⟨b⟩ := local_result s (show Setup d N B from
    ⟨hN, hBN, hBC, hB3, h.residual_rank, hYB⟩)
  have hLB : L = B := eq_of_le_of_card_ge hLK (by rw [r.card, b.card])
  have hfirst : r.cover.borel.W₁ = b.cover.borel.W₁ :=
    r.cover.center_plane.symm.trans ((congrArg centerImage hLB).trans b.cover.center_plane)
  have hsecond := opposite_plane_eq r.cover.borel.planes b.cover.borel.planes hfirst
  apply SetLike.coe_injective
  calc
    (I : Set G) = (L : Set G) * (planeResidual d.M d.Y r.cover.borel.W₂ : Set G) *
      (d.S : Set G) := r.product
    _ = (B : Set G) * (planeResidual d.M d.Y b.cover.borel.W₂ : Set G) *
      (d.S : Set G) := by simp only [hLB, hsecond]
    _ = (N : Set G) := b.product.symm


/-- The actual balanced envelope puts its two-core in the selected central plane. -/
theorem LocalResult.representative_twoCore_le_plane
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (H : Subgroup G) (K : Subgroup H)
    (hK : IsComponent H K) (hLK : L ≤ K.map H.subtype) :
    H.pCoreIn 2 ≤ r.cover.borel.W₁ := by
  apply twoCore_le_plane_of_component_envelope I L r.cover.borel.W₁ H
    (normalizer_eq_knownSimple hG s h r) r.cover.overgroup_centralizer _ K hK hLK
  rw [← r.cover.center_plane]
  exact map_subtype_le _

/-- If the actual envelope core is the central plane, its overgroup is already I-local. -/
theorem LocalResult.representative_le_of_core_plane
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (H : Subgroup G)
    (hcore : H.pCoreIn 2 = r.cover.borel.W₁) : H ≤ I :=
  GlobalGeometry.representative_le_of_core_plane I r.cover.borel.W₁ H
    (normalizer_eq_knownSimple hG s h r) hcore


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
