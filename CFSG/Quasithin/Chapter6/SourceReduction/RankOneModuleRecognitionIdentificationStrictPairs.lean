module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityPreparation
public import Theory.GroupTheory.BaerSuzukiLocal

/-!
# Conjugate pairs and the central plane in the strict branch

The common local analysis makes U normalize each H-conjugate of V. In the
strict branch, the intersection U ∩ V has order eight and hence index two
in V. A conjugate pair generating a non-two-group therefore has exactly
these intersections as its mutual normalizers. Source 6.2.6 then gives the
actual quaternion central product O₂(⟨V,Vᵍ⟩). A normal-intersection and
order calculation identifies this core with (U ∩ V)(U ∩ Vᵍ), inside U.

Relative Baer--Suzuki constructs such a pair. Its center of order two
forces V ∩ Z(U) = ⟨z⟩, proves U nonabelian, and identifies the image of
U ∩ V under the literal quotient U → U/Z(U) as an order-four plane.
No order-32 assertion about O₂(H) is used.

Source: Aschbacher--Smith, 6.2.14--16, printed pp.688--689. These results
supply the pair and plane geometry; the full strict-branch contradiction
remains with this task, and final identification with
qt-d-1222-rankone-recognition-identification.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

omit [Finite G] in
private theorem index_two_of_card_eight (B V : Subgroup G) (h : B ≤ V)
    (hB : Nat.card B = 8) (hV : Nat.card V = 16) : B.relIndex V = 2 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B V bot_le h
  rw [relIndex_bot_left, relIndex_bot_left, hB, hV] at hc
  omega

omit [Finite G] in
private theorem between_index_two (B N V : Subgroup G)
    (hBN : B ≤ N) (hNV : N ≤ V) (hi : B.relIndex V = 2) (hn : ¬ V ≤ N) : N = B := by
  have hm := relIndex_mul_relIndex B N V hBN hNV
  rw [hi] at hm
  have hn1 : N.relIndex V ≠ 1 := fun he => hn (relIndex_eq_one.mp he)
  have hbone : B.relIndex N = 1 := by
    have hd : B.relIndex N ∣ 2 := ⟨N.relIndex V, hm.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · exact hh
    · rw [hh] at hm
      omega
  exact le_antisymm (relIndex_eq_one.mp hbone) hBN

omit [Finite G] in
theorem LocalAnalysis.closure_normalizes_conjugate_layer
    (A : LocalAnalysis (T : Subgroup G) L M R z) {g : G}
    (hg : g ∈ centralizer ({z} : Set G)) :
    sourceClosure (T : Subgroup G) L R z ≤
      normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G) := by
  have hn : sourceClosure (T : Subgroup G) L R z ≤ normalizer (layer L R : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (A.layer_closure_commutator.trans inf_le_left)
  have hm := (map_mono (f := (MulAut.conj g).toMonoidHom) hn).trans
    ((layer L R).le_normalizer_map (MulAut.conj g).toMonoidHom)
  have he : (sourceClosure (T : Subgroup G) L R z).map
      (MulAut.conj g).toMonoidHom = sourceClosure (T : Subgroup G) L R z :=
    mem_normalizer_iff_map_conj_eq.mp
      (sourceClosure_normalized (T : Subgroup G) L R z hg)
  rwa [he] at hm

theorem LocalAnalysis.strict_pair_normalizers
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {g : G} (hg : g ∈ centralizer ({z} : Set G))
    (hp : ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let U := sourceClosure (T : Subgroup G) L R z
    let V := layer L R
    let Vg := V.map (MulAut.conj g).toMonoidHom
    (V ⊓ normalizer (Vg : Set G) = U ⊓ V) ∧
    (Vg ⊓ normalizer (V : Set G) = U ⊓ Vg) ∧
    (V ⊓ normalizer (Vg : Set G)).relIndex V = 2 ∧
    (Vg ⊓ normalizer (V : Set G)).relIndex Vg = 2 := by
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  let f := (MulAut.conj g).toMonoidHom
  have hUc : U.map f = U := mem_normalizer_iff_map_conj_eq.mp
    (sourceClosure_normalized (T : Subgroup G) L R z hg)
  have hU : U ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (A.layer_closure_commutator.trans inf_le_left)
  have hUg : U ≤ normalizer (V.map f : Set G) := A.closure_normalizes_conjugate_layer hg
  have hc : Nat.card (U ⊓ V : Subgroup G) = 8 :=
    (A.strict_intersection_eq_core h611 hnatural hstrict).2
  have hcg : Nat.card (U ⊓ V.map f : Subgroup G) = 8 := by
    rw [← hUc, ← map_inf _ _ _ (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj g).injective, hc]
  have hV : Nat.card V = 16 := hnatural.2.1.card
  have hVg : Nat.card (V.map f) = 16 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hV
  have hVp : IsPGroup 2 V := T.isPGroup'.to_le h611.layer_le_T
  have hVgp : IsPGroup 2 (V.map f) := hVp.map f
  have hi := index_two_of_card_eight (U ⊓ V) V inf_le_right hc hV
  have hig := index_two_of_card_eight (U ⊓ V.map f) (V.map f) inf_le_right hcg hVg
  have he := between_index_two (U ⊓ V) (V ⊓ normalizer (V.map f : Set G)) V
    (le_inf inf_le_right (inf_le_left.trans hUg)) inf_le_left hi
    (fun hn => hp (hVp.to_sup_of_normal_right' hVgp (hn.trans inf_le_right)))
  have heg := between_index_two (U ⊓ V.map f) (V.map f ⊓ normalizer (V : Set G)) (V.map f)
    (le_inf inf_le_right (inf_le_left.trans hU)) inf_le_left hig
    (fun hn => hp (hVp.to_sup_of_normal_left' hVgp (hn.trans inf_le_right)))
  exact ⟨he, heg, he.symm ▸ hi, heg.symm ▸ hig⟩


/-- The actual quaternion core of a non-two pair is generated by the two
strict hyperplanes and lies in the original source closure. -/
theorem LocalAnalysis.strict_pair_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {g : G} (hg : g ∈ centralizer ({z} : Set G))
    (hp : ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let U := sourceClosure (T : Subgroup G) L R z
    let V := layer L R
    let Vg := V.map (MulAut.conj g).toMonoidHom
    let J := V ⊔ Vg
    Nonempty (QuaternionCentralProductData (pCore 2 J)) ∧
    Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) ∧
    (U ⊓ V) ⊔ (U ⊓ Vg) = J.pCoreIn 2 ∧
    J.pCoreIn 2 ≤ U ∧
    V ⊓ Vg = ((center (pCore 2 J)).map (pCore 2 J).subtype).map J.subtype := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  let f := (MulAut.conj g).toMonoidHom
  let Vg := V.map f
  let J := V ⊔ Vg
  obtain ⟨_, _, hi, hig⟩ := A.strict_pair_normalizers h611 hnatural hstrict hg hp
  obtain ⟨⟨d⟩, e, _, hinter⟩ := A.non_two_pair g hi hig hp
  have hJH : J ≤ H := by
    refine sup_le (layer_le_involution_centralizer h611 hz) ?_
    rintro _ ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem hg (layer_le_involution_centralizer h611 hz hv)) (H.inv_mem hg)
  have hUn : H ≤ normalizer (U : Set G) := sourceClosure_normalized _ _ _ _
  have hUp : IsPGroup 2 U := (H.isPGroup_pCoreIn 2).to_le A.closure_le_core
  have hUI : U ⊓ J ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (hUp.to_le inf_le_left) inf_le_right
    ((le_inf (hJH.trans hUn) J.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hIP : (U ⊓ V) ⊔ (U ⊓ Vg) ≤ J.pCoreIn 2 := by
    apply sup_le
    · exact (le_inf inf_le_left (inf_le_right.trans le_sup_left)).trans hUI
    · exact (le_inf inf_le_left (inf_le_right.trans le_sup_right)).trans hUI
  have hUnV : U ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (A.layer_closure_commutator.trans inf_le_left)
  have hnorm : U ⊓ Vg ≤ normalizer (U ⊓ V : Set G) :=
    (le_inf (inf_le_left.trans U.le_normalizer) (inf_le_left.trans hUnV)).trans
      inf_normalizer_le_normalizer_inf
  have hUc : U.map f = U := mem_normalizer_iff_map_conj_eq.mp (hUn hg)
  have hc : Nat.card (U ⊓ V : Subgroup G) = 8 :=
    (A.strict_intersection_eq_core h611 hnatural hstrict).2
  have hcg : Nat.card (U ⊓ Vg : Subgroup G) = 8 := by
    change Nat.card (U ⊓ V.map f : Subgroup G) = 8
    rw [← hUc, ← map_inf _ _ _ (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj g).injective, hc]
  have hcP : Nat.card (J.pCoreIn 2) = 32 := (card_subtype J (pCore 2 J)).trans d.card
  have hcinter : Nat.card (V ⊓ Vg : Subgroup G) = 2 := by
    rw [hinter, card_subtype, card_subtype, d.center_card]
  have hbound : Nat.card ((U ⊓ V) ⊓ (U ⊓ Vg) : Subgroup G) ≤ 2 := by
    rw [← hcinter]
    exact card_le_of_le (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊓ V) (U ⊓ Vg) hnorm
  rw [hc, hcg] at hprod
  have hsupcard : 32 ≤ Nat.card ((U ⊓ V) ⊔ (U ⊓ Vg) : Subgroup G) := by
    nlinarith [Nat.mul_le_mul_right (Nat.card ((U ⊓ V) ⊔ (U ⊓ Vg) : Subgroup G)) hbound]
  have he : (U ⊓ V) ⊔ (U ⊓ Vg) = J.pCoreIn 2 :=
    eq_of_le_of_card_ge hIP (hcP.symm ▸ hsupcard)
  exact ⟨⟨d⟩, e, he, he ▸ sup_le inf_le_left inf_le_left, hinter⟩



/-- Relative Baer--Suzuki supplies a non-two pair inside the chosen centralizer. -/
theorem LocalAnalysis.exists_non_two_layer_pair
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    ∃ g ∈ centralizer ({z} : Set G),
      ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  have hnot : ¬ layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
    intro he
    have hc := A.layer_core_card
    rw [inf_eq_left.mpr he, hnatural.2.1.card] at hc
    contradiction
  obtain ⟨g, hg, _, hp⟩ := exists_noncentralizing_conjugate_sup_not_isPGroup
    (centralizer ({z} : Set G)) (layer L R) (layer_le_involution_centralizer h611 hz)
    (T.isPGroup'.to_le h611.layer_le_T) hnot
  exact ⟨g, hg, hp⟩

/-- Source 6.2.16(1): the actual center of U meets V in precisely the marked line. -/
theorem LocalAnalysis.strict_layer_center_intersection
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    (center U).map U.subtype ⊓ layer L R = zpowers z := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  obtain ⟨g, hg, hp⟩ := A.exists_non_two_layer_pair h611 hnatural hz
  let Vg := V.map (MulAut.conj g).toMonoidHom
  let J := V ⊔ Vg
  obtain ⟨⟨d⟩, _, he, hPU, hinter⟩ := A.strict_pair_core h611 hnatural hz hstrict hg hp
  have hzV : z ∈ V := hz.1
  have hzU : z ∈ U := (ZS_le_sourceClosure_intersection h611 hz hz).1
  have hUH : U ≤ H := A.closure_le_core.trans (H.pCoreIn_le 2)
  have hzC : z ∈ (center U).map U.subtype := by
    refine ⟨⟨z, hzU⟩, mem_center_iff.mpr ?_, rfl⟩
    intro u
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hUH u.property))
  have hzVg : z ∈ Vg := by
    refine ⟨z, hzV, ?_⟩
    change g * z * g⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hpairline : V ⊓ Vg = zpowers z := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr (show z ∈ V ⊓ Vg from ⟨hzV, hzVg⟩))
    rw [hinter, card_subtype, card_subtype, d.center_card, Nat.card_zpowers, horder]
  have hupper : (center U).map U.subtype ⊓ V ≤ V ⊓ Vg := by
    rintro x ⟨⟨u, hu, rfl⟩, hv⟩
    have huI : (u : G) ∈ (U ⊓ V) ⊔ (U ⊓ Vg) :=
      (show U ⊓ V ≤ (U ⊓ V) ⊔ (U ⊓ Vg) from le_sup_left) ⟨u.property, hv⟩
    have huP : (u : G) ∈ J.pCoreIn 2 := he ▸ huI
    obtain ⟨q, hq, hqu⟩ := huP
    change (q : G) = (u : G) at hqu
    rw [hinter]
    refine ⟨q, ⟨⟨q, hq⟩, mem_center_iff.mpr ?_, rfl⟩, hqu⟩
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hyU : (y.val : G) ∈ U := hPU ⟨y.val, y.property, rfl⟩
    have hh := congrArg Subtype.val (mem_center_iff.mp hu ⟨y.val, hyU⟩)
    change (y.val : G) * (q : G) = (q : G) * (y.val : G)
    change (y.val : G) * (u : G) = (u : G) * (y.val : G) at hh
    simpa only [hqu] using hh
  exact le_antisymm (hupper.trans_eq hpairline) (zpowers_le.mpr ⟨hzC, hzV⟩)

/-- U is nonabelian in the strict branch; its center cannot contain the
order-eight intersection with V. -/
theorem LocalAnalysis.strict_closure_noncommutative
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    ¬ IsMulCommutative (sourceClosure (T : Subgroup G) L R z) := by
  intro hc
  let U := sourceClosure (T : Subgroup G) L R z
  have he := A.strict_layer_center_intersection h611 hnatural hz horder hstrict
  have hcenter : (center U).map U.subtype = U := by
    rw [center_eq_top_iff.mpr hc, ← MonoidHom.range_eq_map, range_subtype]
  change (center U).map U.subtype ⊓ layer L R = zpowers z at he
  rw [hcenter] at he
  have hcard := (A.strict_intersection_eq_core h611 hnatural hstrict).2
  rw [he, Nat.card_zpowers, horder] at hcard
  contradiction

/-- The literal central-quotient image of the strict intersection is an
order-four plane, the dimension assertion in 6.2.16(1). -/
theorem LocalAnalysis.strict_central_quotient_plane_card
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let U := sourceClosure (T : Subgroup G) L R z
    Nat.card (((U ⊓ layer L R).subgroupOf U).map (QuotientGroup.mk' (center U))) = 4 := by
  let U := sourceClosure (T : Subgroup G) L R z
  let I := (U ⊓ layer L R).subgroupOf U
  have hI : Nat.card I = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ layer L R ≤ U from inf_le_left)).toEquiv).trans
      (A.strict_intersection_eq_core h611 hnatural hstrict).2
  have hmap : (center U ⊓ I).map U.subtype = zpowers z := by
    rw [map_inf _ _ _ U.subtype_injective,
      map_subgroupOf_eq_of_le (show U ⊓ layer L R ≤ U from inf_le_left),
      ← inf_assoc, inf_eq_left.mpr (map_subtype_le _)]
    exact A.strict_layer_center_intersection h611 hnatural hz horder hstrict
  have hci : Nat.card (center U ⊓ I : Subgroup U) = 2 := by
    rw [← card_subtype U (center U ⊓ I), hmap, Nat.card_zpowers, horder]
  have he := relIndex_mul_relIndex (⊥ : Subgroup U) (center U ⊓ I) I bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, hci, hI, inf_relIndex_right] at he
  have hr := relIndex_ker I (QuotientGroup.mk' (center U))
  rw [QuotientGroup.ker_mk'] at hr
  change Nat.card (I.map (QuotientGroup.mk' (center U))) = 4
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
