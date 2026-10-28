module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryGraphNeighbors
public import Theory.GroupTheory.CommutatorOrbitCard
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The two moving neighbors in the odd escaping graph

Centralizer rigidity below the global parameter bounds every nonzero
two-group displacement from below. Sylow conjugacy in the layer normalizer
and line centralizer gives the matching upper bound, identifying the first
neighbor commutator with the literal endpoint line.

Equality of the endpoint lines would put the backward closure in the local
two-core, contradicting criticality. The closure commutator bound therefore
forces the chosen neighbor out of O₂(H). Applying the proved index-two
selection in H constructs the reverse neighbor. Its hyperplane acts
nontrivially by the same centralizer rigidity, and its commutator is the
original line. Both conjugators and relative normalizers are retained.

These are the two-neighbor and line-identification steps of 6.1.19. The
subsequent parameter reduction and nonabelianness, initial 6.1.4–5, and final
6.1.27 assembly remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.17(4), 6.1.19 and F.7.13(1), printed
pp.672–674 and 314.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
variable {G : Type*} [Group G] [Finite G]

private theorem commutator_card_lower
    {V A : Subgroup G} [IsElementaryAbelian 2 V] {n : ℕ}
    (hs : globalS V = n) (hA : IsPGroup 2 A)
    (hmove : ⁅V,A⁆ ≠ ⊥) : 2 ^ n ≤ Nat.card (⁅V,A⁆ : Subgroup G) := by
  have hnc : ¬ A ≤ centralizer (V : Set G) := by
    intro hc
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hc))
  obtain ⟨a,ha,hav⟩ := SetLike.not_le_iff_exists.mp hnc
  let C := centralizer ({a} : Set G)
  have hlower : 2 ^ n ≤ C.relIndex V := by
    by_contra hlt
    have hlog : subgroupCorank V (V ⊓ C) < n := by
      unfold subgroupCorank
      rw [inf_relIndex_left]
      exact (Nat.log_lt_iff_lt_pow (b := 2) (x := n) (y := C.relIndex V)
        (by decide) (C.subgroupOf V).index_ne_zero_of_finite).mpr (Nat.lt_of_not_ge hlt)
    have hr := centralizer_inf_eq_of_corank_lt_globalS
      (show V ⊓ C ≤ V from inf_le_left)
      (show (subgroupCorank V (V ⊓ C) : ℕ∞) < globalS V from by
        rw [hs]; exact_mod_cast hlog) hA
    have haC : a ∈ centralizer (V ⊓ C : Set G) := by
      intro c hc
      exact mem_centralizer_singleton_iff.mp hc.2
    exact hav ((hr.le ⟨ha,haC⟩).2)
  have hc := card_le_commutator_card_mul_centralizer V a
  have hcount : C.relIndex V * Nat.card (C.subgroupOf V) = Nat.card V :=
    (C.subgroupOf V).index_mul_card
  have hupper : C.relIndex V ≤ Nat.card (⁅V,A⁆ : Subgroup G) := by
    rw [←hcount] at hc
    have hh := (Nat.mul_le_mul_right (Nat.card (C.subgroupOf V))
      (Nat.card_le_card_of_injective _ (inclusion_injective
        (commutator_mono (H₁ := V) le_rfl (zpowers_le.mpr ha)))))
    exact (Nat.le_of_mul_le_mul_right · (Nat.card_pos (α := C.subgroupOf V))) (hc.trans hh)
  exact hlower.trans hupper

variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

private theorem commutator_le_line
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAN : A ≤ normalizer (layer L R : Set G))
    (hAC : A ≤ Escape.I (T : Subgroup G) L R) :
    ⁅layer L R,A⁆ ≤ ZS (T : Subgroup G) L R := by
  let B := layer L R
  let Z := ZS (T : Subgroup G) L R
  let J := normalizer (B : Set G) ⊓ centralizer (Z : Set G)
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) := by
    apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
    · exact h.sylow_normalizes_layer.trans (normalizer (B : Set G)).le_normalizer
    · exact h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z)
  have hAJ : A ≤ J := le_inf hAN hAC
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  obtain ⟨P,hP⟩ := (show IsPGroup 2 (A.subgroupOf J) from hA.comap_subtype).exists_le_sylow
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq J P S
  have hmap : (P : Subgroup J).map (MulAut.conj m).toMonoidHom =
      (T : Subgroup G).subgroupOf J := by
    change ((m • P : Sylow 2 J) : Subgroup J) = _
    rw [hm,hS]
  have hAT : A.map (MulAut.conj (m : G)).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨a,ha,rfl⟩
    have hh : MulAut.conj m (⟨a,hAJ ha⟩ : J) ∈ (T : Subgroup G).subgroupOf J :=
      hmap ▸ mem_map_of_mem (MulAut.conj m).toMonoidHom (hP ha)
    exact hh
  have hBn : B.map (MulAut.conj (m : G)).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp m.property.1
  have hZn : Z.map (MulAut.conj (m : G)).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) m.property.2)
  have hAc : A.map (MulAut.conj (m : G)).toMonoidHom ≤ centralizer (Z : Set G) := by
    have hh := (map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hAC).trans
      (map_centralizer_le_centralizer_image (Z : Set G) (MulAut.conj (m : G)).toMonoidHom)
    simpa only [←Subgroup.coe_map,hZn] using hh
  apply (map_le_map_iff_of_injective (f := (MulAut.conj (m : G)).toMonoidHom) (MulAut.conj (m : G)).injective).mp
  rw [map_commutator,hBn,hZn]
  exact (commutator_mono le_rfl (le_inf hAT hAc)).trans
    (natural_central_line_sylow_commutator h hnat).le


/-- Every nonzero two-group displacement in the line centralizer fills that line. -/
theorem commutator_eq_line
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAN : A ≤ normalizer (layer L R : Set G))
    (hAC : A ≤ Escape.I (T : Subgroup G) L R)
    (hne : ⁅layer L R,A⁆ ≠ ⊥) :
    ⁅layer L R,A⁆ = ZS (T : Subgroup G) L R := by
  let := h.layer_elementary
  apply eq_of_le_of_card_ge (commutator_le_line h hnat hA hAN hAC)
  change Nat.card (layer L R ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) : Subgroup G) ≤ _
  rw [(hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1]
  exact commutator_card_lower hs hA hne

/-- The same displacement equality for the literal conjugate layer and line. -/
theorem conjugate_commutator_eq_line
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (a : G) {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAN : A ≤ normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G))
    (hAC : A ≤ centralizer ((ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom : Set G))
    (hne : ⁅(layer L R).map (MulAut.conj a).toMonoidHom,A⁆ ≠ ⊥) :
    ⁅(layer L R).map (MulAut.conj a).toMonoidHom,A⁆ =
      (ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom := by
  let f := (MulAut.conj a⁻¹).toMonoidHom
  have hn : A.map f ≤ normalizer (layer L R : Set G) := by
    have hh := map_mono (f := f) hAN
    rw [map_equiv_normalizer_eq,fusion_map_conj_inverse] at hh
    exact hh
  have hc : A.map f ≤ Escape.I (T : Subgroup G) L R := by
    have hh := (map_mono (f := f) hAC).trans
      (map_centralizer_le_centralizer_image
        ((ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom : Set G) f)
    change A.map f ≤ centralizer (((ZS (T : Subgroup G) L R).map
      (MulAut.conj a).toMonoidHom).map f : Set G) at hh
    rwa [fusion_map_conj_inverse] at hh
  have hnon : ⁅layer L R,A.map f⁆ ≠ ⊥ := by
    intro hz
    apply hne
    apply (map_eq_bot_iff_of_injective _ (f := f) (MulAut.conj a⁻¹).injective).mp
    rwa [map_commutator,fusion_map_conj_inverse]
  apply map_injective (f := f) (MulAut.conj a⁻¹).injective
  rw [map_commutator,fusion_map_conj_inverse,fusion_map_conj_inverse]
  exact commutator_eq_line h hnat hs (hA.map f) hn hc hnon

namespace OddConfiguration
variable (d : OddConfiguration T L M R)

/-- Criticality prevents equality of the two literal endpoint lines. -/
theorem endpoint_line_ne
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M) :
    (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom ≠
      ZS (T : Subgroup G) L R := by
  intro he
  have hN : d.representative⁻¹ ∈ Escape.H (T : Subgroup G) L R :=
    (Subgroup.normalizer (ZS (T : Subgroup G) L R : Set G)).inv_mem
      (mem_normalizer_iff_map_conj_eq.mpr he)
  have hHN : d.H ≤ Escape.H (T : Subgroup G) L R := d.overgroup.trans
    (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
  have hnorm := natural_escape_normalizer_normalizes_U h hE hNS
  have hU : (Escape.U (T : Subgroup G) L R).map
      (MulAut.conj d.representative⁻¹).toMonoidHom = Escape.U (T : Subgroup G) L R :=
    mem_normalizer_iff_map_conj_eq.mp (hnorm hN)
  have hc := map_mono (f := (MulAut.conj d.representative⁻¹).toMonoidHom) d.closure_le
  rw [hU] at hc
  exact d.closure_back_not_le_core (hc.trans
    ((natural_escape_frattini_and_normalizer_core h hnat hE hNS).2.1.trans
      (Chapter3.twoCore_le_of_sylow_le T d.hstar.1.1.2 hHN)))

/-- The first neighbor displacement is the entire endpoint central line. -/
theorem neighbor_commutator_eq_endpoint_line
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    {a : G} (ha : d.representative⁻¹ * a ∈ d.H)
    (hne : ⁅(layer L R).map (MulAut.conj a).toMonoidHom,
      d.localClosure ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)⁆ ≠ ⊥) :
    ⁅(layer L R).map (MulAut.conj a).toMonoidHom,
      d.localClosure ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)⁆ =
      (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom := by
  have hAC : d.localClosure ≤ centralizer
      ((ZS (T : Subgroup G) L R).map (MulAut.conj a).toMonoidHom : Set G) := by
    rw [d.neighbor_line_eq h ha]
    exact ((d.crossed_centralization h hnat hs).2.trans
      (map_mono (f := (MulAut.conj d.representative).toMonoidHom) inf_le_right)).trans
      (map_centralizer_le_centralizer_image
        (ZS (T : Subgroup G) L R : Set G) (MulAut.conj d.representative).toMonoidHom)
  let : IsElementaryAbelian 2 d.localClosure := d.closure_elementary
  rw [conjugate_commutator_eq_line h hnat hs a
    ((IsElementaryAbelian.isPGroup 2 d.localClosure).to_le inf_le_left)
    inf_le_right (inf_le_left.trans hAC) hne,d.neighbor_line_eq h ha]


/-- The local closure centralizes the line fixer in the local two-core,
modulo the original central line. Relative normality is retained inside H. -/
theorem closure_core_commutator
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n) :
    ⁅d.localClosure,d.H.pCoreIn 2 ⊓ Escape.I (T : Subgroup G) L R⁆ ≤
      ZS (T : Subgroup G) L R := by
  let Q := d.H.pCoreIn 2 ⊓ Escape.I (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  have hHZ : d.H ≤ Subgroup.normalizer (Z : Set G) := d.overgroup.trans
    (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
  have hHQ : d.H ≤ Subgroup.normalizer (Q : Set G) := by
    apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
    · exact d.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H))
    · exact hHZ.trans (normalizer_le_normalizer_centralizer Z)
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow d.H (T.subtype d.hstar.1.1.2)
    change d.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf d.H).map d.H.subtype at hh
    rw [map_subgroupOf_eq_of_le d.hstar.1.1.2] at hh
    exact inf_le_left.trans hh
  have hcomm : ⁅layer L R,Q⁆ ≤ Z :=
    commutator_le_line h hnat (T.isPGroup'.to_le hQT)
      (hQT.trans h.sylow_normalizes_layer) inf_le_right
  have hpre : d.localClosure ≤ commutatorPreimage d.H Q Z := by
    apply conjugateSpanBy_le
    · exact le_commutatorPreimage (h.layer_le_T.trans d.hstar.1.1.2) hcomm
    · exact commutatorPreimage_normalized d.H Q Z d.H hHZ d.H.le_normalizer hHQ hHZ
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le d.H Q Z hHZ)

/-- The moving neighbor escapes the actual two-core of H. If it were in
that core, the two line identities would force the distinct endpoint lines
to be equal. -/
theorem neighbor_not_le_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    {a : G} (ha : d.representative⁻¹ * a ∈ d.H)
    (hplace : (layer L R).map (MulAut.conj a).toMonoidHom ≤
      d.localClosure.map (MulAut.conj d.representative).toMonoidHom)
    (hne : ⁅(layer L R).map (MulAut.conj a).toMonoidHom,
      d.localClosure ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)⁆ ≠ ⊥) :
    ¬ (layer L R).map (MulAut.conj a).toMonoidHom ≤ d.H.pCoreIn 2 := by
  intro hc
  have hEI := hplace.trans ((d.crossed_centralization h hnat hs).1.trans inf_le_right)
  have hcomm := (commutator_mono
    (show d.localClosure ⊓ Subgroup.normalizer
      ((layer L R).map (MulAut.conj a).toMonoidHom : Set G) ≤ d.localClosure from inf_le_left)
    (le_inf hc hEI)).trans
    (d.closure_core_commutator h hnat)
  rw [commutator_comm, d.neighbor_commutator_eq_endpoint_line h hnat hs ha hne] at hcomm
  have he := eq_of_le_of_card_ge hcomm
    (by rw [card_map_of_injective (MulAut.conj d.representative).injective])
  exact d.endpoint_line_ne h hnat hE hNS he

private theorem all_proper_overgroups
    (X : Subgroup d.H) (hTX : ((T : Subgroup G).subgroupOf d.H) ≤ X)
    (hX : X ≠ ⊤) : X ≤ M.subgroupOf d.H := by
  have hlt : X.map d.H.subtype < d.H := by
    refine lt_of_le_of_ne (map_subtype_le _) ?_
    intro he
    apply hX
    apply map_injective d.H.subtype_injective
    simpa only [← MonoidHom.range_eq_map,range_subtype] using he
  obtain ⟨Y,hXY,hY⟩ := exists_le_covBy_of_lt hlt
  have hTY : (T : Subgroup G) ≤ Y := by
    have hh := map_mono (f := d.H.subtype) hTX
    rw [map_subgroupOf_eq_of_le d.hstar.1.1.2] at hh
    exact hh.trans hXY
  rw [d.unique_maximal Y hTY hY] at hXY
  intro x hx
  exact (hXY (mem_map_of_mem d.H.subtype hx)).2

/-- The index-two selection in H applies to any elementary subgroup which
escapes its two-core, with the chosen layer still an actual H-conjugate. -/
theorem exists_neighbor_of_not_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {A : Subgroup G} (hA : IsElementaryAbelian 2 A) (hAH : A ≤ d.H)
    (hcore : ¬ A ≤ d.H.pCoreIn 2) :
    ∃ k : d.H, (Subgroup.normalizer
      ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)).relIndex A = 2 := by
  let S := T.subtype d.hstar.1.1.2
  let B := M.subgroupOf d.H
  have hB : B ≠ ⊤ := by
    intro he
    apply d.hstar.1.2
    intro x hx
    exact show (⟨x,hx⟩ : d.H) ∈ B from he ▸ mem_top _
  have hSB : (S : Subgroup d.H) ≤ B := fun x hx => h.sylow_le hx
  let := hA
  have hAC : ¬ A.subgroupOf d.H ≤ pCore 2 d.H := by
    intro hh
    apply hcore
    have hm := map_mono (f := d.H.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAH] at hm
  obtain ⟨k,hk⟩ := index_two_conjugate_of_unique_maximal S B (A.subgroupOf d.H)
    hSB hB (fun X hX hne => d.all_proper_overgroups X hX hne)
    d.generation (IsElementaryAbelian.subgroupOf hAH) hAC
  have hmap (C : Subgroup d.H) :
      (C.map (MulAut.conj k).toMonoidHom).map d.H.subtype =
        (C.map d.H.subtype).map (MulAut.conj (k : G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hBmap : B.map d.H.subtype = d.H ⊓ Subgroup.normalizer (layer L R : Set G) := by
    rw [d.normalizer]
    exact (subgroupOf_map_subtype M d.H).trans (inf_comm M d.H)
  have hh := relIndex_map_map_of_injective
    (B.map (MulAut.conj k).toMonoidHom) (A.subgroupOf d.H) d.H.subtype_injective
  rw [hk,hmap,hBmap,map_subgroupOf_eq_of_le hAH] at hh
  have hnorm : (d.H ⊓ Subgroup.normalizer (layer L R : Set G)).map
      (MulAut.conj (k : G)).toMonoidHom =
      d.H ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj (k : G)).injective,
      map_normalizer_eq_of_bijective _ (f := (MulAut.conj (k : G)).toMonoidHom) (MulAut.conj (k : G)).bijective]
    have he : d.H.map (MulAut.conj (k : G)).toMonoidHom = d.H :=
      mem_normalizer_iff_map_conj_eq.mp (d.H.le_normalizer k.property)
    rw [he]
  rw [hnorm] at hh
  refine ⟨k,?_⟩
  have hi : (d.H ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)).subgroupOf A =
      (Subgroup.normalizer ((layer L R).map (MulAut.conj (k : G)).toMonoidHom : Set G)).subgroupOf A := by
    ext x
    exact and_iff_right (hAH x.property)
  change ((d.H ⊓ _).subgroupOf A).index = 2 at hh
  rwa [hi] at hh


/-- Reversing the moving neighbor gives a hyperplane actor on an actual
H-conjugate of the natural layer, with commutator the original central line. -/
theorem reverse_neighbor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    {a : G} (ha : d.representative⁻¹ * a ∈ d.H)
    (hplace : (layer L R).map (MulAut.conj a).toMonoidHom ≤
      d.localClosure.map (MulAut.conj d.representative).toMonoidHom)
    (hne : ⁅(layer L R).map (MulAut.conj a).toMonoidHom,
      d.localClosure ⊓ Subgroup.normalizer ((layer L R).map (MulAut.conj a).toMonoidHom : Set G)⁆ ≠ ⊥) :
    ∃ k : d.H, let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let V₀ := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
      V₀ ≤ d.localClosure ∧
      (Subgroup.normalizer (V₀ : Set G)).relIndex E = 2 ∧
      ⁅V₀,E ⊓ Subgroup.normalizer (V₀ : Set G)⁆ = ZS (T : Subgroup G) L R := by
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let := h.layer_elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEH : E ≤ d.H := hplace.trans d.opposite_placements.1
  have hEC : E ≤ Escape.I (T : Subgroup G) L R :=
    hplace.trans ((d.crossed_centralization h hnat hs).1.trans inf_le_right)
  obtain ⟨k,hk⟩ := d.exists_neighbor_of_not_core h inferInstance hEH
    (d.neighbor_not_le_core h hnat hE hs hNS ha hplace hne)
  let V₀ := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  let F := E ⊓ Subgroup.normalizer (V₀ : Set G)
  have hF : F ≤ E := inf_le_left
  have hi : F.relIndex E = 2 := by rw [inf_relIndex_left]; exact hk
  have hsE : globalS E = n := by
    rw [globalS_map_equiv (layer L R) (MulAut.conj a),hs]
  have hr : subgroupCorank E F < n := by
    unfold subgroupCorank
    rw [hi]
    norm_num
    exact h.n_gt_one
  have hnon : ⁅V₀,F⁆ ≠ ⊥ := by
    intro hz
    have hVp : IsPGroup 2 V₀ := (IsElementaryAbelian.isPGroup 2 (layer L R)).map _
    have hc := commutator_eq_bot_iff_le_centralizer.mp hz
    have hr' := centralizer_inf_eq_of_corank_lt_globalS hF
      (show (subgroupCorank E F : ℕ∞) < globalS E from by
        rw [hsE]; exact_mod_cast hr) hVp
    have hVE : V₀ ≤ centralizer (E : Set G) := by
      have hh : V₀ ≤ V₀ ⊓ centralizer (E : Set G) := by
        rw [←hr']
        exact le_inf le_rfl hc
      exact hh.trans inf_le_right
    have hEV : E ≤ Subgroup.normalizer (V₀ : Set G) :=
      (le_centralizer_iff.mp hVE).trans (Subgroup.centralizer_le_normalizer _)
    have he := relIndex_eq_one.mpr hEV
    rw [hk] at he
    norm_num at he
  have hHZ : d.H ≤ Subgroup.normalizer (ZS (T : Subgroup G) L R : Set G) :=
    d.overgroup.trans (sup_le (Subgroup.centralizer_le_normalizer _) h.sylow_normalizes_ZS)
  have hZk : (ZS (T : Subgroup G) L R).map (MulAut.conj (k : G)).toMonoidHom =
      ZS (T : Subgroup G) L R := mem_normalizer_iff_map_conj_eq.mp (hHZ k.property)
  have hFC : F ≤ centralizer ((ZS (T : Subgroup G) L R).map
      (MulAut.conj (k : G)).toMonoidHom : Set G) := by
    rw [hZk]
    exact hF.trans hEC
  refine ⟨k,?_,hk,?_⟩
  · change V₀ ≤ conjugateSpanBy (layer L R) d.H
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun x : d.H => (layer L R).map (MulAut.conj (x : G)).toMonoidHom) k
  · exact (conjugate_commutator_eq_line h hnat hs (k : G)
      ((IsElementaryAbelian.isPGroup 2 E).to_le hF) inf_le_right hFC hnon).trans hZk

/-- Both chosen neighbors, the two exact commutator lines and escape from
O₂(H), with no additional selection or displacement premises. -/
theorem exists_two_neighbors
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M) :
    ∃ (a : G) (k : d.H), let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let V₀ := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
      d.representative⁻¹ * a ∈ d.H ∧
      E ≤ d.localClosure.map (MulAut.conj d.representative).toMonoidHom ∧
      V₀ ≤ d.localClosure ∧
      (Subgroup.normalizer (E : Set G)).relIndex d.localClosure = 2 ∧
      ⁅E,d.localClosure ⊓ Subgroup.normalizer (E : Set G)⁆ =
        (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom ∧
      ¬ E ≤ d.H.pCoreIn 2 ∧
      (Subgroup.normalizer (V₀ : Set G)).relIndex E = 2 ∧
      ⁅V₀,E ⊓ Subgroup.normalizer (V₀ : Set G)⁆ = ZS (T : Subgroup G) L R := by
  obtain ⟨a,ha,_,hplace,hi,hne⟩ := d.exists_moving_index_two_neighbor h hs
  obtain ⟨k,hk,hi',he'⟩ := d.reverse_neighbor h hnat hE hs hNS ha hplace hne
  exact ⟨a,k,ha,hplace,hk,hi,d.neighbor_commutator_eq_endpoint_line h hnat hs ha hne,
    d.neighbor_not_le_core h hnat hE hs hNS ha hplace hne,hi',he'⟩

end OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph
