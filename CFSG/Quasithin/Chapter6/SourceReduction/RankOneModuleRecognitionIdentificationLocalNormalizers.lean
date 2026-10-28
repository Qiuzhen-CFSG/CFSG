module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationContracts
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionComplete
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanksGlobal
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.SpecificGroups.SL2.NaturalStabilizer

/-!
# Normalizer control in the natural-layer local analysis

The central-line factorization and the relative TI theorem give source
6.2.1. Source 6.1.11 then proves 6.2.3: a noncommuting mutually normalizing
pair would be fused by the centralizer of the distinguished plane, which
already normalizes the layer. Sylow conjugacy inside its normalizer puts
the arbitrary pair in the chosen Sylow before applying that source result.

The natural SL₂ marking shows that the component centralizer of a nonzero
point is exactly T ∩ L. Hence its normalizer preserves the distinguished
plane, giving both normalizer identities of 6.2.9 for H = C_G(z). Even
characteristic supplies the generalized-Fitting clause of 6.2.10(1).
The Chapter 12 companion discharges E.6.1 and the central-line factorization.

Source: Aschbacher--Smith, 6.2.1, 6.2.3, 6.2.9--10, pp.680, 685.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

theorem local_normalizer_plane (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R)) :
    normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G) := by
  have hNM : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ M := by
    intro x hx
    obtain ⟨c, hc, m, hm, rfl⟩ := hfactor x hx
    exact M.mul_mem (hnatural.2.2.2.1 hc) hm.1
  exact (le_inf hNM le_rfl).trans
    (inf_normalizer_le_of_trivial_intersections hE.ti h.ZS_ne_bot inf_le_left)

theorem local_commuting_normalized (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hleft : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hright : (layer L R).map (MulAut.conj g).toMonoidHom ≤ normalizer (layer L R : Set G)) :
    ⁅layer L R, (layer L R).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hC : centralizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (B : Set G) :=
    (le_inf hnatural.2.2.2.1 le_rfl).trans
      (hE.localCentralizer_le_normalizer h.ZS_ne_bot inf_le_left)
  have hinside (k : G) (hk : B.map (MulAut.conj k).toMonoidHom ≤ (T : Subgroup G))
      (hmut : B ≤ normalizer (B.map (MulAut.conj k).toMonoidHom : Set G)) :
      ⁅B, B.map (MulAut.conj k).toMonoidHom⁆ = ⊥ := by
    by_contra hnon
    have hcomm : ⁅B, B.map (MulAut.conj k).toMonoidHom⁆ ≤
        B ⊓ B.map (MulAut.conj k).toMonoidHom :=
      le_inf (le_normalizer_iff_commutator_le_left.mp (hk.trans h.sylow_normalizes_layer))
        (le_normalizer_iff_commutator_le_right.mp hmut)
    obtain ⟨_, _, _, _, c, hc, he⟩ := mutual_conjugate_source_of_natural h hnat hE
      (natural_layer_rank_bounds h hnat hE).2.2 hfactor k hk hnon hcomm
    have heB : B.map (MulAut.conj k).toMonoidHom = B :=
      he.trans (mem_normalizer_iff_map_conj_eq.mp (hC hc))
    rw [heB] at hnon
    let := h.layer_elementary
    exact hnon (commutator_eq_bot_iff_le_centralizer.mpr B.le_centralizer)
  obtain ⟨c, hc, hcT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (normalizer (B : Set G)) A
    (h.sylow_normalizes_layer.trans (normalizer (B : Set G)).le_normalizer)
    ((T.isPGroup'.to_le h.layer_le_T).map _) hright
  have hcB : B.map (MulAut.conj c).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp hc
  have hcg : B.map (MulAut.conj (c * g)).toMonoidHom = A.map (MulAut.conj c).toMonoidHom :=
    (fusion_map_conj_mul B c g).symm
  have hmut : B ≤ normalizer (B.map (MulAut.conj (c * g)).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj c).toMonoidHom) hleft
    rwa [hcB, map_equiv_normalizer_eq, ← hcg] at hh
  have hz := hinside (c * g) (hcg.trans_le hcT) hmut
  have he : (⁅B, A⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom = ⊥ := by
    rw [map_commutator, hcB, ← hcg, hz]
  exact (map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp he

theorem local_involution_fitting_core (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    {z : G} (ho : orderOf z = 2) (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    generalizedFitting (centralizer ({z} : Set G)) = pCore 2 (centralizer ({z} : Set G)) := by
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
    (Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
      (isTwoLocal_involution_centralizer ho) hT))
omit [Finite G] in
theorem local_component_point_centralizer_isPGroup (hnat : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ layer L R) (hz1 : z ≠ 1) :
    IsPGroup 2 ((centralizer ({z} : Set G)).subgroupOf L) := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnat
  let q : L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let v : Fin 2 → F := (f ⟨z, hz⟩).toAdd
  have hv : v ≠ 0 := by
    intro he
    have he' : f ⟨z, hz⟩ = 1 := congrArg Multiplicative.ofAdd he
    exact hz1 (congrArg Subtype.val (f.injective (he'.trans (map_one f).symm)))
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hp := (Matrix.SL2.stabilizer_nonzero_isPGroup v hv).comap_of_ker_isPGroup q
    (hk ▸ (pCore_isPGroup : IsPGroup 2 (pCore 2 L)))
  apply hp.to_le
  intro l hl
  change Matrix.mulVec (q l).val v = v
  have he := hf l ⟨z, hz⟩
  have hc : (l : G) * z * (l : G)⁻¹ = z :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hl)
  rw [hc] at he
  have he' : f.symm (Multiplicative.ofAdd (Matrix.mulVec (q l).val v)) = ⟨z, hz⟩ :=
    Subtype.ext he
  have hh := congrArg (fun w => (f w).toAdd) he'
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using hh

theorem local_component_point_centralizer (h : Hypothesis611 κ T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (hz1 : z ≠ 1) :
    L ⊓ centralizer ({z} : Set G) = (T : Subgroup G) ⊓ L := by
  obtain ⟨S, hS⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes_L
  have hp := local_component_point_centralizer_isPGroup hnat hz.1 hz1
  have hle : (S : Subgroup L) ≤ (centralizer ({z} : Set G)).subgroupOf L := by
    rw [hS]
    intro l hl
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hz.2 l ⟨hl, l.property⟩)
  have he : (centralizer ({z} : Set G)).subgroupOf L = (S : Subgroup L) :=
    S.is_maximal' hp hle
  have hh := congrArg (fun U : Subgroup L => U.map L.subtype) he
  rw [hS, subgroupOf_map_subtype, subgroupOf_map_subtype] at hh
  simpa only [inf_comm] using hh

theorem local_plane_normalizer (h : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L R))
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2)
    (hplane : normalizer (ZS (T : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G)) :
    centralizer ({z} : Set G) ⊓ normalizer (ZS (T : Subgroup G) L R : Set G) =
      centralizer ({z} : Set G) ⊓ M := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at ho
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  have hCL := local_component_point_centralizer h hnat hz hz1
  apply le_antisymm (inf_le_inf_left _ (hplane.trans hE.normalizer_le))
  intro x hx
  have hxB : x ∈ normalizer (layer L R : Set G) :=
    inf_elementCentralizer_le_normalizer_of_trivial_intersections hE.ti hz.1 hz1 ⟨hx.2, hx.1⟩
  have hxL : x ∈ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal hx.2
  have hxC : x ∈ normalizer (centralizer ({z} : Set G) : Set G) :=
    (centralizer ({z} : Set G)).le_normalizer hx.1
  have hxS : x ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [← hCL]
    exact inf_normalizer_le_normalizer_inf ⟨hxL, hxC⟩
  exact ⟨hx.1, inf_normalizer_le_normalizer_inf
    ⟨hxB, normalizer_le_normalizer_centralizer _ hxS⟩⟩

/-- The layer-normalizer identity in source 6.2.9, for the literal centralizer. -/
theorem local_layer_normalizer
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L R))
    {z : G} (hz : z ∈ ZS (T : Subgroup G) L R) (ho : orderOf z = 2) :
    centralizer ({z} : Set G) ⊓ normalizer (layer L R : Set G) =
      centralizer ({z} : Set G) ⊓ M := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at ho
  apply le_antisymm (inf_le_inf_left _ hE.normalizer_le)
  intro x hx
  exact ⟨hx.1, inf_elementCentralizer_le_normalizer_of_trivial_intersections
    hE.ti hz.1 hz1 ⟨hx.2, hx.1⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
