module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The binary local centralizer and the zero-distance core

We pull Z_alpha back through the actual injection of M into its holomorph
amalgam. Its centralizer contains O₂(M). Simplicity of the marked SL₃(2)
quotient makes that centralizer either O₂(M) or M; the latter would make
Omega-one of Z(R) normal in M, contrary to MS3 when R is nontrivial.

At distance zero Z_alpha itself has nontrivial normal image in SL₃(2).
The quotient by its pullback is consequently a two-group, so the two-residual
lies in that pullback and centralizes O₂(M). Thus [Q_alpha,Ltilde_alpha]=1.
This proves the core clause of (3.1), without invoking any module classification.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.1)--(2.2), (3.1), printed pp.855--857, 859--860. No assumption of
odd index for the reduced edge group or finiteness of the amalgam is used.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

@[expose] noncomputable def localZ (R : Subgroup M) : Subgroup M := (Z R (alpha R)).comap (embedM R)

omit [Finite M] in
theorem localZ_normal : (localZ R).Normal := by
  constructor
  intro z hz m
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  have h := (mem_normalizer_iff.mp (Z_normalized R (alpha R) hm) (embedM R z)).mp hz
  simpa only [localZ, mem_comap, map_mul, map_inv] using h

omit [Finite M] in
theorem localZ_map : (localZ R).map (embedM R) = Z R (alpha R) := by
  rw [localZ, map_comap_eq]
  apply inf_eq_right.mpr
  change Z R (alpha R) ≤ Mbar R
  rw [← stabilizer_m_base]
  exact Z_le_stabilizer R (alpha R)

theorem LocalSource.core_le_localZ_centralizer (source : LocalSource L R) :
    pCore 2 M ≤ centralizer (localZ R : Set M) := by
  intro q hq z hz
  apply embedM_injective R
  simp only [map_mul]
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q R (alpha R) rfl))
  exact hc (by rw [Q_alpha R source.two_group source.core_le]; exact mem_map_of_mem _ hq)
    (embedM R z) hz

omit [Finite M] in
theorem LocalSource.residual_le_of_image_top (source : LocalSource L R)
    (A : Subgroup M) [A.Normal] (hA : A.map source.projection = ⊤) : L ≤ A := by
  have hAQ : A ⊔ pCore 2 M = ⊤ := by
    have h := congrArg (fun B => B.comap source.projection) hA
    simpa only [comap_map_eq, source.projection_kernel, comap_top] using h
  let q := QuotientGroup.mk' A
  have hsurj : Function.Surjective (q.comp (pCore 2 M).subtype) := by
    intro x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective A x
    obtain ⟨a, ha, n, hn, rfl⟩ := mem_sup_of_normal_left.mp (show m ∈ A ⊔ pCore 2 M by
      rw [hAQ]; trivial)
    refine ⟨⟨n, hn⟩, ?_⟩
    simp [q, ha]
  rw [← source.residual]
  exact sInf_le ⟨inferInstance, pCore_isPGroup.of_surjective _ hsurj⟩

/-- The binary core assertion of MS93 (3.1), on the actual amalgam carrier. -/
theorem LocalSource.core_eq_bot_of_b_zero (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 0) : core R (alpha R) = ⊥ := by
  let := localZ_normal (R := R)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : ((localZ R).map source.projection).Normal :=
    (inferInstance : (localZ R).Normal).map _ source.projection_surjective
  have hnot : ¬ localZ R ≤ pCore 2 M := by
    obtain ⟨a', hd, hne⟩ := criticalPair_exists R (alpha R)
      (geometry.exists_critical (alpha R) rfl)
    have ha' : alpha R = a' := (cosetGraph_connected R).dist_eq_zero_iff.mp (hd.trans hb)
    subst a'
    intro hle
    apply hne
    rw [← localZ_map, Q_alpha R source.two_group source.core_le]
    exact map_mono hle
  have htop : (localZ R).map source.projection = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (hnot (by simpa only [source.projection_kernel] using (Subgroup.map_eq_bot_iff _).mp h)).elim
    · exact h
  have hL := source.residual_le_of_image_top (localZ R) htop
  rw [core_alpha R source.two_group source.core_le source.residual,
    (commutator_eq_bot_iff_le_centralizer.mpr
      (source.core_le_localZ_centralizer.trans (centralizer_le hL))), Subgroup.map_bot]

theorem omegaCenter_le_localZ : omegaCenter R ≤ localZ R := by
  intro x hx
  have hm : embedM R x ∈ edgeOmega R (beta R) := by
    rw [edgeOmega, Q_beta, omegaCenter_map R (embedM R) (embedM_injective R)]
    exact mem_map_of_mem _ hx
  show embedM R x ∈ Z R (alpha R)
  rw [Z, if_pos (show color R (alpha R) = false from rfl)]
  have hle : edgeOmega R (beta R) ≤ Z R (alpha R) := by
    rw [Z, if_pos (show color R (alpha R) = false from rfl)]
    exact le_iSup_of_le (beta R) (le_iSup_of_le (base_adjacent R) le_rfl)
  exact hle hm

/-- MS3 excludes a central omega-center of R; simplicity then gives the exact kernel. -/
theorem LocalSource.localZ_centralizer (source : LocalSource L R) (hR : R ≠ ⊥) :
    centralizer (localZ R : Set M) = pCore 2 M := by
  let := localZ_normal (R := R)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let A := centralizer (localZ R : Set M)
  have hnorm : (A.map source.projection).Normal :=
    (inferInstance : A.Normal).map _ source.projection_surjective
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact le_antisymm (by simpa only [source.projection_kernel] using
      (Subgroup.map_eq_bot_iff _).mp h) source.core_le_localZ_centralizer
  · have hAtop : A = ⊤ := by
      have hh := congrArg (fun B => B.comap source.projection) h
      have hQA : pCore 2 M ≤ A := source.core_le_localZ_centralizer
      simpa only [comap_map_eq, source.projection_kernel, comap_top,
        sup_eq_left.mpr hQA] using hh
    let D : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
    let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
    have hDnorm : (D.map R.subtype).Normal := by
      constructor
      intro d hd m
      have hdZ : d ∈ localZ R := omegaCenter_le_localZ hd
      have hm : m ∈ A := hAtop ▸ mem_top m
      have hcomm := hm d hdZ
      have heq : m * d * m⁻¹ = d := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rwa [heq]
    have hDbot := source.characteristic.eq_bot_of_normal D hDnorm
    let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR
    exact (omega_center_ne_bot source.two_group hDbot).elim

theorem Geometry.radical_ne_bot (geometry : Geometry R) : R ≠ ⊥ := by
  intro hR
  have hQ : Q R (beta R) = ⊥ := by rw [Q_beta, hR, Subgroup.map_bot]
  have hZ : Z R (alpha R) = ⊥ := by
    apply le_bot_iff.mp
    rw [Z, if_pos (show color R (alpha R) = false from rfl)]
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    obtain ⟨g, hg, heq⟩ := stabilizer_transitive_neighbors R (alpha R)
      (base_adjacent R) ht
    change act R g (beta R) = t at heq
    have hQ' := Q_act R g (beta R)
    rw [heq, hQ, Subgroup.map_bot] at hQ'
    exact (omegaCenter_le (Q R t)).trans hQ'.le
  obtain ⟨a', _, hn⟩ := criticalPair_exists R (alpha R)
    (geometry.exists_critical (alpha R) rfl)
  exact hn (hZ ▸ bot_le)

theorem LocalSource.C_alpha (source : LocalSource L R) (hR : R ≠ ⊥) :
    C R (alpha R) = Q R (alpha R) := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    have hxM : x ∈ Mbar R := (stabilizer_m_base R) ▸ hx
    obtain ⟨m, rfl⟩ := hxM
    have hm : m ∈ centralizer (localZ R : Set M) := by
      intro z hz
      apply embedM_injective R
      simpa only [map_mul] using hc (embedM R z) hz
    rw [source.localZ_centralizer hR] at hm
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ hm
  · intro x hx
    exact ⟨hx.1, le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)) hx⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
