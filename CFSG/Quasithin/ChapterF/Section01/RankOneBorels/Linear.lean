module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.MatrixBorel
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.Transport

/-!
# The concrete PSL₂ branch of F.1.3(1)

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed pp.259–260,
Remark F.1.2 and Lemma F.1.3(1). For every finite field of order 2ⁿ, n > 0,
every Sylow two-subgroup has a proper solvable normalizer containing all its
proper overgroups and splitting over an abelian odd-order torus.

The standard normalizer is the actual stabilizer of infinity on the
projective line. Elementary SL₂ matrices establish uniqueness of the proper
overgroup. In characteristic two the map SL₂ → PSL₂ is an isomorphism;
transport and Sylow conjugacy give the result for arbitrary Sylow subgroups.
No restriction n ≥ 2, choice of Galois-field presentation, or classification
of subgroups is required.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source.Linear

open BenderSuzuki.Converse Matrix

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The standard upper-unipotent Sylow in SL₂ satisfies the full output contract. -/
theorem standard_facts (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = 2 ^ n) :
    RankOneSylowFacts (SpecialLinearGroup.upperUnipotentSylow F 2) := by
  let S := SpecialLinearGroup.upperUnipotentSylow F 2
  have hS : (S : Subgroup (SL2 F)) = Unip F := unip_eq_upper.symm
  have hnS : Subgroup.normalizer (S : Set (SL2 F)) = Borel F := by
    change Subgroup.normalizer ((S : Subgroup (SL2 F)) : Set (SL2 F)) = _
    rw [hS, unip_normalizer]
  change RankOneSylowFacts S
  refine ⟨?_, ?_, twoCore_sylow_normalizer S, ?_, ?_⟩
  · rw [hnS]
    apply lt_top_iff_ne_top.mpr
    intro h
    exact weyl_notMem_Borel (F := F) (h ▸ Subgroup.mem_top _)
  · intro M hSM hM
    rw [hnS]
    exact proper_overgroup_le_borel M (hS ▸ hSM) hM
  · rw [hnS]
    exact borel_solvable
  · refine ⟨Torus F, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnS]
      exact Torus_le_Borel
    · have hc : Nat.card (Torus F) = Nat.card Fˣ := by
        rw [Torus_eq_range]
        exact (Nat.card_congr (MonoidHom.ofInjective
          (torHom_injective (F := F))).toEquiv).symm
      rw [hc, Nat.card_units, hcard, Nat.coprime_two_left]
      exact Nat.Even.sub_odd Nat.one_le_two_pow
        ((Nat.even_pow' (Nat.ne_of_gt hn)).mpr even_two) odd_one
    · rw [Torus_eq_range]
      infer_instance
    · rw [hS]
      exact Unip_disjoint_Torus
    · rw [hS, hnS]
      exact Unip_sup_Torus

/-- The image of the genuine upper-unipotent Sylow under SL₂ → PSL₂. -/
noncomputable def projectiveSylow : Sylow 2 (PSL2 F) :=
  (SpecialLinearGroup.upperUnipotentSylow F 2).mapSurjective
    (pi_surjective (F := F))

theorem projectiveSylow_coe : (projectiveSylow F : Subgroup (PSL2 F)) = PUnip F := by
  rw [projectiveSylow, Sylow.coe_mapSurjective,
    SpecialLinearGroup.coe_upperUnipotentSylow, ← unip_eq_upper]
  rfl

/-- The standard normalizer is the natural stabilizer of infinity. -/
theorem projectiveSylow_normalizer :
    Subgroup.normalizer (projectiveSylow F : Set (PSL2 F)) = PBorel F := by
  change Subgroup.normalizer ((projectiveSylow F : Subgroup (PSL2 F)) : Set (PSL2 F)) = _
  rw [projectiveSylow_coe, PUnip,
    ← Subgroup.map_normalizer_eq_of_bijective _ ⟨pi_injective, pi_surjective⟩,
    unip_normalizer, PBorel_eq_map]

set_option backward.isDefEq.respectTransparency false in
theorem projective_facts (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = 2 ^ n)
    (T : Sylow 2 (PSL2 F)) : RankOneSylowFacts T := by
  apply all_sylows (projectiveSylow F) _ T
  exact transport (MulEquiv.ofBijective (pi F) ⟨pi_injective, pi_surjective⟩)
    (SpecialLinearGroup.upperUnipotentSylow F 2) (projectiveSylow F) rfl
    (standard_facts F n hn hcard)

set_option backward.isDefEq.respectTransparency false in
/-- Every Sylow normalizer is an actual natural point stabilizer. -/
theorem normalizer_eq_point_stabilizer (T : Sylow 2 (PSL2 F)) :
    ∃ x : P1 F, Subgroup.normalizer (T : Set (PSL2 F)) =
      MulAction.stabilizer (PSL2 F) x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 F) (projectiveSylow F) T
  refine ⟨g • pInf F, ?_⟩
  have hmap : (projectiveSylow F : Subgroup (PSL2 F)).map
      (MulAut.conj g).toMonoidHom = (T : Subgroup (PSL2 F)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have he := Subgroup.map_equiv_normalizer_eq
    (projectiveSylow F : Subgroup (PSL2 F)) (MulAut.conj g)
  rw [hmap] at he
  simp only [Sylow.coe_coe] at he
  rw [← he, projectiveSylow_normalizer, PBorel,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]

end CFSG.Quasithin.ChapterF.Source.Linear

namespace CFSG.Quasithin.ChapterF.Source

/-- The concrete linear case of F.1.3(1), including n = 1. -/
theorem rankOneSylowFacts_psl2 (F : Type*) [Field F] [Finite F]
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = 2 ^ n)
    (T : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    RankOneSylowFacts T := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact Linear.projective_facts F n hn hcard T

end CFSG.Quasithin.ChapterF.Source
