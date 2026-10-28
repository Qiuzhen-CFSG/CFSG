module

public import Theory.SpecificGroups.Suzuki.TwoConjugateWitness.Geometry

/-!
# The complete Suzuki two-conjugate witness

The preceding root construction selects an internal conjugator and a genuine
nonsolvable generated subgroup. Recognition supplies its Suzuki model. The
prescribed Sylow intersection and its normalizer are preserved, and simplicity
makes that proper normalizer intersection core-free. Mapping the same Sylow
through the same recognition isomorphism identifies the original intersection
with a Borel of the recognized group.

Source: Aschbacher--Smith, E.2.7, printed p.218, Bender-group paragraph.
-/

public section
noncomputable section
namespace BenderSuzuki.MatrixGroups
open Subgroup

/-- An actual two-conjugate witness, retaining the original ambient Sylow and
normalizer, and one isomorphism identifying the subgroup and its Borel. -/
structure SuzukiTwoConjugateWitness {m : ℕ}
    (S : Sylow 2 (SuzukiMatrixGroup m)) (V : Subgroup (SuzukiMatrixGroup m)) where
  subgroup : Subgroup (SuzukiMatrixGroup m)
  le : V ≤ subgroup
  conjugator : subgroup
  generate : V.subgroupOf subgroup ⊔
    (V.subgroupOf subgroup).map (MulAut.conj conjugator).toMonoidHom = ⊤
  outside : (conjugator : SuzukiMatrixGroup m) ∉ normalizer (S : Set (SuzukiMatrixGroup m))
  sylow : Sylow 2 subgroup
  sylow_eq : (sylow : Subgroup subgroup).map subgroup.subtype = (S : Subgroup _) ⊓ subgroup
  normalizer_eq : (normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup =
    normalizer (sylow : Set subgroup)
  core_eq_bot : ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup).normalCore = ⊥
  parameter : ℕ
  positive : 0 < parameter
  degree_dvd : 2 * parameter + 1 ∣ 2 * m + 1
  equiv : subgroup ≃* SuzukiMatrixGroup parameter
  borel_eq : ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup).map equiv.toMonoidHom =
    normalizer ((sylow : Subgroup subgroup).map equiv.toMonoidHom : Set (SuzukiMatrixGroup parameter))
  borel_conjugate : ∃ c : SuzukiMatrixGroup parameter,
    ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup).map equiv.toMonoidHom =
      (SuzukiBorelSubgroup parameter).map (MulAut.conj c).toMonoidHom

private theorem pair_map {G D : Type*} [Group G] [Group D]
    (f : G →* D) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup, map_map, map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]

private theorem core_eq_bot_of_not_mem {G : Type*} [Group G] [IsSimpleGroup G]
    (M : Subgroup G) (x : G) (hx : x ∉ M) : M.normalCore = ⊥ := by
  rcases M.normalCore_normal.eq_bot_or_eq_top with he | he
  · exact he
  · have hxC : x ∈ M.normalCore := by rw [he]; exact mem_top _
    exact False.elim (hx (M.normalCore_le hxC))

/-- Every elementary subgroup of order greater than two in the prescribed
Suzuki Sylow subgroup yields the full internal witness. No subgroup model,
subfield, Sylow conclusion, or witness is assumed. -/
theorem suzuki_twoConjugateWitness {m : ℕ} (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m))
    (V : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hcard : 2 < Nat.card V) :
    Nonempty (SuzukiTwoConjugateWitness S V) := by
  obtain ⟨g, hg, hgN, hsol⟩ := suzuki_exists_internal_elementary_pair hm S V hVS hcard
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  have hVI : V ≤ I := le_sup_left
  have hne : V ≠ ⊥ := by intro h; rw [h, card_bot] at hcard; omega
  obtain ⟨⟨P, hP⟩, hN⟩ := suzuki_subgroup_sylow_normalizer hm S I V hVS hVI hne
  have hNP : (normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf I =
      normalizer (P : Set I) := by rw [← P.coe_coe, hP]; exact hN.symm
  obtain ⟨k, hk, ⟨e⟩⟩ := External.suzukiSubgroup_exists_mulEquiv_of_not_isSolvable hm I hsol
  have hdiv : 2 * k + 1 ∣ 2 * m + 1 := by
    apply suzukiMatrixGroup_degree_dvd_of_card_dvd hk hm
    rw [← Nat.card_congr e.toEquiv]
    exact I.card_subgroup_dvd_card
  let : IsSimpleGroup (SuzukiMatrixGroup k) := (External.huppert_blackburn_XI_3_6 k hk).1
  let : IsSimpleGroup I := e.isSimpleGroup
  let M := (normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf I
  have hcore : M.normalCore = ⊥ :=
    core_eq_bot_of_not_mem M (⟨g, hg⟩ : I) hgN
  let gg : I := ⟨g, hg⟩
  have hgen : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj gg).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [pair_map, map_subgroupOf_eq_of_le hVI, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hB : M.map e.toMonoidHom = normalizer
      ((P : Subgroup I).map e.toMonoidHom : Set (SuzukiMatrixGroup k)) := by
    rw [show M = normalizer (P : Set I) from hNP, ← P.coe_coe,
      map_normalizer_eq_of_bijective (P : Subgroup I) (f := e.toMonoidHom) e.bijective]
  have hBc : ∃ c : SuzukiMatrixGroup k, M.map e.toMonoidHom =
      (SuzukiBorelSubgroup k).map (MulAut.conj c).toMonoidHom := by
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow k hk
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup k) R Q
    have hQ : (P : Subgroup I).map e.toMonoidHom =
        (SuzukiRootSubgroup k).map (MulAut.conj c).toMonoidHom := by
      change (Q : Subgroup (SuzukiMatrixGroup k)) = _
      rw [← hR, ← hc]
      rfl
    refine ⟨c, ?_⟩
    rw [hB, hQ, ← map_normalizer_eq_of_bijective _ (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).bijective,
      suzukiRootSubgroup_normalizer k hk]
  refine ⟨⟨I, hVI, gg, hgen, hgN, P, ?_, hNP, hcore, k, hk, hdiv, e, hB, hBc⟩⟩
  rw [hP, subgroupOf_map_subtype]

end BenderSuzuki.MatrixGroups
end
