module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOvergroupCoreDGS
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairResidual

/-!
# DGS residual and omega-center geometry in the original tensor pair

Under the temporary zero-core assumption of original 9.3.3, the two
original factors are exactly the two-residuals of the reduced DGS factors.
DGS (6.2)(a)--(b) therefore makes every normal subgroup escaping the
reduced core contain the original factor and cover its local Borel cosets.
The actual Ω₁(Z(S)) spans supply the elementary central-core geometry
and the centralizer alternatives used by the later critical-pair argument.
Core-freeness selects a noncentral endpoint with exactly its local core
as the kernel on this span.

At the tensor endpoint the reduced factor cannot itself be two-perfect:
its residual is the original L, whereas the opposite Sylow witness lies
outside L. Thus any subsequent DGS branch proving L S = O²(L S), as in
(10.10) for the nonbinary field, contradicts the original zero-core setup.
The source branch selection and its core movement are not assumed here
and remain to be proved; these statements do not yet prove 9.3.3.

Source: DGS85 Part II (6.1)--(6.2), pp.118--119, and (10.10), p.164;
Aschbacher--Smith, 9.3.3, p.733, and F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 SourceOldResidualOvergroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original factors are the literal reduced residuals. In particular,
normal subgroups escaping a reduced core contain the original factor. -/
theorem old_residual_core_zero_reduced_residuals
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    let P : Fin 2 → Subgroup G := ![L, (pResidual 2 H).map H.subtype]
    let S := commonTwo T L
    ∀ i,
      (pResidual 2 (P i ⊔ S : Subgroup G)).map (P i ⊔ S).subtype = P i ∧
      (∀ N : Subgroup G, N ≤ P i ⊔ S →
        P i ⊔ S ≤ normalizer (N : Set G) →
        N ≤ ChapterF.Source.twoCore (P i ⊔ S) ∨ P i ≤ N) ∧
      (∀ N : Subgroup G, N ≤ P i ⊔ S →
        P i ⊔ S ≤ normalizer (N : Set G) →
        ¬ N ≤ ChapterF.Source.twoCore (P i ⊔ S) →
        N ⊔ ChapterF.Source.borel (P i ⊔ S) S = P i ⊔ S) := by
  obtain ⟨hf, _, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  let P : Fin 2 → Subgroup G := ![L, (pResidual 2 H).map H.subtype]
  have hp (i : Fin 2) : Group.IsPerfect (P i) := by
    fin_cases i
    · exact Chapter1.mem_L_isPerfect D.maximal.1
    · exact Chapter1.mem_L_isPerfect
        (source_hstar_residual_mem_local_of_a5 hH eK)
  dsimp only
  intro i
  let : Group.IsPerfect (P i) := hp i
  have hr := hf.localJoin_residual_eq_of_perfect i
  refine ⟨hr, ?_, ?_⟩
  · intro N hN hnN
    obtain ⟨ei⟩ := hq i
    simpa only [hr] using hf.a5_localJoin_normal_dichotomy hn i ei N hN hnN
  · intro N hN hnN hQ
    exact hf.a5_localJoin_normal_sup_borel hn hq i N hN hnN hQ

/-- The genuine omega-center span has the DGS elementary core geometry,
with both original orientations and the same common two-subgroup. -/
theorem old_residual_core_zero_dgs_omega_geometry
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    let P : Fin 2 → Subgroup G := ![L, (pResidual 2 H).map H.subtype]
    let S := commonTwo T L
    let Z := Stellmacher.omegaOneCenterAmbient S
    ∀ i,
      let V := conjugateSpanBy Z (P i ⊔ S)
      V ≤ ChapterF.Source.twoCore (P i ⊔ S) ∧
      ChapterF.Source.twoCore (P i ⊔ S) ≤ centralizer (V : Set G) ∧
      IsElementaryAbelian 2 V ∧
      (((P i ⊔ S) ⊓ centralizer (V : Set G) = ChapterF.Source.twoCore (P i ⊔ S)) ∨
        (V = Z ∧ P i ⊔ S ≤ centralizer (Z : Set G))) := by
  obtain ⟨hf, _, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  dsimp only
  intro i
  obtain ⟨hv, hc, ha⟩ := hf.a5_localJoin_omega_span hn hq i
  exact ⟨hv, hc, ha, hf.a5_localJoin_omega_span_centralizer hn hq i⟩

/-- The original opposite-factor witness forces a nontrivial two-group
quotient of the reduced tensor endpoint. This is the obstruction to the
nonbinary DGS (10.10) residual identity in the zero-core branch. -/
theorem old_residual_core_zero_reduced_not_twoPerfect
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    ¬ IsPPerfect 2 (L ⊔ commonTwo T L : Subgroup G) := by
  intro hp
  have hr := (m.old_residual_core_zero_reduced_residuals
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero 0).1
  change (pResidual 2 (L ⊔ commonTwo T L : Subgroup G)).map
    (L ⊔ commonTwo T L).subtype = L at hr
  rw [(pResidual_eq_top_iff 2 _).mpr hp,
    ← MonoidHom.range_eq_map, range_subtype] at hr
  exact m.old_residual_common_sylow_not_le_component
    ((show commonTwo T L ≤ L ⊔ commonTwo T L from le_sup_right).trans_eq hr)

/-- The original zero-core configuration has a noncentral DGS endpoint
with the literal local two-core as its omega-span action kernel. -/
theorem old_residual_core_zero_dgs_noncentral_endpoint
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hBA : B ≤ A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (M₀ : Subgroup G)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hzero : pCore 2 M₀ = ⊥) :
    let P : Fin 2 → Subgroup G := ![L, (pResidual 2 H).map H.subtype]
    let S := commonTwo T L
    let Z := Stellmacher.omegaOneCenterAmbient S
    ∃ i : Fin 2,
      ¬ P i ⊔ S ≤ centralizer (Z : Set G) ∧
      (P i ⊔ S) ⊓ centralizer (conjugateSpanBy Z (P i ⊔ S) : Set G) =
        ChapterF.Source.twoCore (P i ⊔ S) := by
  obtain ⟨hf, _, hq, hn⟩ := m.old_residual_core_zero_rank_two_source
    hH eK A B hAB hA9 hBA hBK hB3 hAK M₀ hgen hzero
  exact hf.a5_exists_noncentral_omega_span hn hq

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
