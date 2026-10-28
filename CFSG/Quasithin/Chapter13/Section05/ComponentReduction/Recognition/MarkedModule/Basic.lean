module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.ComponentAction
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Initial
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.CommutingPerfectRank
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Relative normality, ambient generation, and the marked stabilizer in 13.5.21

The marked noncentral L₁* forces its normalizer to preserve the ordinary
component K*: distinct components commute. Three distinct conjugates of
K* would give odd prime rank at least three. Hence its orbit has length at
most two, and Sylow normalization rules out length two. The C-component
correspondence lifts this to normality of the original K inside H.

The earlier identity V₃=[V,L₁] gives [V₃,L₁]=V₃ by two-residual
commutator idempotence. Its H-closure consequently satisfies U_H=[U_H,K]
in the ambient group. Two-perfectness lifts K*=[K*,V*] to K=[K,V].
Since [Q_H,V]≤V₃, the normal centralizer of Q_H/U_H contains V and
therefore K=[K,V]. Together these give the original equality U_H=[Q_H,K].
The quotient and linear versions retain the original tilde map and
Action.starRepresentation; no splitting is used.

The literal L₁*T* preserves Action.seedSpace. It is its own two-residual
supplemented by T*, and is not a two-group. Thus a concrete upper bound
three on the marked stabilizer's relative index already gives index
exactly three, the exact product equality, and its embedded two-residual.
The bound is still an explicit model obligation.

These are conditional source deductions, not all of Lemma 13.5.21.
The source assembly retains the genuine 13.5 setup and full proper-K
input, and supplies its strongly quasithin H*, earlier seed identity,
index-two seed, nonabelian U_H, marked local action, and catalogue
containment L₁≤K. Recognition.Selected is used unchanged. Uniqueness
of the noncentral chief factor, its natural central quotient, the concrete
index bound, and Ũ_H=[Ũ_H,L₁] remain separate obligations.

The orbit argument specializes the proof in ChapterA/Section03/
SQTKStructure/ComponentOrbitBound to ordinary components, whose commutation
needs no further A.3 structural input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.5.21(3),(5),(6), printed p.924 (PDF p.941), with the seed
identity from the earlier 13.5 geometry and the orbit argument in 1.2.1(3).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule
open Section08.Source
variable {G : Type*} [Group G] [Finite G]

private theorem component_orbit_bound {B : Subgroup G} (hB : IsComponent G B)
    (hG : IsStronglyQuasithin G) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 := by
  classical
  by_cases hn : B.Normal
  · exact Or.inl hn
  have hex : ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≠ B := by
    by_contra! h
    exact hn (normal_iff_map_conj_eq.mpr h)
  obtain ⟨g, hg⟩ := hex
  let C := B.map (MulAut.conj g).toMonoidHom
  have hC : IsComponent G C := hB.map_conj g
  have hBC : B ≠ C := hg.symm
  have hcomm (D E : Subgroup G) (hD : IsComponent G D) (hE : IsComponent G E)
      (hne : D ≠ E) : D ≤ centralizer (E : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hE hne)
  have hpair (t : G) :
      B.map (MulAut.conj t).toMonoidHom = B ∨
        B.map (MulAut.conj t).toMonoidHom = C := by
    let D := B.map (MulAut.conj t).toMonoidHom
    by_cases hDB : D = B
    · exact Or.inl hDB
    by_cases hDC : D = C
    · exact Or.inr hDC
    have hD : IsComponent G D := hB.map_conj t
    have h₀₁ := hcomm B C hB hC hBC
    have h₀₂ := hcomm B D hB hD (fun he => hDB he.symm)
    have h₁₂ := hcomm C D hC hD (fun he => hDC he.symm)
    let := hB.2
    let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
    let f₁ : B →* G := (MulAut.conj g).toMonoidHom.comp B.subtype
    let f₂ : B →* G := (MulAut.conj t).toMonoidHom.comp B.subtype
    obtain ⟨p, hp, ho, hr⟩ :=
      CommutingPerfectRank.exists_odd_prime_rank_three_of_commuting_perfect
        B.subtype f₁ f₂ B.subtype_injective
        ((MulAut.conj g).injective.comp B.subtype_injective)
        ((MulAut.conj t).injective.comp B.subtype_injective)
        (fun x y => (h₀₁ x.property (f₁ y)
          (mem_map_of_mem (MulAut.conj g).toMonoidHom y.property)).symm)
        (fun x y => (h₀₂ x.property (f₂ y)
          (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm)
        (fun x y => (h₁₂ (mem_map_of_mem (MulAut.conj g).toMonoidHom x.property)
          (f₂ y) (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm)
    have hu := hG p hp ho
    omega
  have hsub : (Set.range fun g : G => B.map (MulAut.conj g).toMonoidHom) ⊆ {B, C} := by
    rintro _ ⟨t, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair t
  have hi : (normalizer (B : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hBC)
  have hnt : normalizer (B : Set G) ≠ ⊤ :=
    fun h => hn (normalizer_eq_top_iff.mp h)
  have hlo := (normalizer (B : Set G)).one_lt_index_of_ne_top hnt
  exact Or.inr (by omega)

omit [Finite G] in
private theorem component_normalizer_of_marked_subgroup {B A : Subgroup G}
    (hB : IsComponent G B) (hAB : A ≤ B) (hm : ⁅B, A⁆ ≠ ⊥) :
    normalizer (A : Set G) ≤ normalizer (B : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hn
  have hAconj : A ≤ B.map (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [← mem_normalizer_iff_map_conj_eq.mp hg]
    exact map_mono hAB
  have hc := hB.commutator_eq_bot_of_ne (hB.map_conj g) (fun he => hn he.symm)
  exact hm (bot_unique ((commutator_mono le_rfl hAconj).trans_eq hc))

variable {D : ChapterF.Section09.Setup G} {K : Subgroup G}

/-- The original Sylow normalizes K because it preserves the marked noncentral L₁. -/
theorem sylow_normalizes (s : Selected D K) (h : D.Hypothesis)
    (hLK : D.L₁ ≤ K) (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥) :
    (D.T : Subgroup G) ≤ normalizer (K : Set G) := by
  apply s.normalizes_of_star _ h.T_le_H
  apply le_trans _ (component_normalizer_of_marked_subgroup s.star_component
    (map_mono (comap_mono hLK)) hm)
  have hn : (D.T : Subgroup G).subgroupOf D.H ≤
      normalizer (D.L₁.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq (le_sup_left.trans h.local_le)]
    exact comap_mono (local_residual_normalized D h)
  exact (map_mono hn).trans (le_normalizer_map _)

/-- The orbit bound and Sylow normalization prove normality inside H. -/
theorem normal_in_H (s : Selected D K) (h : D.Hypothesis)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hLK : D.L₁ ≤ K) (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥) :
    (K.subgroupOf D.H).Normal := by
  have hTK := sylow_normalizes s h hLK hm
  have hn : (D.T : Subgroup G).subgroupOf D.H ≤
      normalizer (K.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq s.le_H]
    exact comap_mono hTK
  have hSN : (starSylow D h : Subgroup (Hstar D.H)) ≤
      normalizer (starImage D.H K : Set (Hstar D.H)) :=
    (map_mono hn).trans (le_normalizer_map _)
  have hnormal : (starImage D.H K).Normal := by
    rcases component_orbit_bound s.star_component hSQ with hnormal | hi
    · exact hnormal
    · have hd := index_dvd_of_le hSN
      rw [hi] at hd
      exact ((starSylow D h).not_dvd_index hd).elim
  let : Group.IsNilpotent (pCore 2 D.H) := pCore_isNilpotent
  exact cComponent_normal_of_quotient_normal s.ccomponent (pCore 2 D.H) hnormal

/-- Ambient generation is established before passing to U_H/V₁. -/
theorem ambient_generation (s : Selected D K) (h : D.Hypothesis)
    (hLK : D.L₁ ≤ K) (hn : (K.subgroupOf D.H).Normal)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆) : D.UH = ⁅D.UH, K⁆ :=
  conjugateSpanBy_eq_commutator_of_seed D.Vplus D.H K D.L₁ s.le_H
    ((normal_subgroupOf_iff_le_normalizer s.le_H).mp hn) hLK
    (NormalBranch.seed_commutator h hseed).symm

/-- The literal ambient quotient retains the full K-commutator. -/
theorem tilde_generation (s : Selected D K) (h : D.Hypothesis)
    (hLK : D.L₁ ≤ K) (hn : (K.subgroupOf D.H).Normal)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde K⁆ := by
  have hU := Action.UH_le_ambient D h
  have hK : K ≤ D.g2.G₁ := s.le_H.trans h.g2_hypothesis.H_le
  have hc : ⁅D.UH.subgroupOf D.g2.G₁, K.subgroupOf D.g2.G₁⁆ =
      D.UH.subgroupOf D.g2.G₁ := by
    apply map_injective D.g2.G₁.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hU,
      map_subgroupOf_eq_of_le hK, ← ambient_generation s h hLK hn hseed]
  change (D.UH.subgroupOf D.g2.G₁).map _ =
    ⁅(D.UH.subgroupOf D.g2.G₁).map _, (K.subgroupOf D.g2.G₁).map _⁆
  rw [← map_commutator, hc]

private theorem perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- Two-perfectness removes the two-core error in the starred commutator. -/
theorem component_ambient_commutator (s : Selected D K) (h : D.Hypothesis)
    (hn : D.V ≤ normalizer (K : Set G))
    (hc : ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K) :
    K = ⁅K, D.V⁆ := by
  let := s.ccomponent.perfect
  have hn' : D.V.subgroupOf D.H ≤ normalizer (K.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq s.le_H]
    exact comap_mono hn
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 D.H)).ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := eq_commutator_of_isPPerfect_of_map_eq (K.subgroupOf D.H)
    (D.V.subgroupOf D.H) perfect_twoPerfect hn'
    (QuotientGroup.mk' (pCore 2 D.H)) hk hc.symm
  have hm := congrArg (map D.H.subtype) he
  simpa only [map_commutator, map_subgroupOf_eq_of_le s.le_H,
    map_subgroupOf_eq_of_le h.V_le_H] using hm

/-- The seed/core intersection bounds [Q_H,V] in the original ambient group. -/
theorem core_actor_commutator_le_seed (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH) :
    ⁅D.QH, D.V⁆ ≤ D.Vplus := by
  rw [← LocalGeometry.seed_eq_intersection_core h hindex hU]
  exact le_inf (le_normalizer_iff_commutator_le_right.mp
    (h.QH_le_T.trans h.T_normalizes_V))
    (le_normalizer_iff_commutator_le_left.mp (h.V_le_H.trans
      (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D))))

/-- The normal centralizer of Q_H/U_H absorbs [K,V]=K, giving the upper bound. -/
theorem core_component_commutator_le (s : Selected D K) (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hc : K = ⁅K, D.V⁆) : ⁅D.QH, K⁆ ≤ D.UH := by
  let U := D.UH.subgroupOf D.H
  let Q := D.QH.subgroupOf D.H
  let V := D.V.subgroupOf D.H
  let B := K.subgroupOf D.H
  let : U.Normal := h.UH_normal
  let : Q.Normal := h.duality_inputs.1
  let C := centralizerModulo (⊤ : Subgroup D.H) Q U
  let : C.Normal := centralizerModulo_top_normal Q U
  have hVC : V ≤ C := by
    intro v hv
    apply mem_centralizerModulo_iff.mpr
    exact ⟨mem_top _, fun q hq => le_conjugateSpanBy D.Vplus D.H
      (core_actor_commutator_le_seed h hindex hU (commutator_mem_commutator hq hv))⟩
  have he : B = ⁅B, V⁆ := by
    apply map_injective D.H.subtype_injective
    simpa only [B, V, map_commutator, map_subgroupOf_eq_of_le s.le_H,
      map_subgroupOf_eq_of_le h.V_le_H] using hc
  have hBC : B ≤ C := by
    rw [he]
    exact (commutator_mono le_rfl hVC).trans (commutator_le_right B C)
  apply commutator_le.mpr
  intro q hq k hk
  exact (mem_centralizerModulo_iff.mp (hBC (show (⟨k, s.le_H hk⟩ : D.H) ∈ B from hk))).2
    ⟨q, pCoreIn_le 2 D.H hq⟩ hq

/-- Clause (5)'s ambient equality, without a quotient-level lifting gap. -/
theorem ambient_core_equality (s : Selected D K) (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hLK : D.L₁ ≤ K) (hn : (K.subgroupOf D.H).Normal)
    (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hc : ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K) :
    D.UH = ⁅D.QH, K⁆ := by
  have hnV : D.V ≤ normalizer (K : Set G) := h.V_le_H.trans
    ((normal_subgroupOf_iff_le_normalizer s.le_H).mp hn)
  refine le_antisymm ?_ (core_component_commutator_le s h hindex hU
    (component_ambient_commutator s h hnV hc))
  exact (ambient_generation s h hLK hn hseed).le.trans
    (commutator_mono h.UH_le_QH le_rfl)



/-- Source application of the orbit and ambient lifting arguments. The source
configuration supplies the two nontrivial starred actions, and the catalogue
supplies L₁ ≤ K. The seed identity is the earlier 13.5 geometry. -/
theorem group_conclusions (s : Selected D K) (h : D.Hypothesis)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hLK : D.L₁ ≤ K) (hseed : D.Vplus = ⁅D.V, D.L₁⁆)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hc : ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K) :
    (K.subgroupOf D.H).Normal ∧ D.UH = ⁅D.UH, K⁆ ∧
      D.tilde D.UH = ⁅D.tilde D.UH, D.tilde K⁆ ∧ D.UH = ⁅D.QH, K⁆ := by
  have hn := normal_in_H s h hSQ hLK hm
  exact ⟨hn, ambient_generation s h hLK hn hseed,
    tilde_generation s h hLK hn hseed,
    ambient_core_equality s h hindex hU hLK hn hseed hc⟩

section Linear
open Representation.BinaryOffender
variable (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The literal L₁*T* in H/O₂(H). -/
noncomputable def localStar : Subgroup (Hstar D.H) :=
  starImage D.H D.L₁ ⊔ starImage D.H D.T

/-- The stabilizer of the original V₃/V₁ inside K*T*, before choosing coordinates. -/
noncomputable def markedParabolic (K : Subgroup G) : Subgroup (Hstar D.H) :=
  (starImage D.H K ⊔ starImage D.H D.T) ⊓
    subspaceStabilizer (Action.starRepresentation D h) (Action.seedSpace D)

/-- Ambient full commutators give full displacement in the faithful binary action. -/
theorem linear_generation (s : Selected D K) (hLK : D.L₁ ≤ K)
    (hn : (K.subgroupOf D.H).Normal) (hseed : D.Vplus = ⁅D.V, D.L₁⁆) :
    subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K) = ⊤ := by
  let C := subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K)
  let π := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  let J : Subgroup D.UH :=
    (Subgroup.toAddSubgroup.symm C.toAddSubgroup).comap π
  let B := J.map D.UH.subtype
  have hUB : D.UH ≤ B := by
    rw [ambient_generation s h hLK hn hseed]
    apply commutator_le.mpr
    intro u hu k hk
    let uU : D.UH := ⟨u, hu⟩
    let kH : D.H := ⟨k, s.le_H hk⟩
    have hmem : ⁅u, k⁆ ∈ D.UH :=
      (ambient_generation s h hLK hn hseed).ge (commutator_mem_commutator hu hk)
    refine ⟨⟨⁅u, k⁆, hmem⟩, ?_, rfl⟩
    change Additive.ofMul (π ⟨⁅u, k⁆, hmem⟩) ∈ C
    have hd : Action.starRepresentation D h (QuotientGroup.mk' (pCore 2 D.H) kH)
        (Additive.ofMul (π uU⁻¹)) - Additive.ofMul (π uU⁻¹) ∈ C :=
      Submodule.subset_span ⟨_, mem_map_of_mem _ hk, _, Submodule.mem_top, rfl⟩
    rw [Action.starRepresentation_apply, sub_eq_neg_add] at hd
    change Additive.ofMul ((π uU⁻¹)⁻¹ * π _) ∈ C at hd
    rw [← map_inv, ← map_mul] at hd
    convert hd using 1
    congr 2
    apply Subtype.ext
    simp only [uU, kH, coe_mul, coe_inv, inv_inv, commutatorElement_def, mul_assoc]
  apply top_unique
  intro w _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) w.toMul
  obtain ⟨v, hv, hve⟩ := hUB u.property
  have he : v = u := Subtype.ext hve
  subst v
  change Additive.ofMul (π u) ∈ C at hv
  simpa [C, π, hu] using hv

/-- The earlier L₁T-normalization acts on the actual quotient seed. -/
theorem localStar_stabilizes_seed :
    localStar D ≤ subspaceStabilizer (Action.starRepresentation D h) (Action.seedSpace D) := by
  have hlocal : starImage D.H (D.L₁ ⊔ (D.T : Subgroup G)) ≤
      subspaceStabilizer (Action.starRepresentation D h) (Action.seedSpace D) := by
    apply le_subspaceStabilizer
    rintro x ⟨a, ha, rfl⟩ w hw
    obtain ⟨u, hu, he⟩ := hw
    have hew : Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) = w :=
      congrArg Additive.ofMul he
    rw [← hew, Action.starRepresentation_apply]
    refine ⟨⟨a.val * u.val * a.val⁻¹,
      le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
        a.val a.property u.val u.property⟩, ?_, rfl⟩
    exact le_normalizer_iff.mp h.local_normalizes a ha u hu
  exact (sup_le (map_mono (comap_mono le_sup_left))
    (map_mono (comap_mono le_sup_right))).trans hlocal

/-- One inclusion of the required marked stabilizer equality uses only the source setup. -/
theorem localStar_le_markedParabolic (hLK : D.L₁ ≤ K) :
    localStar D ≤ markedParabolic D h K :=
  le_inf (sup_le_sup (map_mono (comap_mono hLK)) le_rfl)
    (localStar_stabilizes_seed D h)

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- The local residual is still two-perfect under the literal star map. -/
theorem localStar_residual_twoPerfect : IsPPerfect 2 (starImage D.H D.L₁) := by
  let e := subgroupOfEquivOfLe (show D.L₁ ≤ D.H from le_sup_left.trans h.local_le)
  have hp := (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)).of_surjective
    e.symm.toMonoidHom e.symm.surjective
  let q := QuotientGroup.mk' (pCore 2 D.H)
  exact hp.of_surjective (q.subgroupMap (D.L₁.subgroupOf D.H))
    (q.subgroupMap_surjective _)

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- The marked noncentral residual cannot disappear into the Sylow two-group. -/
theorem localStar_not_le_sylow
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥) :
    ¬ localStar D ≤ starImage D.H D.T := by
  intro hle
  have hLS : starImage D.H D.L₁ ≤ (starSylow D h : Subgroup (Hstar D.H)) :=
    le_sup_left.trans hle
  let A := starImage D.H D.L₁
  have hp : IsPGroup 2 A := (starSylow D h).isPGroup'.to_le hLS
  have he := (localStar_residual_twoPerfect D h).hom_eq_one_of_isPGroup hp (MonoidHom.id A)
  have hbot : A = ⊥ := by
    apply bot_unique
    intro a ha
    have ha1 := congrArg (fun f : A →* A => (f ⟨a, ha⟩ : Hstar D.H)) he
    exact ha1
  apply hm
  change ⁅starImage D.H K, A⁆ = ⊥
  rw [hbot, commutator_bot_right]

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- The actual Sylow image normalizes the actual local residual image. -/
theorem starSylow_normalizes_local :
    starImage D.H D.T ≤ normalizer (starImage D.H D.L₁ : Set (Hstar D.H)) := by
  have hn : (D.T : Subgroup G).subgroupOf D.H ≤
      normalizer (D.L₁.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq (le_sup_left.trans h.local_le)]
    exact comap_mono (local_residual_normalized D h)
  exact (map_mono hn).trans (le_normalizer_map _)

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- This join is precisely the source setwise product L₁*T*. -/
theorem localStar_product :
    (localStar D : Set (Hstar D.H)) =
      Set.image2 (· * ·) (starImage D.H D.L₁ : Set (Hstar D.H))
        (starImage D.H D.T : Set (Hstar D.H)) :=
  coe_mul_of_right_le_normalizer_left _ _ (starSylow_normalizes_local D h)

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
/-- No extra parabolic-residual identification is required after identifying its product. -/
theorem localStar_twoResidual :
    (pResidual 2 (localStar D)).map (localStar D).subtype = starImage D.H D.L₁ :=
  embedded_pResidual_join_pGroup _ _ (localStar_residual_twoPerfect D h)
    (starSylow D h).isPGroup' (starSylow_normalizes_local D h)

/-- An index-three calculation in the concrete module identifies the exact local product. -/
theorem localStar_eq_markedParabolic_of_index_three
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hi : (starImage D.H D.T).relIndex (markedParabolic D h K) = 3) :
    localStar D = markedParabolic D h K := by
  have hLP := localStar_le_markedParabolic D h hLK
  have hSL : starImage D.H D.T ≤ localStar D := le_sup_right
  have he := relIndex_mul_relIndex (starImage D.H D.T) (localStar D)
    (markedParabolic D h K) hSL hLP
  rw [hi] at he
  have hd : (localStar D).relIndex (markedParabolic D h K) ∣ 3 :=
    ⟨_, by simpa only [mul_comm] using he.symm⟩
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with hone | hthree
  · exact le_antisymm hLP (relIndex_eq_one.mp hone)
  · rw [hthree] at he
    have hSLone : (starImage D.H D.T).relIndex (localStar D) = 1 := by omega
    exact (localStar_not_le_sylow D h hm (relIndex_eq_one.mp hSLone)).elim

/-- A bound from a concrete module already gives the exact index, stabilizer,
and embedded residual required by the source. The Sylow index is odd. -/
theorem marked_parabolic_of_index_bound
    (hLK : D.L₁ ≤ K)
    (hm : ⁅starImage D.H K, starImage D.H D.L₁⁆ ≠ ⊥)
    (hi : (starImage D.H D.T).relIndex (markedParabolic D h K) ≤ 3) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 ∧
      localStar D = markedParabolic D h K ∧
      (pResidual 2 (markedParabolic D h K)).map
        (markedParabolic D h K).subtype = starImage D.H D.L₁ := by
  have hLP := localStar_le_markedParabolic D h hLK
  have hTP : starImage D.H D.T ≤ markedParabolic D h K := le_sup_right.trans hLP
  have hodd : ¬ 2 ∣ (starImage D.H D.T).relIndex (markedParabolic D h K) := by
    intro hd
    exact (starSylow D h).not_dvd_index (hd.trans (relIndex_dvd_index_of_le hTP))
  have hne : (starImage D.H D.T).relIndex (markedParabolic D h K) ≠ 1 :=
    fun he => localStar_not_le_sylow D h hm (hLP.trans (relIndex_eq_one.mp he))
  have hi3 : (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 := by omega
  have he := localStar_eq_markedParabolic_of_index_three D h hLK hm hi3
  refine ⟨hi3, he, ?_⟩
  rw [← he]
  exact localStar_twoResidual D h

end Linear
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule
