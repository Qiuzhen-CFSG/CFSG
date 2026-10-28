module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairReduced
public import Theory.GroupTheory.NormalSectionTwoResidual
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.SolvableResidual.TwoKernel
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# Residuals and centralizers in the reduced A5 local groups

For the genuine reduced pair of DGS (6.1), a normal subgroup escaping
O₂(Lᵢ S) contains O²(Lᵢ S) and covers the local Borel cosets. This is
DGS (6.2)(a)--(b) in the A5 row: map the normal subgroup into the simple
A5 quotient, then remove the remaining two-group quotient by the residual.
The residual is perfect and is unchanged by adjoining S to the original
normal factor. In particular it equals that factor when the factor is perfect.

For the actual seed Ω₁(Z(S)), characteristic two places its local conjugate
span in the center of O₂(Lᵢ S). The span is elementary abelian. Applying
the normal-subgroup result to its centralizer gives the A5 specialization
of (6.2)(c): the local centralizer is exactly the two-core, or the span is
already the central seed. The common seed is nontrivial, and core-freeness
selects a noncentral endpoint with this exact kernel.
These are structural results about the original
subgroups, without a marked-recognition or splitting assumption.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs, Part II,
(6.0)--(6.2), pp.118--119. The reduced DGS factor is Lᵢ S; identifying
its core with O₂(Lᵢ) still requires the later rank-two argument.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
namespace HypothesisF11

omit [Finite G] in
/-- The original normal factor absorbs the two-residual of its join with S. -/
theorem localJoin_residual_le_local (h : HypothesisF11 L S) (i : Fin 2) :
    (pResidual 2 (L i ⊔ S : Subgroup G)).map (L i ⊔ S).subtype ≤ L i := by
  let P := L i ⊔ S
  let N := (L i).subgroupOf P
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (L i).le_normalizer (h.S_normalizes i))
  have hsup : N ⊔ S.subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L i ≤ P from le_sup_left),
      map_subgroupOf_eq_of_le (show S ≤ P from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hr : pResidual 2 P ≤ N := sInf_le
    ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N (S.subgroupOf P)
      h.S_isP.comap_subtype hsup⟩
  rintro x ⟨y, hy, rfl⟩
  exact hr hy

/-- Adjoining the actual normalizing two-group preserves the embedded residual. -/
theorem localJoin_residual_eq (h : HypothesisF11 L S) (i : Fin 2) :
    (pResidual 2 (L i ⊔ S : Subgroup G)).map (L i ⊔ S).subtype =
      (pResidual 2 (L i)).map (L i).subtype :=
  (embedded_pResidual_eq_of_le_of_residual_le 2 le_sup_left
    (h.localJoin_residual_le_local i)).symm

/-- A perfect original factor is the entire reduced two-residual. -/
theorem localJoin_residual_eq_of_perfect (h : HypothesisF11 L S) (i : Fin 2)
    [Group.IsPerfect (L i)] :
    (pResidual 2 (L i ⊔ S : Subgroup G)).map (L i ⊔ S).subtype = L i := by
  rw [h.localJoin_residual_eq i, pResidual_eq_top_of_isPerfect 2,
    ← MonoidHom.range_eq_map, range_subtype]

/-- DGS (6.2)(a) in the A5 row, retaining the reduced local group. -/
theorem a5_localJoin_normal_dichotomy (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (N : Subgroup G) (hN : N ≤ L i ⊔ S)
    (hnN : L i ⊔ S ≤ normalizer (N : Set G)) :
    N ≤ twoCore (L i ⊔ S) ∨
      (pResidual 2 (L i ⊔ S : Subgroup G)).map (L i ⊔ S).subtype ≤ N := by
  let P := L i ⊔ S
  let eP := (h.a5_localJoinQuotientEquiv hn i e).symm.trans e
  let f : P →* alternatingGroup (Fin 5) :=
    eP.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hf : Function.Surjective f := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 P := by
    ext x
    change eP (QuotientGroup.mk x) = 1 ↔ x ∈ pCore 2 P
    rw [map_eq_one_iff eP eP.injective, QuotientGroup.eq_one_iff]
  let : (N.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hnN
  by_cases hQ : N ≤ twoCore P
  · exact Or.inl hQ
  · right
    have hescape : ¬ N.subgroupOf P ≤ f.ker := by
      intro hc
      apply hQ
      intro x hx
      exact mem_map_of_mem P.subtype (hk ▸ hc (show (⟨x, hN hx⟩ : P) ∈ N.subgroupOf P from hx))
    have hr := pResidual_le_normal_of_not_le_simple_kernel 2 f hf
      (hk ▸ pCore_isPGroup) (N.subgroupOf P) hescape
    rintro x ⟨y, hy, rfl⟩
    exact hr hy

/-- The residual covers the reduced local group together with its actual Sylow. -/
theorem a5_localJoin_residual_sup_S (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Fin 2) :
    (pResidual 2 (L i ⊔ S : Subgroup G)).map (L i ⊔ S).subtype ⊔ S = L i ⊔ S := by
  obtain ⟨T, hT⟩ := (h.a5_localJoin_hypothesis hn he).sylow i
  have hh := congrArg (Subgroup.map (L i ⊔ S).subtype) (pResidual_sup_sylow_eq_top T)
  simpa only [Subgroup.map_sup, hT, inf_eq_left.mpr (show S ≤ L i ⊔ S from le_sup_right),
    ← MonoidHom.range_eq_map, range_subtype] using hh

/-- DGS (6.2)(b): an escaping normal subgroup covers every local Borel coset. -/
theorem a5_localJoin_normal_sup_borel (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Fin 2) (N : Subgroup G) (hN : N ≤ L i ⊔ S)
    (hnN : L i ⊔ S ≤ normalizer (N : Set G))
    (hQ : ¬ N ≤ twoCore (L i ⊔ S)) :
    N ⊔ borel (L i ⊔ S) S = L i ⊔ S := by
  obtain ⟨e⟩ := he i
  have hr := (h.a5_localJoin_normal_dichotomy hn i e N hN hnN).resolve_left hQ
  apply le_antisymm (sup_le hN (borel_le _ _))
  apply (h.a5_localJoin_residual_sup_S hn he i).ge.trans
  apply sup_le_sup hr
  rw [h.localJoin_borel_eq hn i]
  exact le_sup_right

/-- The reduced two-residual is perfect because its quotient is perfect A5. -/
theorem a5_localJoin_residual_perfect (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G)) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    Group.IsPerfect (pResidual 2 (L i ⊔ S : Subgroup G)) := by
  let P := L i ⊔ S
  let eP := (h.a5_localJoinQuotientEquiv hn i e).symm.trans e
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (P ⧸ pCore 2 P) :=
    Group.IsPerfect.ofSurjective (f := eP.symm.toMonoidHom) eP.symm.surjective
  have heq := pResidual_eq_solvableResidual_of_perfect_image
    (QuotientGroup.mk' (pCore 2 P)) (QuotientGroup.mk'_surjective _)
    (show IsPGroup 2 (QuotientGroup.mk' (pCore 2 P)).ker by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  change Group.IsPerfect (pResidual 2 P)
  rw [heq]
  infer_instance

/-- The centralizer alternative underlying DGS (6.2)(c). The seed may be
the omega-center of S; only its literal centralization by S is needed. -/
theorem a5_localJoin_seed_span_centralizer (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Fin 2) (Z : Subgroup G) (hSZ : S ≤ centralizer (Z : Set G)) :
    (L i ⊔ S) ⊓ centralizer (conjugateSpanBy Z (L i ⊔ S) : Set G) ≤
      twoCore (L i ⊔ S) ∨
    (conjugateSpanBy Z (L i ⊔ S) = Z ∧ L i ⊔ S ≤ centralizer (Z : Set G)) := by
  let P := L i ⊔ S
  let V := conjugateSpanBy Z P
  let C := P ⊓ centralizer (V : Set G)
  have hnC : P ≤ normalizer (C : Set G) :=
    (le_inf P.le_normalizer ((le_normalizer_conjugateSpanBy Z P).trans
      (normalizer_le_normalizer_centralizer V))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨e⟩ := he i
  rcases h.a5_localJoin_normal_dichotomy hn i e C inf_le_left hnC with hC | hR
  · exact Or.inl hC
  · have hrZ : (pResidual 2 P).map P.subtype ≤ centralizer (Z : Set G) :=
      (hR.trans inf_le_right).trans (centralizer_le (le_conjugateSpanBy Z P))
    have hPZ : P ≤ centralizer (Z : Set G) :=
      (h.a5_localJoin_residual_sup_S hn he i).ge.trans (sup_le hrZ hSZ)
    exact Or.inr ⟨le_antisymm
      (conjugateSpanBy_le le_rfl (hPZ.trans (Subgroup.centralizer_le_normalizer _)))
      (le_conjugateSpanBy Z P), hPZ⟩

/-- The actual DGS vertex seed lies in the center of the local core, and
its local conjugate span is elementary abelian. -/
theorem a5_localJoin_omega_span (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Fin 2) :
    let V := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient S) (L i ⊔ S)
    V ≤ twoCore (L i ⊔ S) ∧
      twoCore (L i ⊔ S) ≤ centralizer (V : Set G) ∧ IsElementaryAbelian 2 V := by
  let P := L i ⊔ S
  let Q := twoCore P
  let Z := Stellmacher.omegaOneCenterAmbient S
  let V := conjugateSpanBy Z P
  have hQS : Q ≤ S := by
    change twoCore (L i ⊔ S) ≤ S
    rw [h.localJoin_twoCore_eq_parabolic hn i]
    exact h.parabolic_core_le_S i
  have hZP : Z ≤ P := fun x hx =>
    (show S ≤ P from le_sup_right) ((Stellmacher.mem_omegaOneCenterAmbient_iff S x).mp hx).1
  have hQZ : Q ≤ centralizer (Z : Set G) := by
    intro q hq z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff S z).mp hz).2.2 q (hQS hq) |>.symm
  have hZQ : Z ≤ Q := by
    intro z hz
    have hc : (⟨z, hZP hz⟩ : P) ∈ centralizer (pCore 2 P : Set P) := by
      intro q hq
      exact Subtype.ext ((hQZ (mem_map_of_mem P.subtype hq) z hz).symm)
    exact mem_map_of_mem P.subtype ((h.a5_localJoin_hypothesis hn he).local_core_selfCentralizing i hc)
  have hPQ : P ≤ normalizer (Q : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hVQ : V ≤ Q := conjugateSpanBy_le hZQ hPQ
  have hQV : Q ≤ centralizer (V : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes Q Z P hPQ hQZ
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian S
  let : IsMulCommutative V := le_centralizer_iff_isMulCommutative.mp (hVQ.trans hQV)
  exact ⟨hVQ, hQV, conjugateSpanBy_elementary_of_commutative Z P⟩

/-- In the noncentral A5 row the kernel on the genuine omega-center span
is exactly the local two-core. -/
theorem a5_localJoin_omega_span_centralizer (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Fin 2) :
    let Z := Stellmacher.omegaOneCenterAmbient S
    let V := conjugateSpanBy Z (L i ⊔ S)
    ((L i ⊔ S) ⊓ centralizer (V : Set G) = twoCore (L i ⊔ S)) ∨
      (V = Z ∧ L i ⊔ S ≤ centralizer (Z : Set G)) := by
  have hSZ : S ≤ centralizer (Stellmacher.omegaOneCenterAmbient S : Set G) := by
    intro s hs z hz
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff S z).mp hz).2.2 s hs |>.symm
  rcases h.a5_localJoin_seed_span_centralizer hn he i _ hSZ with hc | hc
  · exact Or.inl (le_antisymm hc (le_inf (map_subtype_le _)
      (h.a5_localJoin_omega_span hn he i).2.1))
  · exact Or.inr hc

/-- The common Sylow has a nontrivial omega-center. -/
theorem omega_seed_ne_bot (h : HypothesisF11 L S) :
    Stellmacher.omegaOneCenterAmbient S ≠ ⊥ := by
  have hS : S ≠ ⊥ := by
    intro hS
    apply h.local_twoCore_ne_bot 0
    obtain ⟨T, hT⟩ := h.sylow 0
    apply bot_unique
    have hh := (pCoreIn_le_sylow (L 0) T).trans_eq hT
    exact hh.trans (hS ▸ inf_le_left)
  let : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hS
  intro hz
  apply omega_center_ne_bot h.S_isP
  exact (map_eq_bot_iff_of_injective _ S.subtype_injective).mp hz

/-- Core-freeness selects an actual noncentral endpoint for the DGS
critical-pair argument; its omega-span action has exactly the two-core kernel. -/
theorem a5_exists_noncentral_omega_span (h : HypothesisF11 L S)
    (hn : ∀ i, borel (L i) S ≤ normalizer (S : Set G))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))) :
    let Z := Stellmacher.omegaOneCenterAmbient S
    ∃ i : Fin 2,
      ¬ L i ⊔ S ≤ centralizer (Z : Set G) ∧
      (L i ⊔ S) ⊓ centralizer (conjugateSpanBy Z (L i ⊔ S) : Set G) =
        twoCore (L i ⊔ S) := by
  let Z := Stellmacher.omegaOneCenterAmbient S
  have hZS : Z ≤ S := fun z hz => (Stellmacher.mem_omegaOneCenterAmbient_iff S z).mp hz |>.1
  have hex : ∃ i : Fin 2, ¬ L i ⊔ S ≤ centralizer (Z : Set G) := by
    by_contra! hc
    have hGC : generated L S ≤ centralizer (Z : Set G) :=
      sup_le (sup_le (le_sup_left.trans (hc 0)) (le_sup_left.trans (hc 1)))
        (le_sup_right.trans (hc 0))
    have hzcore : Z ≤ (generated L S).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (h.S_isP.to_le hZS) (hZS.trans le_sup_right)
        (hGC.trans (Subgroup.centralizer_le_normalizer _))
    have hzbot : Z = ⊥ := by
      simpa only [pCoreIn, h.twoCore_free, Subgroup.map_bot, le_bot_iff] using hzcore
    exact h.omega_seed_ne_bot hzbot
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  exact (h.a5_localJoin_omega_span_centralizer hn he i).resolve_right (fun hh => hi hh.2)

end HypothesisF11
end CFSG.Quasithin.ChapterF.Source
