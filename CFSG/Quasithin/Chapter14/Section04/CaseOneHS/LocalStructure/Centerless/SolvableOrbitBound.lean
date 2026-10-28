module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableNatural
public import Theory.GroupTheory.Commutator.SymmetricThreeSmallOrbit

/-!
# The opposing orbit bound and solvable centerlessness

The actual K-action on U/V₁ has kernel O₂(K) and image S₃. If the original
Goldschmidt module Ue had order at most eight, the K-span of V₂ would have
tilded image of order at most four. The normal cubic residual then moves
that entire image, and normality propagates the commutator to its H-span,
which is all of U/V₁. Coprime splitting forces the K-fixed subgroup to be
trivial, contradicting the nontrivial image of Z(U), centralized by K.

H.5.5 gives order eight for the same Ue, so this proves centerlessness in
the original S₃ × S₃ branch and applies it to LocalStructure. The proof
retains both literal quotient maps and the original shifted normal closure.
It uses no theorem that assumes centerlessness.
Source: Aschbacher--Smith 14.3.31, printed p.1003, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- The literal tilded actor has symmetric-three action quotient. -/
theorem source_solvable_tilde_actor_model (K : Subgroup G) (hKH : K ≤ F.H)
    (hKN : F.H ≤ normalizer (K : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))) :
    let C := centralizer (F.tilde F.U : Set F.G₁tilde)
    ∃ hn : (F.tilde F.U).Normal, letI := hn
      Nonempty (((F.tilde K) ⧸ C.comap (F.tilde K).subtype) ≃* Equiv.Perm (Fin 3)) := by
  let := chosen.elementary
  let A := K.subgroupOf F.H
  let q := F.tildeProjection
  let B := F.tilde K
  let Z := F.tilde F.U
  let C := centralizer (Z : Set F.G₁tilde)
  let : A.Normal := normal_subgroupOf_of_le_normalizer hKN
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V F.H)
  let hZ : Z.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := hZ
  refine ⟨hZ,?_⟩
  let f : A →* B ⧸ C.comap B.subtype :=
    (QuotientGroup.mk' (C.comap B.subtype)).comp (q.subgroupMap A)
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (q.subgroupMap_surjective A)
  have hact : (F.localTildeAction F.H le_rfl).ker = C.comap q := by
    change (F.tildeAction F.H F.U le_rfl (le_normalizer_conjugateSpanBy V F.H)).ker = _
    exact F.tildeAction_ker F.H F.U le_rfl (le_normalizer_conjugateSpanBy V F.H)
  have hk : f.ker = pCore 2 A := by
    have hh : f.ker = (pCore 2 F.H).comap A.subtype := by
      rw [←(CaseOneLarge.source_closure_geometry F d earlier hq chosen structural alternatives hne).tilde_kernel,
        hact]
      ext k
      change QuotientGroup.mk' (C.comap B.subtype) (q.subgroupMap A k) = 1 ↔ q (k:F.H) ∈ C
      exact QuotientGroup.eq_one_iff _
    rw [hh]
    apply le_antisymm
    · exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
    · apply map_le_iff_le_comap.mp
      exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map A.subtype⟩
  let j : A ≃* K := subgroupOfEquivOfLe hKH
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      ((QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans model.some))⟩

omit [Finite G] d earlier hq chosen structural alternatives hne in
private theorem tilde_span (A B : Subgroup G) (hAH : A ≤ F.H) (hBH : B ≤ F.H) :
    F.tilde (conjugateSpanBy A B) = conjugateSpanBy (F.tilde A) (F.tilde B) := by
  have hSH : conjugateSpanBy A B ≤ F.H := conjugateSpanBy_le hAH (hBH.trans F.H.le_normalizer)
  have hs : (conjugateSpanBy A B).subgroupOf F.H =
      conjugateSpanBy (A.subgroupOf F.H) (B.subgroupOf F.H) := by
    apply Subgroup.map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hSH,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hBH]
  change ((conjugateSpanBy A B).subgroupOf F.H).map F.tildeProjection = _
  rw [hs,map_conjugateSpanBy]
  rfl

/-- The original orbit has order greater than eight. The proof retains the
full central action and the literal quotient by the marked point. -/
theorem source_solvable_orbit_card_gt_eight (K : Subgroup G)
    (hKH : K ≤ F.H) (hKN : F.H ≤ normalizer (K : Set G))
    (hKC : K ≤ centralizer (F.ZU : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)))
    (hZ : F.ZU ≠ F.Vi 1) : 8 < Nat.card (amalgamModule F L K) := by
  by_contra hbig
  have hsmall : Nat.card (amalgamModule F L K) ≤ 8 := by omega
  let := chosen.elementary
  let c := CaseOneLarge.source_closure_geometry F d earlier hq chosen structural alternatives hne
  let := F.tilde_elementary_of_point c.two c.frattini_point
  let W := conjugateSpanBy (F.Vi 2) K
  let q := F.tildeProjection
  have hWU : W ≤ F.U := conjugateSpanBy_le
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
    (hKH.trans (le_normalizer_conjugateSpanBy V F.H))
  have hWH : W ≤ F.H := hWU.trans F.U_le_H
  have hWe : W ≤ amalgamModule F L K := conjugateSpanBy_le
    (source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne K hKH).1
    ((show K ≤ amalgamGroup F L K from le_sup_left.trans le_sup_left).trans
      (le_normalizer_conjugateSpanBy _ _))
  have h1W : F.Vi 1 ≤ W := (F.monotone (by decide : 1 ≤ 2)).trans (le_conjugateSpanBy _ _)
  have hWcard : Nat.card W ≤ 8 :=
    (Nat.card_le_card_of_injective (inclusion hWe) (inclusion_injective hWe)).trans hsmall
  have hWtcard : Nat.card (F.tilde W) ≤ 4 := by
    let f := F.tildeMap W hWH
    have hk : f.ker = (F.Vi 1).subgroupOf W := by
      ext w
      change f w = 1 ↔ (w:G) ∈ F.Vi 1
      constructor
      · intro hh
        exact (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H)
          (⟨w,hWH w.property⟩ : F.H)).mp (congrArg Subtype.val hh)
      · intro hh
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H)
          (⟨w,hWH w.property⟩ : F.H)).mpr hh
    have hkc : Nat.card f.ker = 2 := by
      rw [hk,Nat.card_congr (subgroupOfEquivOfLe h1W).toEquiv]
      simpa using F.card 1 (by decide)
    have hh := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective (F.tildeMap_surjective W hWH),card_top,hkc] at hh
    omega
  have hH : F.tilde F.H = ⊤ := by
    change (F.H.subgroupOf F.H).map q = ⊤
    rw [subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hgen : conjugateSpanBy W F.H = F.U := by
    apply le_antisymm (conjugateSpanBy_le hWU (le_normalizer_conjugateSpanBy V F.H))
    rw [(source_seed_geometry d earlier hq chosen F).2.1]
    exact conjugateSpanBy_mono (le_conjugateSpanBy _ _) le_rfl
  have hgent : conjugateSpanBy (F.tilde W) ⊤ = F.tilde F.U := by
    rw [←hH,←tilde_span F W F.H hWH le_rfl,hgen]
  obtain ⟨hn,hm⟩ := source_solvable_tilde_actor_model d earlier hq chosen structural alternatives F hne K hKH hKN model
  let := hn
  let : (F.tilde K).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hH]
    exact F.tilde_normalizes F.H K hKN))
  have hfix := fixed_eq_bot_of_symmetricThree_small_orbit (F.tilde F.U) (F.tilde K) (F.tilde W)
    (IsElementaryAbelian.isPGroup 2 _) (map_mono (comap_mono hWU))
    (F.tilde_normalizes K W (le_normalizer_conjugateSpanBy _ _)) hWtcard hgent hm
  have hZt : F.tilde F.ZU = ⊥ := by
    apply bot_unique
    rw [←hfix]
    refine le_inf (map_mono (comap_mono (map_subtype_le (center F.U)))) ?_
    rintro x ⟨z,hz,rfl⟩ y ⟨k,hk,rfl⟩
    have he : k*z=z*k := Subtype.ext ((hKC hk) z hz).symm
    exact (map_mul q k z).symm.trans ((congrArg q he).trans (map_mul q z k))
  apply hZ
  apply le_antisymm _ (F.point_le_ZU (by decide))
  intro z hz
  have hzq : q ⟨z,(map_subtype_le (center F.U)).trans F.U_le_H hz⟩ = 1 := by
    have hh := mem_map_of_mem q (show (⟨z,(map_subtype_le (center F.U)).trans F.U_le_H hz⟩ : F.H) ∈
      F.ZU.subgroupOf F.H from hz)
    change q _ ∈ F.tilde F.ZU at hh
    simpa only [hZt,mem_bot] using hh
  exact (QuotientGroup.eq_one_iff (N := (F.Vi 1).subgroupOf F.H)
    (⟨z,(map_subtype_le (center F.U)).trans F.U_le_H hz⟩ : F.H)).mp hzq

/-- Original 14.3.31 in the S₃ × S₃ alternative. The same shifted actor has
an order-eight orbit by H.5.5 and an orbit of strictly larger order. -/
theorem source_centerless_of_solvable_model
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hker,hm,hcard⟩ :=
    source_solvable_orbit_card_eight d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  have hlarge := source_solvable_orbit_card_gt_eight d earlier hq chosen structural alternatives
    F hne _ hKH hKN hKC hK hZ
  omega

/-- The solvable centerlessness branch applied to the original local-structure
consumer; the independent action theorem retains its earlier source direction. -/
theorem localStructure_of_solvable_model_action
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_solvable_model d earlier hq chosen structural alternatives F hne
      classification hZ model) action
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
