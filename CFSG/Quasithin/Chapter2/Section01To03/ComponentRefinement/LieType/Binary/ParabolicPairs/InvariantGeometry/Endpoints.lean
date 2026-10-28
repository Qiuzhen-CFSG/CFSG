module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.TransvectionOvergroups
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.SylowCoordinates

/-!
# The invariant endpoint pair without Dynkin action

A transvection centralizer has exactly two maximal proper overgroups: its
image-line and fixed-hyperplane stabilizers. Automorphisms fixing the
transvection permute these overgroups. A swap changes the subspace dimension,
so absence of Dynkin action makes both endpoint flags invariant under N_S(L).
The two stabilizers generate the component and contain its Sylow intersection.

This proves the endpoint case of the invariant parabolic construction in
Aschbacher–Smith 2.3.9(7), printed pp.525–526. All invariance is relative to
the component normalizer; other elements of S may permute components.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

/-- A one-space proper flag. -/
noncomputable def Flag.singleton {n : ℕ} (W : Space n) (hW : W ≠ ⊥ ∧ W ≠ ⊤) : Flag n where
  spaces := {W}
  nonempty := by simp
  proper := by simpa using hW
  chain := by simp

theorem Flag.singleton_types {n : ℕ} (W : Space n) (hW : W ≠ ⊥ ∧ W ≠ ⊤) :
    (Flag.singleton W hW).types = {Module.finrank (ZMod 2) W} := by
  classical
  simp [Flag.types, Flag.singleton]

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} [NeZero n]

theorem flagStabilizer_singleton (e : L ≃* PSL n) (W : Space n)
    (hW : W ≠ ⊥ ∧ W ≠ ⊤) :
    flagStabilizer e (Flag.singleton W hW) = subspaceStabilizer e W := by
  ext x
  simp [mem_flagStabilizer, mem_subspaceStabilizer, Flag.singleton]

theorem subspaceStabilizer_eq_of_le (e : L ≃* PSL n) {W U : Space n}
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (h : subspaceStabilizer e W ≤ subspaceStabilizer e U) : W = U := by
  apply BinaryLinear.FourParabolicAction.parabolic_le_imp_eq hU0 hU1
  intro g hg
  obtain ⟨x, rfl⟩ := (linearModel e).surjective g
  exact h hg

theorem subspaceStabilizer_ne_top_of_proper (e : L ≃* PSL n) {W : Space n}
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) : subspaceStabilizer e W ≠ ⊤ := by
  intro ht
  apply BinaryLinear.FourParabolicAction.parabolic_ne_top hW0 hW1
  apply top_unique
  intro g _
  obtain ⟨x, rfl⟩ := (linearModel e).surjective g
  exact show x ∈ subspaceStabilizer e W from ht ▸ mem_top x

private theorem permutes_cover (C P Q : Subgroup L)
    (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) (hPQ : ¬ P ≤ Q) (hQP : ¬ Q ≤ P)
    (hCP : C ≤ P) (hCQ : C ≤ Q)
    (hcover : ∀ K : Subgroup L, C ≤ K → K ≠ ⊤ → K ≤ P ∨ K ≤ Q)
    (α : MulAut L) (hC : C.map α.toMonoidHom = C) :
    ((P.map α.toMonoidHom = P ∧ Q.map α.toMonoidHom = Q) ∨
      (P.map α.toMonoidHom = Q ∧ Q.map α.toMonoidHom = P)) := by
  have hmaxP : IsCoatom P := by
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hP, ?_⟩
    intro K hKt hPK
    rcases hcover K (hCP.trans hPK) hKt with h | h
    · exact h
    · exact (hPQ (hPK.trans h)).elim
  have hmaxQ : IsCoatom Q := by
    apply isCoatom_iff_ge_of_le.mpr
    refine ⟨hQ, ?_⟩
    intro K hKt hQK
    rcases hcover K (hCQ.trans hQK) hKt with h | h
    · exact (hQP (hQK.trans h)).elim
    · exact h
  have hmaxP' : IsCoatom (P.map α.toMonoidHom) := (OrderIso.isCoatom_iff α.mapSubgroup P).mpr hmaxP
  have hmaxQ' : IsCoatom (Q.map α.toMonoidHom) := (OrderIso.isCoatom_iff α.mapSubgroup Q).mpr hmaxQ
  have hCP' : C ≤ P.map α.toMonoidHom := by
    simpa only [hC] using map_mono (f := α.toMonoidHom) hCP
  have hCQ' : C ≤ Q.map α.toMonoidHom := by
    simpa only [hC] using map_mono (f := α.toMonoidHom) hCQ
  have hp : P.map α.toMonoidHom = P ∨ P.map α.toMonoidHom = Q := by
    rcases hcover _ hCP' hmaxP'.ne_top with h | h
    · exact Or.inl ((hmaxP'.le_iff_eq hP).mp h).symm
    · exact Or.inr ((hmaxP'.le_iff_eq hQ).mp h).symm
  have hq : Q.map α.toMonoidHom = P ∨ Q.map α.toMonoidHom = Q := by
    rcases hcover _ hCQ' hmaxQ'.ne_top with h | h
    · exact Or.inl ((hmaxQ'.le_iff_eq hP).mp h).symm
    · exact Or.inr ((hmaxQ'.le_iff_eq hQ).mp h).symm
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact (hPQ (map_injective α.injective (hp.trans hq.symm)).le).elim
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact (hPQ (map_injective α.injective (hp.trans hq.symm)).le).elim


variable {e : L ≃* PSL n} {t : L}

private theorem endpoint_properties (c : TransvectionCoordinates e t) (hn : 3 ≤ n) :
    (c.line ≠ ⊥ ∧ c.line ≠ ⊤) ∧ (c.hyperplane ≠ ⊥ ∧ c.hyperplane ≠ ⊤) ∧
      Module.finrank (ZMod 2) c.line ≠ Module.finrank (ZMod 2) c.hyperplane := by
  have h := (c.flag (by omega)).proper
  refine ⟨h c.line (by simp [TransvectionCoordinates.flag]),
    h c.hyperplane (by simp [TransvectionCoordinates.flag]), ?_⟩
  have := c.line_finrank
  have := c.hyperplane_finrank
  omega

/-- The image-line and fixed-hyperplane stabilizers generate the component. -/
theorem TransvectionCoordinates.endpoints_generate (c : TransvectionCoordinates e t)
    (hn : 3 ≤ n) :
    subspaceStabilizer e c.line ⊔ subspaceStabilizer e c.hyperplane = ⊤ := by
  obtain ⟨hl, hh, hd⟩ := endpoint_properties c hn
  by_contra hne
  have hC : centralizer ({t} : Set L) ≤
      subspaceStabilizer e c.line ⊔ subspaceStabilizer e c.hyperplane := by
    rw [c.centralizer_eq]
    exact inf_le_left.trans le_sup_left
  rcases c.proper_overgroup_endpoint (by omega) _ hC hne with h | h
  · exact hd (congrArg (fun W : Space n => Module.finrank (ZMod 2) W)
      (subspaceStabilizer_eq_of_le e hl.1 hl.2 (le_sup_right.trans h)).symm)
  · exact hd (congrArg (fun W : Space n => Module.finrank (ZMod 2) W)
      (subspaceStabilizer_eq_of_le e hh.1 hh.2 (le_sup_left.trans h)))

/-- An automorphism fixing the transvection fixes or exchanges its endpoints. -/
theorem TransvectionCoordinates.endpoints_permuted (c : TransvectionCoordinates e t)
    (hn : 3 ≤ n) (α : MulAut L) (ht : α t = t) :
    ((subspaceStabilizer e c.line).map α.toMonoidHom = subspaceStabilizer e c.line ∧
      (subspaceStabilizer e c.hyperplane).map α.toMonoidHom = subspaceStabilizer e c.hyperplane) ∨
    ((subspaceStabilizer e c.line).map α.toMonoidHom = subspaceStabilizer e c.hyperplane ∧
      (subspaceStabilizer e c.hyperplane).map α.toMonoidHom = subspaceStabilizer e c.line) := by
  obtain ⟨hl, hh, hd⟩ := endpoint_properties c hn
  have hPQ : ¬ subspaceStabilizer e c.line ≤ subspaceStabilizer e c.hyperplane := by
    intro h
    exact hd (congrArg (fun W : Space n => Module.finrank (ZMod 2) W)
      (subspaceStabilizer_eq_of_le e hh.1 hh.2 h))
  have hQP : ¬ subspaceStabilizer e c.hyperplane ≤ subspaceStabilizer e c.line := by
    intro h
    exact hd (congrArg (fun W : Space n => Module.finrank (ZMod 2) W)
      (subspaceStabilizer_eq_of_le e hl.1 hl.2 h).symm)
  have hC : (centralizer ({t} : Set L)).map α.toMonoidHom = centralizer ({t} : Set L) := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      simpa only [map_mul, MulEquiv.apply_symm_apply, ht] using congrArg α h
    · intro h
      apply α.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply, ht] using h
  apply permutes_cover (centralizer ({t} : Set L)) _ _
    (subspaceStabilizer_ne_top_of_proper e hl.1 hl.2)
    (subspaceStabilizer_ne_top_of_proper e hh.1 hh.2) hPQ hQP
  · rw [c.centralizer_eq]
    exact inf_le_left
  · rw [c.centralizer_eq]
    exact inf_le_right
  · exact c.proper_overgroup_endpoint (by omega)
  · exact hC

/-- Intrinsic invariance under the normalizer action gives the required ambient invariance. -/
theorem flagInvariant_of_stabilizer_maps (e : L ≃* PSL n) (S : Subgroup G) (F : Flag n)
    (h : ∀ s : G, s ∈ S → ∀ hs : s ∈ normalizer (L : Set G),
      (flagStabilizer e F).map (L.normalizerMonoidHom ⟨s, hs⟩).toMonoidHom =
        flagStabilizer e F) : FlagInvariant e S F := by
  intro s hs
  rw [mem_normalizer_iff_map_conj_eq]
  change ((flagStabilizer e F).map L.subtype).map (MulAut.conj s).toMonoidHom = _
  have hm : ((flagStabilizer e F).map L.subtype).map (MulAut.conj s).toMonoidHom =
      ((flagStabilizer e F).map (L.normalizerMonoidHom ⟨s, hs.2⟩).toMonoidHom).map
        L.subtype := by
    rw [map_map, map_map]
    rfl
  rw [hm, h s hs.1 hs.2]
  rfl

variable {H M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Absence of dimension-changing conjugation fixes both endpoint stabilizers. -/
theorem TransvectionCoordinates.endpoints_fixed_of_no_dynkin
    (c : TransvectionCoordinates e t) (hn : 3 ≤ n)
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t)
    (hd : ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype))
    {s : G} (hs : s ∈ (S : Subgroup H).map H.subtype)
    (hsL : s ∈ normalizer (L : Set G)) :
    (subspaceStabilizer e c.line).map (L.normalizerMonoidHom ⟨s, hsL⟩).toMonoidHom =
      subspaceStabilizer e c.line ∧
    (subspaceStabilizer e c.hyperplane).map (L.normalizerMonoidHom ⟨s, hsL⟩).toMonoidHom =
      subspaceStabilizer e c.hyperplane := by
  have htfix : L.normalizerMonoidHom ⟨s, hsL⟩ t = t := by
    apply Subtype.ext
    change s * (t : G) * s⁻¹ = (t : G)
    rw [projection_centralizes_normalizer h e ht hs hsL, mul_inv_cancel_right]
  rcases c.endpoints_permuted hn _ htfix with hfix | hswap
  · exact hfix
  · obtain ⟨hl, hh, hdim⟩ := endpoint_properties c hn
    exact (hd ⟨s, hs, hsL, c.line, c.hyperplane, hl.1, hl.2, hh.1, hh.2, hdim, hswap.1⟩).elim

/-- In degrees four and five, trivial Dynkin action supplies the two generating
invariant end-node flags, containing the actual Sylow intersection. -/
theorem exists_invariant_endpoint_pair (h : LocalSetup H L M S z)
    (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2)
    (hd : ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype)) :
    ∃ F₁ F₂ : Flag n,
      ExcludedFlagShape F₁ ∧ ExcludedFlagShape F₂ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₁ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₂ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₁ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₂ ∧
      flagStabilizer e F₁ ⊔ flagStabilizer e F₂ = ⊤ := by
  obtain ⟨c⟩ := projection_transvectionCoordinates h hn e ht ht2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hl, hh, _⟩ := endpoint_properties c hn3
  let F₁ := Flag.singleton c.line hl
  let F₂ := Flag.singleton c.hyperplane hh
  have hF₁ : F₁.types = {1} := by
    rw [Flag.singleton_types, c.line_finrank]
  have hF₂ : F₂.types = {n - 1} := by
    rw [Flag.singleton_types]
    have hd := c.hyperplane_finrank
    congr 1
    omega
  have hK₁ : flagStabilizer e F₁ = subspaceStabilizer e c.line := flagStabilizer_singleton e _ _
  have hK₂ : flagStabilizer e F₂ = subspaceStabilizer e c.hyperplane := flagStabilizer_singleton e _ _
  have hS : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ centralizer ({t} : Set L) := by
    obtain ⟨T, hT⟩ := exists_component_sylow h
    rw [← hT]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((projection_mem_center_component_sylow h e ht ht2 T hT).2 x hx)
  refine ⟨F₁, F₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hn with hn | hn
    · exact Or.inl ⟨hn, Or.inl hF₁⟩
    · exact Or.inr ⟨hn, Or.inl hF₁⟩
  · rcases hn with hn | hn
    · exact Or.inl ⟨hn, Or.inr (by simpa [hn] using hF₂)⟩
    · exact Or.inr ⟨hn, Or.inr (Or.inl (by simpa [hn] using hF₂))⟩
  · apply flagInvariant_of_stabilizer_maps
    intro s hs hsL
    rw [hK₁]
    exact (c.endpoints_fixed_of_no_dynkin hn3 h ht hd hs hsL).1
  · apply flagInvariant_of_stabilizer_maps
    intro s hs hsL
    rw [hK₂]
    exact (c.endpoints_fixed_of_no_dynkin hn3 h ht hd hs hsL).2
  · rw [hK₁]
    exact hS.trans (by rw [c.centralizer_eq]; exact inf_le_left)
  · rw [hK₂]
    exact hS.trans (by rw [c.centralizer_eq]; exact inf_le_right)
  · rw [hK₁, hK₂]
    exact c.endpoints_generate hn3

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
