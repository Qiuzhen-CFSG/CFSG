module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs

/-!
# The literal residual parabolic and its two-core

The original parabolic embeds into C_G(U) through two subgroup inclusions.
The central two-subgroup U is contained in each Sylow two-subgroup of its
centralizer, hence in the residual parabolic. Its pullback is a nontrivial
normal two-subgroup. This supplies the family condition O₂(H) ≠ 1 required
by 4.4.13, without an extra model hypothesis.

We also isolate the maximal-overgroup placement: uniqueness supplies an upper
bound on H ∩ M; equality requires containing the actual maximal overgroup.
Source: Aschbacher--Smith, E.6.27, printed p.257, and B.6.1, printed p.112.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

open Subgroup ChapterB

universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]

/-- The literal embedding of a minimal parabolic of O^{2'}(C_G(U)). -/
def residualEmbedding (U : Subgroup G)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G)))) : H →* G :=
  (centralizer (U : Set G)).subtype.comp
    ((primeToResidual 2 (centralizer (U : Set G))).subtype.comp H.subtype)

omit [Finite G] in
theorem residualEmbedding_injective (U : Subgroup G)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G)))) :
    Function.Injective (residualEmbedding U H) :=
  (centralizer (U : Set G)).subtype_injective.comp
    ((primeToResidual 2 (centralizer (U : Set G))).subtype_injective.comp
      H.subtype_injective)

omit [Finite G] in
theorem residualEmbedding_range (U : Subgroup G)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G)))) :
    (residualEmbedding U H).range =
      (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
        (centralizer (U : Set G)).subtype := by
  simp only [residualEmbedding, MonoidHom.range_comp, range_subtype]


omit [Finite G] in
/-- Restriction of a relative minimal parabolic to its own carrier. -/
theorem minimalParabolic_subtype (S : Sylow 2 X) (H : Subgroup X)
    (hH : IsMinimalParabolicOver S H) :
    IsMinimalParabolicOver (S.subtype hH.1.1.le) ⊤ := by
  obtain ⟨N, hN, hu⟩ := hH.1.2
  have hmax : IsCoatom (N.subgroupOf H) := by
    refine ⟨?_, ?_⟩
    · intro he
      exact hN.2.lt.not_ge (subgroupOf_eq_top.mp he)
    · intro L hL
      have hNL : N < L.map H.subtype := by
        have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hL
        rwa [map_subgroupOf_eq_of_le hN.2.le] at hh
      have he : L.map H.subtype = H :=
        (hN.2.eq_or_eq hNL.le (map_subtype_le L)).resolve_left (ne_of_gt hNL)
      apply map_injective H.subtype_injective
      simpa only [← MonoidHom.range_eq_map, range_subtype] using he
  rw [isMinimalParabolicOver_top_iff]
  refine ⟨⟨N.subgroupOf H, ⟨hmax, ?_⟩, ?_⟩,
    (isMinimalParabolicOver_iff S H).mp hH |>.2⟩
  · exact comap_mono hN.1
  · intro L hL
    have hSL : (S : Subgroup X) ≤ L.map H.subtype := by
      have hh := map_mono (f := H.subtype) hL.2
      change ((S : Subgroup X).subgroupOf H).map H.subtype ≤ _ at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.le] at hh
    have hLH : L.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hL.1.lt_top
      simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
    have hLN : L ≤ N.subgroupOf H :=
      map_le_iff_le_comap.mp (hH.1.le_maximal hN hSL hLH)
    exact ((hL.1.le_iff.mp hLN).resolve_left hmax.ne_top).symm

/-- The Sylow subgroup used by the original residual-parabolic consumer. -/
def parabolicSylow {U : Subgroup G} (S : Sylow 2 (centralizer (U : Set G)))
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H) : Sylow 2 H :=
  (residualSylow S).subtype hH.1.1.le

omit [Finite G] in
/-- No Sylow conjugation is hidden in the residual-parabolic embedding. -/
theorem parabolicSylow_image {U : Subgroup G}
    (S : Sylow 2 (centralizer (U : Set G)))
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H) :
    (parabolicSylow S H hH : Subgroup H).map (residualEmbedding U H) =
      (S : Subgroup (centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype := by
  change (((residualSylow S : Subgroup (primeToResidual 2 (centralizer (U : Set G)))).subgroupOf H).map _) = _
  rw [residualEmbedding, ← map_map, ← map_map,
    map_subgroupOf_eq_of_le hH.1.1.le, residualSylow_map]

omit [Finite G] in
/-- The actual central subgroup U lies in each Sylow subgroup of C_G(U). -/
theorem subspace_le_centralizer_sylow
    {U : Subgroup G} (hU : IsPGroup 2 U) (ha : IsMulCommutative U)
    (S : Sylow 2 (centralizer (U : Set G))) :
    U ≤ (S : Subgroup (centralizer (U : Set G))).map
      (centralizer (U : Set G)).subtype := by
  let := ha
  let C := centralizer (U : Set G)
  have hUC : U ≤ C := U.le_centralizer
  have hnormal : (U.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUC).mpr (centralizer_le_normalizer _)
  let := hnormal
  have hp : IsPGroup 2 (U.subgroupOf C) := hU.comap_subtype
  have hUS := hp.le_sylow_of_normal S
  have hh := map_mono (f := C.subtype) hUS
  rwa [map_subgroupOf_eq_of_le hUC] at hh

omit [Finite G] [Finite X] in
/-- The pullback of a nontrivial central two-subgroup supplies a nontrivial
intrinsic two-core. The map and range containments retain the literal carrier. -/
theorem twoCore_ne_bot_of_central_subgroup
    {U : Subgroup G} (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (f : X →* G) (hf : Function.Injective f)
    (hUr : U ≤ f.range) (hrC : f.range ≤ centralizer (U : Set G)) :
    pCore 2 X ≠ ⊥ := by
  have hnormal : (U.comap f).Normal := by
    refine ⟨?_⟩
    intro x hx g
    change f (g * x * g⁻¹) ∈ U
    simpa only [map_mul, map_inv, SetLike.mem_coe] using
      ((centralizer_le_normalizer _ (hrC ⟨g, rfl⟩)) (f x)).mp hx
  let := hnormal
  have hle : U.comap f ≤ pCore 2 X :=
    le_sSup ⟨hnormal, hU.comap_of_injective f hf⟩
  intro he
  apply hne
  apply eq_bot_iff.mpr
  intro u hu
  obtain ⟨x, rfl⟩ := hUr hu
  have hx : x ∈ (⊥ : Subgroup X) := he ▸ hle hu
  simp only [mem_bot.mp hx, map_one, mem_bot]

/-- The 4.4.13 family condition for the precise residual parabolic. -/
theorem residual_twoCore_ne_bot
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (S : Sylow 2 (centralizer (U : Set G)))
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H) :
    pCore 2 H ≠ ⊥ := by
  let := h.elementary
  have hUp := (IsElementaryAbelian.isPGroup 2 V).to_le hUV
  have hUa : IsMulCommutative U := by
    apply IsMulCommutative.of_comm
    intro a b
    apply Subtype.ext
    exact setLike_mul_comm (s := V) (hUV a.property) (hUV b.property)
  apply twoCore_ne_bot_of_central_subgroup hUp hU (residualEmbedding U H)
    (residualEmbedding_injective U H)
  · have hSH := map_mono (f := (primeToResidual 2 (centralizer (U : Set G))).subtype)
      hH.1.1.le
    rw [residualSylow_map] at hSH
    rw [residualEmbedding_range]
    exact (subspace_le_centralizer_sylow hUp hUa S).trans (map_mono hSH)
  · rintro _ ⟨x, rfl⟩
    exact ((x : primeToResidual 2 (centralizer (U : Set G))) :
      centralizer (U : Set G)).property

/-- SQTK is inherited from the actual two-local normalizer N_G(U), retaining
both strong quasithinness and the proper-K input of the original ambient group. -/
theorem residual_sqtk
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G)))) : IsSQTK Kc H := by
  let := h.elementary
  have hn := h.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (U : Set G)) from
      ⟨U, hU, (IsElementaryAbelian.isPGroup 2 V).to_le hUV, rfl⟩)
  let f := (residualEmbedding U H).codRestrict (normalizer (U : Set G))
    (fun x => centralizer_le_normalizer (U : Set G)
      (((x : primeToResidual 2 (centralizer (U : Set G))) :
        centralizer (U : Set G)).property))
  have hf : Function.Injective f := by
    intro a b he
    exact residualEmbedding_injective U H
      (congrArg (fun x : normalizer (U : Set G) => (x : G)) he)
  exact ⟨hn.stronglyQuasithin.of_injective f hf, hn.isKGroup.of_injective f hf⟩

omit [Finite G] in
/-- Uniqueness gives the upper containment on the actual local overlap. -/
theorem overlap_le_maximal (f : X →* G) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {M : Subgroup G}
    (hSM : (S : Subgroup X).map f ≤ M) (hescape : ¬ f.range ≤ M) :
    M.comap f ≤ minimalParabolicMax S hP := by
  have hm := minimalParabolicMax_spec S hP
  apply hP.1.le_maximal ⟨hm.2, hm.1.covBy_top⟩ (map_le_iff_le_comap.mp hSM)
  apply lt_top_iff_ne_top.mpr
  intro he
  apply hescape
  rintro _ ⟨x, rfl⟩
  exact (show x ∈ M.comap f from he ▸ mem_top x)

omit [Finite G] in
/-- Equality follows once the actual unique maximal subgroup is placed in M.
This explicit premise is a remaining source deduction, not an axiom. -/
theorem maximal_eq_overlap_of_image_le (f : X →* G) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {M : Subgroup G}
    (hSM : (S : Subgroup X).map f ≤ M) (hescape : ¬ f.range ≤ M)
    (hmax : (minimalParabolicMax S hP).map f ≤ M) :
    minimalParabolicMax S hP = M.comap f :=
  le_antisymm (map_le_iff_le_comap.mp hmax) (overlap_le_maximal f S hP hSM hescape)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

end
