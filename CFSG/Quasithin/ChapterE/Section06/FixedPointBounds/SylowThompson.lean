module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Contracts
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.Transport

/-!
# The Sylow preparation and small-parabolic branch of E.6.27

Start with a Sylow subgroup of `C_M(U)`. The TI condition puts it in
`M_V = N_G(V)`, where Sylow conjugacy moves its ambient image into `T`.
Its maximality identifies the image with `C_T(U^g)`. Higher Thompson
transport, the strict rank bound proved in `Transport`, and E.6.1 uniqueness
control its normalizer. Conjugating back gives the required local Sylow
normalizer bound for the original `U`.

For any promoted Sylow of `C_G(U)` with that image, a minimal parabolic of
`O^{2'}(C_G(U))` contains its residual Sylow. Its literal embedding followed
by the same conjugation transports both its Sylow and the E.1.6 parameter.
Exact E.6.26 then supplies the small-parabolic containment, which is again
transported back. The final existence theorem matches both inputs of
`FixedPointBounds.centralizer_le_of_parabolic_branches`.

E.6.26 is an explicit earlier-source input, with all its original hypotheses;
its proof from E.5.2 belongs to the E.6 owner. This module does not assert the
large-parabolic branch or the completed Proposition E.6.27.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.256--257 (PDF pp.267--268), Lemma E.6.26 and Proposition E.6.27.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The first paragraph of E.6.27: construct the `M_V` placement and prove the
normalizer bound for the original Sylow image. No placement is assumed. -/
theorem placement {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G))) :
    ∃ g ∈ localNormalizer M V,
      let A := (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype
      let Ag := A.map (MulAut.conj g).toMonoidHom
      Ag = (T : Subgroup G) ⊓ centralizer (U.map (MulAut.conj g).toMonoidHom : Set G) ∧
      sylowCentralizer (T : Subgroup G) V ≤ Ag ∧ Ag ≤ T ∧
      thompsonJ Ag j ≤ centralizer (V : Set G) ∧ normalizer (A : Set G) ≤ M := by
  let C := M ⊓ centralizer (U : Set G)
  let A := (P : Subgroup C).map C.subtype
  have hAN : A ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans (h.localCentralizer_le_normalizer hU hUV)
  obtain ⟨g, hg⟩ := exists_conj_le (normalizer (V : Set G)) A hAN
    (P.isPGroup'.map _) (T.subtype h.sylow_le_normalizer)
  let e : G ≃* G := MulAut.conj (g : G)
  have hgM : (g : G) ∈ M := h.normalizer_le g.property
  have hVM : V.map e.toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp g.property
  have hMM : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hgM)
  have hAT : A.map e.toMonoidHom ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_le_normalizer] using hg
  have hCM : C.map e.toMonoidHom = M ⊓ centralizer (U.map e.toMonoidHom : Set G) := by
    change (M ⊓ centralizer (U : Set G)).map e.toMonoidHom = _
    rw [map_inf _ _ _ e.injective, hMM, map_centralizer]
  have hAE : A.map e.toMonoidHom ≤
      (T : Subgroup G) ⊓ centralizer (U.map e.toMonoidHom : Set G) := by
    refine le_inf hAT ?_
    have hm := map_mono (f := e.toMonoidHom) (map_subtype_le (P : Subgroup C))
    rw [hCM] at hm
    exact hm.trans inf_le_right
  let E := (T : Subgroup G) ⊓ centralizer (U.map e.toMonoidHom : Set G)
  have hEC : E ≤ C.map e.toMonoidHom := by
    rw [hCM]
    exact inf_le_inf_right _ h.sylow_le
  have hpre : E.map e.symm.toMonoidHom = A :=
    sylow_image_maximal P ((T.isPGroup'.to_le inf_le_left).map _) (by
      intro a ha
      exact ⟨e a, hAE (mem_map_of_mem _ ha), e.symm_apply_apply a⟩) (by
      rw [map_le_iff_le_comap, ← map_equiv_eq_comap_symm' e C]
      exact hEC)
  have hEq : A.map e.toMonoidHom = E := by
    rw [← hpre]
    rw [map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.apply_symm_apply x
    rw [hid, map_id]
  have hUVg : U.map e.toMonoidHom ≤ V := hVM ▸ map_mono hUV
  have hQA : sylowCentralizer (T : Subgroup G) V ≤ A.map e.toMonoidHom := by
    rw [hEq]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hUVg)
  have hJA : thompsonJ (A.map e.toMonoidHom) j ≤ centralizer (V : Set G) := by
    rw [thompsonJ_map_equiv]
    have hjmap := map_mono (f := e.toMonoidHom)
      ((thompsonJ_sylow_image_le P j).trans hJ)
    rw [map_inf _ _ _ e.injective, hMM, map_centralizer, hVM] at hjmap
    exact hjmap.trans inf_le_right
  have hN : normalizer (A : Set G) ≤ M := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_normalizer_eq_of_bijective _ e.bijective, hMM]
    exact normalizer_le_of_control h hj hQA hAT hJA
  exact ⟨g, ⟨hgM, g.property⟩, hEq, hQA, hAT, hJA, hN⟩

/-- Exact earlier-source E.6.26, with the unique maximal two-local overgroup
spelled out and all Sylow embeddings in the ambient group explicit. -/
@[expose] def E626Input (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (V M : Subgroup G), V ≠ ⊥ → IsElementaryAbelian 2 V →
    V ≤ T → (V.subgroupOf (T : Subgroup G)).Normal →
    normalizer (V : Set G) ≤ M → IsMaximalTwoLocal M →
    normalizer (sylowCentralizer (T : Subgroup G) V : Set G) ≤ M →
    (∀ N : Subgroup G, IsMaximalTwoLocal N →
      normalizer (sylowCentralizer (T : Subgroup G) V : Set G) ≤ N → N = M) →
    ∀ (j : ℕ) (H : Subgroup G) (S : Sylow 2 H), 1 ≤ j →
      generationParameter H ≤ j →
      sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup H).map H.subtype →
      (S : Subgroup H).map H.subtype ≤ T →
      (j : ℕ∞) < globalR V →
      thompsonJ ((S : Subgroup H).map H.subtype) j ≤
        (S : Subgroup H).map H.subtype ⊓ centralizer (V : Set G) →
      H ≤ M ∧ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ M

/-- Apply E.6.26 to the actual conjugated image of a residual minimal parabolic,
then transport containment back to the original `U`. -/
theorem small_parabolic_of_placement
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (h626 : E626Input G)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (g : G) (hg : g ∈ localNormalizer M V)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤
      ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype).map (MulAut.conj g).toMonoidHom)
    (hAT : ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype).map (MulAut.conj g).toMonoidHom ≤ T)
    (hJA : thompsonJ (((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype).map (MulAut.conj g).toMonoidHom) j ≤
        centralizer (V : Set G))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype)
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H)
    (hn : generationParameter H ≤ j) :
    (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
      (centralizer (U : Set G)).subtype ≤ M := by
  let C := centralizer (U : Set G)
  let f : primeToResidual 2 C →* G := C.subtype.comp (primeToResidual 2 C).subtype
  let e : G ≃* G := MulAut.conj g
  let k := e.toMonoidHom.comp f
  have hk : Function.Injective k := e.injective.comp
    (C.subtype_injective.comp (primeToResidual 2 C).subtype_injective)
  obtain ⟨R, hR⟩ := exists_sylow_map k hk (residualSylow S) H hH.1.1.le
  have hRmap : (R : Subgroup (H.map k)).map (H.map k).subtype =
      ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype).map e.toMonoidHom := by
    rw [hR]
    change (residualSylow S : Subgroup (primeToResidual 2 C)).map
      (e.toMonoidHom.comp (C.subtype.comp (primeToResidual 2 C).subtype)) = _
    rw [← map_map, ← map_map, residualSylow_map, hS]
  have hnD : generationParameter (H.map k) ≤ j := by
    rw [← generationParameter_equiv (H.equivMapOfInjective k hk)]
    exact hn
  have hD : H.map k ≤ M := (h626 T V M h.nontrivial h.elementary h.le_sylow
    h.normal_in_sylow h.normalizer_le h.maximalTwoLocal h.normalizer_sylowCentralizer_le
    (fun N hN hQN => h.unique N hN (inf_le_right.trans hQN)) j (H.map k) R hj1 hnD
    (hRmap.symm ▸ hQA) (hRmap.symm ▸ hAT) hj
    (le_inf (thompsonJ_le _ j) (hRmap.symm ▸ hJA))).1
  have hMM : M.map e.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg.1)
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [hMM]
  simpa only [map_map] using hD

/-- Supply the local Sylow, its ambient normalizer bound, and exactly the small
branch consumed by `centralizer_le_of_parabolic_branches`. Only the genuine
earlier Lemma E.6.26 remains an input; the placement and every transport are
constructed here. The final E.6.27 owner must discharge E.6.26 and construct
the independent large-parabolic branch. -/
theorem exists_preparation
    {Kc : GroupClass.{u}} {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 Kc T M V) (h626 : E626Input G)
    (hU : U ≠ ⊥) (hUV : U ≤ V) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤
      M ⊓ centralizer (V : Set G)) :
    ∃ P : Sylow 2 ↥(M ⊓ centralizer (U : Set G)),
      normalizer ((P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
        (M ⊓ centralizer (U : Set G)).subtype : Set G) ≤ M ∧
      ∀ S : Sylow 2 (centralizer (U : Set G)),
        (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
          (P : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
            (M ⊓ centralizer (U : Set G)).subtype →
        ∀ H : Subgroup (primeToResidual 2 (centralizer (U : Set G))),
          IsMinimalParabolicOver (residualSylow S) H → generationParameter H ≤ j →
          (H.map (primeToResidual 2 (centralizer (U : Set G))).subtype).map
            (centralizer (U : Set G)).subtype ≤ M := by
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥(M ⊓ centralizer (U : Set G)))
  obtain ⟨g, hg, _, hQA, hAT, hJA, hN⟩ := placement h hU hUV hj hJ P
  exact ⟨P, hN, small_parabolic_of_placement h h626 hj1 hj P g hg hQA hAT hJA⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson

end
