module

public import Stellmacher.SectionFiveToSeven.PFamilyBridge

/-!
# Conjugation invariance of the Section 5 local family

An ambient group automorphism carries `PFamily U S` onto the corresponding
family over the images of `U` and `S`. The proof transports a Sylow witness,
the ambient 2-core, and the unique maximal subgroup over `S` through the
induced isomorphism between a subgroup and its image.

The conjugation corollary is the step used in Stellmacher (5.1): if `x`
normalizes `S`, then `P₂ = P₁^x` remains in `PFamily ⊤ S`.

Source: `refs/latex/stellmacher-n-group.tex`, the definition of `𝒫(N,S)` and
the assignment `P₂=P₁^x` in the proof of (5.1), journal p. 27.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

variable {G : Type u} [Group G]

private theorem map_internal_ambient
    (e : G ≃* G) (P : Subgroup G) (M : Subgroup P) :
    let eP : P ≃* P.map e.toMonoidHom :=
      P.equivMapOfInjective e.toMonoidHom e.injective
    (M.map eP.toMonoidHom).map (P.map e.toMonoidHom).subtype =
      (M.map P.subtype).map e.toMonoidHom := by
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem twoCoreAmbient_map_equiv
    (e : G ≃* G) (P : Subgroup G) :
    twoCoreAmbient (P.map e.toMonoidHom) =
      (twoCoreAmbient P).map e.toMonoidHom := by
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  have hcore : (pCore 2 P).map eP.toMonoidHom =
      pCore 2 (P.map e.toMonoidHom) := pCore_map_iso 2 eP
  unfold twoCoreAmbient
  rw [← hcore, map_internal_ambient]

private theorem isSylowSubgroupIn_map_equiv
    [Finite G] (e : G ≃* G) (S P : Subgroup G)
    (h : IsSylowSubgroupIn S P) :
    IsSylowSubgroupIn (S.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨T, hTmap⟩ := h
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  have hePsur : Function.Surjective eP.toMonoidHom := by
    intro y
    exact ⟨eP.symm y, eP.apply_symm_apply y⟩
  let T' : Sylow 2 (P.map e.toMonoidHom) :=
    Sylow.mapSurjective hePsur T
  refine ⟨T', ?_⟩
  have hT' : (T' : Subgroup (P.map e.toMonoidHom)) =
      (T : Subgroup P).map eP.toMonoidHom :=
    Sylow.coe_mapSurjective hePsur T
  rw [hT', map_internal_ambient, hTmap]

private theorem uniqueMaximalContaining_map_equiv
    (e : G ≃* G) (S P : Subgroup G)
    (h : IsUniqueMaximalContaining S P) :
    IsUniqueMaximalContaining (S.map e.toMonoidHom)
      (P.map e.toMonoidHom) := by
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨M, hMcoatom, hSM, hMunique⟩ := h
  refine ⟨M.map eP.toMonoidHom,
    (OrderIso.isCoatom_iff eP.mapSubgroup M).2 hMcoatom, ?_, ?_⟩
  · rw [map_internal_ambient]
    exact Subgroup.map_mono hSM
  · intro N hNcoatom hSN
    let M' : Subgroup P := N.map eP.symm.toMonoidHom
    have hM'coatom : IsCoatom M' :=
      (OrderIso.isCoatom_iff eP.symm.mapSubgroup N).2 hNcoatom
    have hforward : M'.map eP.toMonoidHom = N := by
      dsimp only [M']
      rw [Subgroup.map_map]
      have hcomp : eP.toMonoidHom.comp eP.symm.toMonoidHom =
          MonoidHom.id (P.map e.toMonoidHom) := by
        ext x
        exact congrArg Subtype.val (eP.apply_symm_apply x)
      rw [hcomp, Subgroup.map_id]
    have hSM' : S ≤ M'.map P.subtype := by
      apply (Subgroup.map_le_map_iff_of_injective
        (f := e.toMonoidHom) e.injective).mp
      rw [← map_internal_ambient, hforward]
      exact hSN
    have hM'eq : M' = M := hMunique M' hM'coatom hSM'
    rw [← hforward, hM'eq]

private theorem pSet_map_equiv
    [Finite G] (e : G ≃* G) (U S P : Subgroup G)
    (hP : P ∈ SectionThree.PSet U S) :
    P.map e.toMonoidHom ∈
      SectionThree.PSet (U.map e.toMonoidHom) (S.map e.toMonoidHom) := by
  rcases hP with ⟨⟨hPU, hSylow, hcore, hSne⟩, hUnique⟩
  refine ⟨⟨Subgroup.map_mono hPU,
    isSylowSubgroupIn_map_equiv e S P hSylow, ?_, ?_⟩,
    uniqueMaximalContaining_map_equiv e S P hUnique⟩
  · rw [twoCoreAmbient_map_equiv]
    intro hbot
    apply hcore
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using hbot
  · rw [twoCoreAmbient_map_equiv]
    intro heq
    apply hSne
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective heq

/-- An ambient automorphism transports the Section 5 local family, including
the Sylow subgroup and unique-maximal-overgroup conditions. -/
public theorem pFamily_map_equiv_iff
    [Finite G] (e : G ≃* G) (U S P : Subgroup G) :
    P.map e.toMonoidHom ∈
        PFamily (U.map e.toMonoidHom) (S.map e.toMonoidHom) ↔
      P ∈ PFamily U S := by
  rw [pFamily_iff_pSet, pFamily_iff_pSet]
  constructor
  · intro hP
    have hback := pSet_map_equiv e.symm
      (U.map e.toMonoidHom) (S.map e.toMonoidHom)
      (P.map e.toMonoidHom) hP
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp
    simpa only [Subgroup.map_map, hcomp, Subgroup.map_id] using hback
  · exact pSet_map_equiv e U S P

private theorem map_conj_eq_self_of_mem_normalizer
    (S : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    S.map (MulAut.conj x).toMonoidHom = S := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change x⁻¹ * y * x ∈ S ↔ y ∈ S
  have hn := (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * y * x))
  simpa [mul_assoc] using hn

/-- Conjugation by an element normalizing `S` preserves membership in the
global local family `PFamily ⊤ S`. -/
public theorem conjugateBy_mem_pFamily_iff
    [Finite G] (S P : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (S : Set G)) :
    conjugateBy P x ∈ PFamily (⊤ : Subgroup G) S ↔
      P ∈ PFamily (⊤ : Subgroup G) S := by
  have hS := map_conj_eq_self_of_mem_normalizer S x hx
  have hmap :=
    pFamily_map_equiv_iff (MulAut.conj x) (⊤ : Subgroup G) S P
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective, hS] at hmap
  exact hmap

end Stellmacher.SectionsFiveToSeven
