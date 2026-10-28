module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.Action

/-!
# The Burnside fusion step in the Bender geometry

An abelian subgroup weakly closed in a Sylow subgroup controls subgroup
fusion through its normalizer. We prove the required form directly:
conjugate two Sylow subgroups of the centralizer of the target subgroup,
then use weak closure to make the corrected conjugator normalize V.
The correction centralizes the target and therefore preserves the fusion.

Applied to the actual U_C and U, this constructs the moving element in
N_G(V). The model-dependent weak closure of V remains an input; it is
not inferred from mere normalization by T.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.35 and
Proposition 16.5.1, printed p.1194. Conjugation is left conjugation.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
variable {G : Type*} [Group G] [Finite G]

private theorem weakClosure_in_other_sylow {T S : Sylow 2 G} {V : Subgroup G}
    (hweak : ∀ a : G, V.conjBy a ≤ (T : Subgroup G) → V.conjBy a = V)
    (hVS : V ≤ (S : Subgroup G)) {a : G} (ha : V.conjBy a ≤ (S : Subgroup G)) :
    V.conjBy a = V := by
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G S T
  have hVs : V.conjBy s = V := hweak s (by
    rw [← hs]
    exact map_mono hVS)
  have hVas : (V.conjBy a).conjBy s = V := by
    rw [conjBy_conjBy]
    apply hweak
    rw [conjBy_mul, ← hs]
    exact map_mono ha
  have hh := congrArg (fun Q : Subgroup G => Q.conjBy s⁻¹) (hVas.trans hVs.symm)
  simpa only [conjBy_inv] using hh

private theorem normalizer_fuses_of_abelian_weakClosure (T : Sylow 2 G)
    (V B : Subgroup G) [IsMulCommutative V] (hVT : V ≤ (T : Subgroup G))
    (hweak : ∀ a : G, V.conjBy a ≤ (T : Subgroup G) → V.conjBy a = V)
    (hBV : B ≤ V) (g : G) (hBgV : B.conjBy g ≤ V) :
    ∃ a ∈ normalizer (V : Set G), B.conjBy a = B.conjBy g := by
  let C := centralizer (B.conjBy g : Set G)
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le hBgV)
  have hVgC : V.conjBy g ≤ C := by
    rintro x ⟨y, hy, rfl⟩ z ⟨w, hw, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj g) (V.le_centralizer hy w (hBV hw))
  have hpV := T.isPGroup'.of_injective (inclusion hVT) (inclusion_injective hVT)
  have hpVg : IsPGroup 2 (V.conjBy g) := hpV.map _
  obtain ⟨P, hP⟩ := (hpV.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (hpVg.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q P
  have hmap : ((V.conjBy g).subgroupOf C).map (MulAut.conj c).toMonoidHom ≤
      (P : Subgroup C) := by
    rw [← hc]
    exact map_mono hQ
  have hcomp : C.subtype.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (c : G)).toMonoidHom.comp C.subtype := by
    ext x
    rfl
  have hconj := map_mono (f := C.subtype) hmap
  rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le hVgC] at hconj
  have hVP : V ≤ (P : Subgroup C).map C.subtype := by
    rw [← map_subgroupOf_eq_of_le hVC]
    exact map_mono hP
  obtain ⟨S, hS⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have he : V.conjBy ((c : G) * g) = V := by
    apply weakClosure_in_other_sylow hweak (hVP.trans hS)
    rw [conjBy_mul]
    exact hconj.trans hS
  refine ⟨(c : G) * g, mem_normalizer_iff_map_conj_eq.mpr he, ?_⟩
  rw [conjBy_mul]
  exact mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ c.property)

/-- Construct a moving conjugator using weak closure of the actual abelian space V. -/
theorem fusion_mover {T : Sylow 2 G} {L R : Subgroup G} {g : G}
    [IsElementaryAbelian 2 (benderSpace T L)]
    (hweak : ∀ a : G, (benderSpace T L).conjBy a ≤ (T : Subgroup G) →
      (benderSpace T L).conjBy a = benderSpace T L)
    (hconj : R = (commutingSylow T L).conjBy g)
    (hU : omegaOneAmbient R ≤ benderSpace T L) :
    ∃ a ∈ normalizer (benderSpace T L : Set G),
      (omegaOneAmbient (commutingSylow T L)).conjBy a = omegaOneAmbient R := by
  have he := omega_conjugate hconj
  obtain ⟨a, ha, heq⟩ := normalizer_fuses_of_abelian_weakClosure T (benderSpace T L)
    (omegaOneAmbient (commutingSylow T L)) (benderSpace_le_sylow T L) hweak
    le_sup_left g (he ▸ hU)
  exact ⟨a, ha, heq.trans he.symm⟩

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
