module

public import Stellmacher.SectionFiveToSeven.Defs

/-!
# Normality of the omega-one center in a Section 5 family member

If `P` belongs to `PFamily ⊤ S` and `omegaOneCenter S` is normal in `P`,
then all of `P` centralizes `omegaOneCenter S`.  This supplies the implicit
Frattini step used in the proof of Stellmacher (5.1), alternative (c1).

Indeed, inside `P` let `T` be the Sylow 2-subgroup representing `S`, and let
`C = C_P(omegaOneCenter S)`.  Centrality of `omegaOneCenter S` in `S` gives
`T ≤ C`.  If `C` were proper, both `C` and `N_P(T)` would lie in the unique
maximal subgroup of `P` containing `S`; the Sylow Frattini factorization
`N_P(T) ⋁ C = P` would then put `P` in that proper subgroup.  Thus `C=P`.

Source: `refs/latex/stellmacher-n-group.tex`, the proof of (5.1), journal
p. 27, in the deduction of (c1).
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem omegaOneCenter_le_centerAmbient (S : Subgroup G) :
    omegaOneCenter S ≤ (Subgroup.center S).map S.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

omit [Finite G] in
private theorem le_centralizer_omegaOneCenter (S : Subgroup G) :
    S ≤ Subgroup.centralizer (omegaOneCenter S : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨zS, hzCenter, rfl⟩ := omegaOneCenter_le_centerAmbient S hz
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hzCenter ⟨s, hs⟩).symm

private theorem le_unique_coatom
    {K S : Subgroup G} {M : Subgroup K}
    (_hMmax : IsCoatom M)
    (_hSM : S.subgroupOf K ≤ M)
    (huniq : ∀ M' : Subgroup K, IsCoatom M' →
      S.subgroupOf K ≤ M' → M' = M)
    {L : Subgroup K} (hSL : S.subgroupOf K ≤ L) (hL : L ≠ ⊤) : L ≤ M := by
  obtain ⟨M', hM'max, hLM'⟩ := (eq_top_or_exists_le_coatom L).resolve_left hL
  rw [← huniq M' hM'max (hSL.trans hLM')]
  exact hLM'

public theorem normalInOmega_imp_le_centralizer
    (S P : Subgroup G)
    (hP : P ∈ PFamily (⊤ : Subgroup G) S)
    (hNormal : NormalIn (omegaOneCenter S) P) :
    P ≤ Subgroup.centralizer (omegaOneCenter S : Set G) := by
  classical
  rcases hP with ⟨⟨_hPtop, ⟨hSP, T, hTmap⟩, _hcoreNe, hSneCore⟩,
    _hSP', M, hMmax, hSM, huniq⟩
  let A : Subgroup P := (omegaOneCenter S).subgroupOf P
  let : A.Normal := hNormal.2
  let CP : Subgroup P := Subgroup.centralizer (A : Set P)
  let : CP.Normal := inferInstance
  have hT_eq : (T : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_subtype_inj.mp
    rw [hTmap, Subgroup.map_subgroupOf_eq_of_le hSP]
  have hT_le_CP : (T : Subgroup P) ≤ CP := by
    rw [hT_eq]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    have hsS : (s : G) ∈ S := hs
    have haA : (a : G) ∈ omegaOneCenter S := ha
    exact (Subgroup.mem_centralizer_iff.mp
      (le_centralizer_omegaOneCenter S hsS) (a : G) haA)
  have hNormalizer_ne_top : Subgroup.normalizer ((T : Subgroup P) : Set P) ≠ ⊤ := by
    intro htop
    have hTnormal : (T : Subgroup P).Normal :=
      Subgroup.normalizer_eq_top_iff.mp htop
    have hT_le_core : (T : Subgroup P) ≤ pCore 2 P := by
      exact le_sSup ⟨hTnormal, T.isPGroup'⟩
    have hcore_le_T : pCore 2 P ≤ (T : Subgroup P) :=
      (pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T
    apply hSneCore
    calc
      S = (T : Subgroup P).map P.subtype := hTmap.symm
      _ = (pCore 2 P).map P.subtype :=
        congrArg (fun X : Subgroup P => X.map P.subtype)
          (le_antisymm hT_le_core hcore_le_T)
      _ = twoCoreIn P := rfl
  have hNormalizer_le_M : Subgroup.normalizer ((T : Subgroup P) : Set P) ≤ M := by
    apply le_unique_coatom hMmax hSM huniq
    · rw [← hT_eq]
      exact Subgroup.le_normalizer (H := (T : Subgroup P))
    · exact hNormalizer_ne_top
  by_contra hnot
  have hCP_ne_top : CP ≠ ⊤ := by
    intro htop
    apply hnot
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    let pP : P := ⟨p, hp⟩
    let aP : P := ⟨a, hNormal.1 ha⟩
    have hpCP : pP ∈ CP := htop ▸ Subgroup.mem_top pP
    have hcomm := Subgroup.mem_centralizer_iff.mp hpCP aP ha
    exact congrArg Subtype.val hcomm
  have hCP_le_M : CP ≤ M := by
    apply le_unique_coatom hMmax hSM huniq
    · rw [← hT_eq]
      exact hT_le_CP
    · exact hCP_ne_top
  have hfrattini :
      Subgroup.normalizer ((T : Subgroup P) : Set P) ⊔ CP = ⊤ :=
    Sylow.normalizer_sup_eq_top' T hT_le_CP
  have : (⊤ : Subgroup P) ≤ M := hfrattini ▸ sup_le hNormalizer_le_M hCP_le_M
  exact hMmax.1 (top_le_iff.mp this)

end Stellmacher.SectionsFiveToSeven
