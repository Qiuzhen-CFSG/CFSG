module

public import CFSG.Quasithin.ChapterB.Section06To07.Residual
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.MinimalSylowSupplementKernel
public import Theory.GroupAction.Quotient
public import Mathlib.GroupTheory.Frattini
public import Mathlib.RepresentationTheory.Basic

-- This leaf continues the proof of the normal-core construction in Structure.
-- Access to its body stays private, as in the sibling Residual proof module.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Module kernels and the Frattini quotient of a minimal parabolic

The normal-subgroup dichotomy proves (6a) and the containment in (6b).
The Sylow assertion of (6b) and the Frattini identity (7) retain precisely
the earlier source (5), that `Q = O₂(H)` is Sylow in `J`, for the parent
assembly to discharge. The original `J` is not assumed to be odd.

For (6c), take the preimage `I` of the quotient two-core. Its Sylow
intersection `S = T ∩ I` supplements the kernel and is normalized by `T`.
The Frattini argument and unique maximality force `S` to be normal in `H`,
so `S ≤ Q` and the quotient two-core is trivial. For (7), source (5) makes
`J.map (QuotientGroup.mk' Q)` odd. The odd normal minimal-supplement lemma
places it in the actual Frattini subgroup; maximality gives the reverse
inclusion. The final module corollaries use the literal representation kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.6.8(6a)--(6c) and (7), printed pp.114–115.
-/

public section
namespace CFSG.Quasithin.ChapterB

open Subgroup

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem minimalParabolic_join_eq_top_of_le_max
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    {C : Subgroup H} (hCM : C ≤ minimalParabolicMax T hP)
    (hTC : (T : Subgroup H) ⊔ C = ⊤) : False := by
  have hle : (T : Subgroup H) ⊔ C ≤ minimalParabolicMax T hP :=
    sup_le (minimalParabolicMax_spec T hP).2 hCM
  exact (minimalParabolicMax_spec T hP).1.ne_top (top_unique (hTC ▸ hle))

/-- B.6.8(6a), in the exact residual form used by the source proof. -/
public theorem minimalParabolic_normal_le_core_of_residual_not_le
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (C : Subgroup H) [C.Normal]
    (hKC : ¬ minimalParabolicResidual (H := H) ≤ C) :
    C ≤ minimalParabolicCore T hP := by
  rcases minimalParabolic_normal_subgroup_residual_dichotomy T hP C with hCJ | hKC'
  · exact hCJ
  · exact (hKC hKC').elim

/-- B.6.8(6b), before the earlier 2-closedness input is discharged. -/
public theorem minimalParabolic_normal_le_core_of_le_max
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (C : Subgroup H) [C.Normal]
    (hCM : C ≤ minimalParabolicMax T hP) :
    C ≤ minimalParabolicCore T hP := by
  rcases minimalParabolic_normal_subgroup_dichotomy T hP C with hCJ | hTC
  · exact hCJ
  · exact (minimalParabolic_join_eq_top_of_le_max T hP hCM hTC).elim

/-- The precise earlier source premise for B.6.8(5): the ambient two-core is
Sylow in the core `J`, expressed with the literal subgroup-of inclusion. -/
public abbrev minimalParabolicTwoCoreSylowPremise (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : Prop :=
  ¬ 2 ∣ ((minimalParabolicTwoCore (H := H)).subgroupOf
    (minimalParabolicCore T hP)).index

/-- The source (5) premise is exactly Sylow membership of the intrinsic
copy of `O₂(H)` in `J`. Its two-group property already follows from `pCore`. -/
theorem minimalParabolicTwoCoreSylowPremise_iff
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) :
    minimalParabolicTwoCoreSylowPremise T hP ↔
      ∃ P : Sylow 2 (minimalParabolicCore T hP),
        (P : Subgroup (minimalParabolicCore T hP)) =
          (minimalParabolicTwoCore (H := H)).subgroupOf (minimalParabolicCore T hP) := by
  constructor
  · intro h
    exact ⟨(pCore_isPGroup.comap_subtype (K := minimalParabolicCore T hP)).toSylow h, rfl⟩
  · rintro ⟨P, he⟩
    change ¬ 2 ∣ ((minimalParabolicTwoCore (H := H)).subgroupOf
      (minimalParabolicCore T hP)).index
    rw [← he]
    exact P.not_dvd_index

/-- The Sylow conclusion in B.6.8(6b), with source (5) explicit. -/
public theorem minimalParabolic_normal_sylow_of_source5
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (C : Subgroup H) [C.Normal]
    (hCM : C ≤ minimalParabolicMax T hP)
    (hQJ : minimalParabolicTwoCoreSylowPremise T hP) :
    ∃ P : Sylow 2 C,
      (P : Subgroup C).map C.subtype = minimalParabolicTwoCore (H := H) ⊓ C := by
  have hCJ : C ≤ minimalParabolicCore T hP :=
    minimalParabolic_normal_le_core_of_le_max T hP C hCM
  let J := minimalParabolicCore T hP
  let Q := minimalParabolicTwoCore (H := H)
  have hnot : ¬ 2 ∣ (Q.subgroupOf C).index := by
    intro hd
    apply hQJ
    have hd' : 2 ∣ (Q.subgroupOf J).relIndex (C.subgroupOf J) := by
      rwa [relIndex_subgroupOf hCJ]
    exact hd'.trans ((Q.subgroupOf J).relIndex_dvd_index_of_normal (C.subgroupOf J))
  let P : Sylow 2 C := (pCore_isPGroup.comap_subtype (K := C)).toSylow hnot
  refine ⟨P, ?_⟩
  exact subgroupOf_map_subtype Q C

/- The preimage calculation used in (6c).  It is kept separate so that the
quotient statement below exposes the actual preimage subgroup. -/
public theorem minimalParabolic_quotient_twoCore_eq_bot_of_kernel
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (C : Subgroup H) [C.Normal]
    (hCM : C ≤ minimalParabolicMax T hP)
    (hQC : minimalParabolicTwoCore (H := H) ≤ C) :
    pCore 2 (H ⧸ C) = ⊥ := by
  let q := QuotientGroup.mk' C
  let R : Subgroup (H ⧸ C) := pCore 2 (H ⧸ C)
  let I : Subgroup H := R.comap q
  have hCI : C ≤ I := by
    intro x hx
    change q x ∈ R
    have he : q x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [he]
    exact R.one_mem
  have hRleT : R ≤ (T : Subgroup H).map q :=
    pCore_isPGroup.le_sylow_of_normal (T.mapSurjective (QuotientGroup.mk'_surjective C))
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal I
  let S0 : Subgroup H := (T : Subgroup H) ⊓ I
  have hS0 : (S : Subgroup I).map I.subtype = S0 := by
    rw [hS, subgroupOf_map_subtype]
  have hSI : I = C ⊔ S0 := by
    apply le_antisymm
    · intro x hx
      have hqx : q x ∈ R := hx
      obtain ⟨t, ht, htx⟩ := hRleT hqx
      have hct : t⁻¹ * x ∈ C := QuotientGroup.eq.1 htx
      have htS : t ∈ S0 := ⟨ht, by change q t ∈ R; rwa [htx]⟩
      have hm : t * (t⁻¹ * x) ∈ C ⊔ S0 :=
        (C ⊔ S0).mul_mem ((le_sup_right : S0 ≤ C ⊔ S0) htS)
          ((le_sup_left : C ≤ C ⊔ S0) hct)
      simpa only [mul_inv_cancel_left] using hm
    · exact sup_le hCI inf_le_right
  have hTN : (T : Subgroup H) ≤ normalizer (S0 : Set H) := by
    have hn := (normal_subgroupOf_iff_le_normalizer_inf
      (H := I) (K := (T : Subgroup H))).mp inferInstance
    simpa only [inf_comm] using hn
  have hNorm : normalizer (S0 : Set H) ⊔ I = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (G := H) S
    rw [hS0] at h
    exact h
  have hImax : I ≤ minimalParabolicMax T hP := by
    rw [hSI]
    exact sup_le hCM (inf_le_left.trans (minimalParabolicMax_spec T hP).2)
  have hNormTop : normalizer (S0 : Set H) = ⊤ := by
    rcases eq_top_or_exists_le_coatom (normalizer (S0 : Set H)) with h | ⟨M, hM, hNM⟩
    · exact h
    · have hMT : M = minimalParabolicMax T hP :=
        minimalParabolicMax_unique T hP hM (hTN.trans hNM)
      have htopMax : normalizer (S0 : Set H) ⊔ I ≤ minimalParabolicMax T hP :=
        sup_le (hNM.trans_eq hMT) hImax
      exact ((minimalParabolicMax_spec T hP).1.ne_top
        (top_unique (hNorm ▸ htopMax))).elim
  have hSnormal : S0.Normal := normalizer_eq_top_iff.mp hNormTop
  have hSleQ : S0 ≤ minimalParabolicTwoCore (H := H) :=
    le_sSup ⟨hSnormal, T.isPGroup'.to_le inf_le_left⟩
  have hIleC : I ≤ C := by
    rw [hSI]
    exact sup_le le_rfl (hSleQ.trans hQC)
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C x
  exact (QuotientGroup.eq_one_iff y).2 (hIleC hx)

/-- Source (5) makes the image of `J` in the original quotient `H/O₂(H)`
odd. It makes no assertion that the original subgroup `J` is odd. -/
theorem minimalParabolic_core_image_odd_of_source5
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hQJ : minimalParabolicTwoCoreSylowPremise T hP) :
    Odd (Nat.card ((minimalParabolicCore T hP).map
      (QuotientGroup.mk' (minimalParabolicTwoCore (H := H))))) := by
  rw [natCard_map_mk'_eq, ← index_eq_card]
  exact Nat.not_even_iff_odd.mp (fun h => hQJ (even_iff_two_dvd.mp h))

private theorem minimalParabolic_minimal_core_supplement
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (L : Subgroup H) (hTL : (T : Subgroup H) ≤ L)
    (hs : L ⊔ minimalParabolicCore T hP = ⊤) : L = ⊤ := by
  rcases eq_top_or_exists_le_coatom L with h | ⟨M, hM, hLM⟩
  · exact h
  · have hM' := minimalParabolicMax_unique T hP hM (hTL.trans hLM)
    have hle : L ⊔ minimalParabolicCore T hP ≤ minimalParabolicMax T hP :=
      sup_le (hLM.trans_eq hM') (normalCore_le _)
    exact ((minimalParabolicMax_spec T hP).1.ne_top (top_unique (hs ▸ hle))).elim

/-- B.6.8(7), with precisely the earlier source (5) retained for its assembly
owner. Both the image of `J` and the Frattini subgroup are the actual subgroups
of `H/O₂(H)`. -/
theorem minimalParabolic_core_image_eq_frattini_of_source5
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hQJ : minimalParabolicTwoCoreSylowPremise T hP) :
    (minimalParabolicCore T hP).map
      (QuotientGroup.mk' (minimalParabolicTwoCore (H := H))) =
        frattini (minimalParabolicQuotient (H := H)) := by
  let Q := minimalParabolicTwoCore (H := H)
  let J := minimalParabolicCore T hP
  let M := minimalParabolicMax T hP
  let q := QuotientGroup.mk' Q
  have hq := QuotientGroup.mk'_surjective Q
  have hQleJ : Q ≤ J := minimalParabolicTwoCore_le_core T hP
  have hkerJ : q.ker ≤ J := by rwa [QuotientGroup.ker_mk']
  have hkerM : q.ker ≤ M := hkerJ.trans (normalCore_le _)
  apply le_antisymm
  · apply (T.mapSurjective hq).normal_le_frattini_of_minimal_supplement (J.map q)
      (minimalParabolic_core_image_odd_of_source5 T hP hQJ).not_two_dvd_nat
    intro L hTL hs
    have hgen : L.comap q ⊔ J = ⊤ := by
      have hm : (L.comap q ⊔ J).map q = ⊤ := by
        rw [Subgroup.map_sup, map_comap_eq_self_of_surjective hq]
        exact hs
      have hc := congrArg (Subgroup.comap q) hm
      rwa [comap_map_eq_self (hkerJ.trans le_sup_right), comap_top] at hc
    have hL := minimalParabolic_minimal_core_supplement T hP (L.comap q)
      (map_le_iff_le_comap.mp hTL) hgen
    apply comap_injective hq
    simpa only [comap_top] using hL
  · have hM := (minimalParabolicMax_spec T hP).1
    have hm : M.map q ≠ ⊤ := by
      intro he
      have hc := congrArg (Subgroup.comap q) he
      rw [comap_map_eq_self hkerM, comap_top] at hc
      exact hM.ne_top hc
    obtain ⟨X, hX, hMX⟩ := (eq_top_or_exists_le_coatom (M.map q)).resolve_left hm
    have hpre : X.comap q = M :=
      (hM.le_iff_eq (isCoatom_comap_of_surjective hq hX).ne_top).mp
        (map_le_iff_le_comap.mp hMX)
    have hFM : (frattini (H ⧸ Q)).comap q ≤ M :=
      (comap_mono (frattini_le_coatom hX)).trans_eq hpre
    have hFJ : (frattini (H ⧸ Q)).comap q ≤ J :=
      minimalParabolic_normal_le_core_of_le_max T hP _ hFM
    have hmap := map_mono (f := q) hFJ
    rwa [map_comap_eq_self_of_surjective hq] at hmap

section Module
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- B.6.8(6a) for the actual binary module. Here `ρ.ker = C_H(W)`:
membership means that `ρ g` is the identity on every vector of `W`. -/
theorem minimalParabolic_source6a
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W)
    (hK : ¬ minimalParabolicResidual (H := H) ≤ ρ.ker) :
    ρ.ker ≤ minimalParabolicCore T hP :=
  minimalParabolic_normal_le_core_of_residual_not_le T hP ρ.ker hK

/-- B.6.8(6b) for the actual binary module, conditional only on source (5).
The Sylow image is `C_Q(W) = Q ∩ C_H(W)`, without assuming `Q ≤ C_H(W)`. -/
theorem minimalParabolic_source6b_of_source5
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hQJ : minimalParabolicTwoCoreSylowPremise T hP)
    (ρ : Representation (ZMod 2) H W)
    (hM : ρ.ker ≤ minimalParabolicMax T hP) :
    ρ.ker ≤ minimalParabolicCore T hP ∧
      ∃ P : Sylow 2 ρ.ker,
        (P : Subgroup ρ.ker).map ρ.ker.subtype =
          minimalParabolicTwoCore (H := H) ⊓ ρ.ker :=
  ⟨minimalParabolic_normal_le_core_of_le_max T hP ρ.ker hM,
    minimalParabolic_normal_sylow_of_source5 T hP ρ.ker hM hQJ⟩

/-- B.6.8(6c) on the original binary module and the literal quotient by its
pointwise kernel. This proof does not depend on source (5). -/
theorem minimalParabolic_source6c
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (ρ : Representation (ZMod 2) H W)
    (hQ : minimalParabolicTwoCore (H := H) ≤ ρ.ker)
    (hM : ρ.ker ≤ minimalParabolicMax T hP) :
    pCore 2 (H ⧸ ρ.ker) = ⊥ :=
  minimalParabolic_quotient_twoCore_eq_bot_of_kernel T hP ρ.ker hM hQ

end Module

end CFSG.Quasithin.ChapterB
end
