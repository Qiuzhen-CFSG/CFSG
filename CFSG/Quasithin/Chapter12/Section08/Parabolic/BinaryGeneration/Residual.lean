module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Generation
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The embedded residual of the binary parabolic

The cover P=O₂(P)I₂ makes P/I₂ a two-group, hence O²(P)≤I₂.
The original Sylow supplements O²(P) and normalizes U, making O²(P)U
P-normal and giving I₂=O²(P)U. Its embedded two-residual is O²(P).
Characteristicity then supplies relative normality in the actual G₂.

Source: Aschbacher–Smith, Lemma 12.8.9(1), printed p.853.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The source residual supplement, obtained from the actual core cover. -/
theorem binary_residual_supplement (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (L : Subgroup G) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L) :
    F.I₂ L = (pResidual 2 (F.P L)).map (F.P L).subtype ⊔ F.U ∧
      (pResidual 2 (F.I₂ L)).map (F.I₂ L).subtype =
        (pResidual 2 (F.P L)).map (F.P L).subtype := by
  let P := F.P L
  let I := F.I₂ L
  let R := (pResidual 2 P).map P.subtype
  have hIP : I ≤ P := le_sup_right.trans hfactor.ge
  have hTP : (T : Subgroup G) ≤ P := F.binary_sylow_le_P L
  have hUP : F.U ≤ P := F.binary_U_le_P hn L hsquare
  have hIN : P ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  let : (I.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hIP).mpr hIN
  have hsup : I.subgroupOf P ⊔ (P.pCoreIn 2).subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hIP,
      map_subgroupOf_eq_of_le (pCoreIn_le 2 P), ← MonoidHom.range_eq_map, range_subtype]
    exact (sup_comm _ _).trans hfactor.symm
  have hRI : R ≤ I := by
    have hr : pResidual 2 P ≤ I.subgroupOf P := sInf_le ⟨inferInstance,
      isPGroup_quotient_of_sup_eq_top _ _ (isPGroup_pCoreIn 2 P).comap_subtype hsup⟩
    have hh := map_mono (f := P.subtype) hr
    rwa [map_subgroupOf_eq_of_le hIP] at hh
  have hRN : P ≤ normalizer (R : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hPT : P = R ⊔ (T : Subgroup G) := by
    have hh := congrArg (fun A : Subgroup P => A.map P.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTP))
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
    change R ⊔ ((T : Subgroup G).subgroupOf P).map P.subtype = P at hh
    rw [map_subgroupOf_eq_of_le hTP] at hh
    exact hh.symm
  have hTN : (T : Subgroup G) ≤ normalizer ((R ⊔ F.U : Subgroup G) : Set G) :=
    (le_inf (hTP.trans hRN) ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hPN : P ≤ normalizer ((R ⊔ F.U : Subgroup G) : Set G) := by
    rw [hPT]
    exact sup_le (le_sup_left.trans (R ⊔ F.U).le_normalizer) hTN
  have hIR : I = R ⊔ F.U := le_antisymm (conjugateSpanBy_le le_sup_right hPN)
    (sup_le hRI (le_conjugateSpanBy _ _))
  refine ⟨hIR, ?_⟩
  change (pResidual 2 I).map I.subtype = R
  rw [hIR]
  exact embedded_pResidual_join_pGroup R F.U (isPPerfect_embedded_pResidual 2 P)
    (F.binary_U_isPGroup hn hsquare) (hUP.trans hRN)

/-- Characteristicity of O²(I₂) supplies the actual relative G₂ normality. -/
theorem binary_residual_normal_in_G₂ (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (L : Subgroup G) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hIG : F.I₂ L ≤ F.Gi 2) (hnormal : ((F.I₂ L).subgroupOf (F.Gi 2)).Normal) :
    (((pResidual 2 (F.P L)).map (F.P L).subtype).subgroupOf (F.Gi 2)).Normal := by
  have he := (F.binary_residual_supplement hn L hsquare hfactor).2
  have hRG : (pResidual 2 (F.I₂ L)).map (F.I₂ L).subtype ≤ F.Gi 2 :=
    (map_subtype_le _).trans hIG
  rw [← he]
  apply (normal_subgroupOf_iff_le_normalizer hRG).mpr
  exact ((normal_subgroupOf_iff_le_normalizer hIG).mp hnormal).trans
    (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pResidual 2 (F.I₂ L)))

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
