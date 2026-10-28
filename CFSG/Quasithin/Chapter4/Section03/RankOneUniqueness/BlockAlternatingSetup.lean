module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternating
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore

/-!
# The literal pushing-up subgroups in the A₇ branch

The common source configuration already gives O₂(KS) ≤ O₂(I): take its
Sylow intersection inside H, then restrict the core to IS. It also gives
normalization of R by S, normalization of Λ by S, and C.6.4(II).
Once the marked action proves T = SΛ, the strict Sylow intersection gives
R < Λ. The remaining inputs to the constructor below are precisely the
A₇ model and its marked quotient, residual, and Levi action.

Source: Aschbacher--Smith, original 4.3.7, printed p.616, verifying
C.6.2 and C.6.4 for (K,R,S,Λ,KS).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
/-- The two-core of KS lies in the original R = O₂(I). -/
theorem SourceConfiguration.block_join_core_le (c : SourceConfiguration T L) :
    (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).pCoreIn 2 ≤ c.I.pCoreIn 2 := by
  let S := (T : Subgroup G) ⊓ c.H
  let J := c.K.map c.H.subtype ⊔ S
  have hJH : J ≤ c.H := sup_le (map_subtype_le _) inf_le_right
  obtain ⟨P,hP⟩ := c.sylow
  have hPJ : (P : Subgroup c.H) ≤ J.subgroupOf c.H := by
    intro p hp
    apply (le_sup_right : S ≤ J)
    change (p : G) ∈ (T : Subgroup G) ⊓ c.H
    rw [← hP]
    exact mem_map_of_mem c.H.subtype hp
  have hcore := map_mono (f := c.H.subtype)
    (pCoreIn_le_sylow (J.subgroupOf c.H) (P.subtype hPJ))
  rw [map_pCoreIn_of_injective 2 _ c.H.subtype c.H.subtype_injective,
    map_subgroupOf_eq_of_le hJH, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hPJ, hP] at hcore
  have hIJ : c.I ⊔ S ≤ J := by
    rw [c.I_eq]
    exact sup_le (sup_le (c.le_component.trans le_sup_left)
      (c.core_sylow.le.trans (inf_le_left.trans le_sup_right))) le_sup_right
  have hr := (le_inf (hcore.trans (le_sup_right : S ≤ c.I ⊔ S)) le_rfl).trans
    (inf_pCoreIn_le_of_le 2 hIJ)
  exact hr.trans_eq c.core_join.symm

omit [Finite G] in
/-- In T = SΛ, the strict intersection S < T forces the original R < Λ. -/
theorem SourceConfiguration.core_lt_of_sylow_factorization (c : SourceConfiguration T L)
    (hfactor : (T : Subgroup G) = ((T : Subgroup G) ⊓ c.H) ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    c.I.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply lt_of_le_not_ge (c.core_sylow.le.trans inf_le_right)
  intro hh
  have hTS : (T : Subgroup G) ≤ (T : Subgroup G) ⊓ c.H := by
    conv_lhs => rw [hfactor]
    exact sup_le le_rfl (hh.trans (c.core_sylow.le.trans inf_le_left))
  exact c.sylow_strict.not_ge hTS

/-- Construct every structural C.6 input from the source configuration; only
the marked A₇ action and its residual/Levi calculations are parameters. -/
def SourceConfiguration.alternating_pushingUp_input (c : SourceConfiguration T L)
    (ha : ChapterC.IsAlternatingBlock (c.K.map c.H.subtype) 7)
    (hfactor : (T : Subgroup G) = ((T : Subgroup G) ⊓ c.H) ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hres : (pResidual 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)).map
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).subtype = c.K.map c.H.subtype)
    (e : ((c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) ⧸
      pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)) ≃*
        Equiv.Perm (Fin 7))
    (he : ((c.I.pCoreIn 2).subgroupOf (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map
      (e.toMonoidHom.comp (QuotientGroup.mk'
        (pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)))) =
          zpowers (Equiv.swap (0 : Fin 7) 1))
    (hlevi : (pResidual 2 (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G) : Subgroup G)).map
      (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G)).subtype ≤
        normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    ChapterC.Section06.AlternatingCentralVector.Input
      (c.K.map c.H.subtype) (c.I.pCoreIn 2) ((T : Subgroup G) ⊓ c.H)
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) where
  block := ha
  residual := hres
  quotientIso := e
  transposition := he
  core_le := c.block_join_core_le
  R_le_S := c.core_sylow.le.trans inf_le_left
  S_two := T.isPGroup'.to_le inf_le_left
  S_normalizes_R := by
    rw [c.core_join]
    exact le_sup_right.trans ((c.I ⊔ ((T : Subgroup G) ⊓ c.H)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (c.I ⊔ ((T : Subgroup G) ⊓ c.H))
        (pCore 2 (c.I ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))))
  S_normalizes_Λ :=
    (inf_le_left.trans le_sup_right).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
          (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  Λ_two := pCore_isPGroup.map _
  proper := c.core_lt_of_sylow_factorization hfactor
  control := fun _ hne hAR hn => c.core_normalizer_eq_of_component_invariant hAR hne hn
  levi_normalizes := hlevi

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
