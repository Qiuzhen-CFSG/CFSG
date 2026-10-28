module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.SectionBound
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PResidual.PerfectCover


/-!
# Core intersections and the table bound in Lemma 8.2.7

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.718
(PDF p.735), using the L₃(4)/9 and M₂₂/10 rows of 8.2.5.

Residual monotonicity gives O²(I)≤O²(H), without the erroneous stronger
containment I≤O²(H). Restriction of cores identifies V∩O₂(I) with
V∩O₂(H) once P≤O₂(H) is established. For the dimension bound it suffices
that V∩O₂(X) lies in this B: the table and |V:B|=2 imply a quotient rank
at most five for every subgroup of B modulo its intersection with U.

These are conditional deductions. In particular they neither assume nor
claim that B≤X, and leave the source proof of P≤O₂(H) explicit.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
variable {G : Type*} [Group G]

/-- The valid residual containment for the reselected subgroup. -/
theorem pair_residual_le (I H X : Subgroup G) (hIH : I ≤ H)
    (hX : X = (pResidual 2 H).map H.subtype) :
    (pResidual 2 I).map I.subtype ≤ X := by
  rw [hX]
  exact embedded_pResidual_mono 2 hIH

/-- Once the source commutator identity puts P in O₂(H), the two definitions
of B using I and H agree; I need not be normal in H. -/
theorem pair_core_intersection (I H V : Subgroup G) (hIH : I ≤ H)
    (hVI : V ≤ I) (hP : I.pCoreIn 2 ≤ H.pCoreIn 2) :
    V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 := by
  apply le_antisymm (inf_le_inf_left V hP)
  exact le_inf inf_le_left
    ((le_inf (inf_le_left.trans hVI) inf_le_right).trans (inf_pCoreIn_le_of_le 2 hIH))

/-- The smaller residual-core intersection suffices for the upper bound;
no unproved absorption of the whole B into O²(H) is used. -/
theorem residual_core_intersection_le (X H I V : Subgroup G)
    (hXH : X ≤ H) (hHX : H ≤ normalizer (X : Set G)) (hIH : I ≤ H)
    (hVI : V ≤ I) : V ⊓ X.pCoreIn 2 ≤ V ⊓ I.pCoreIn 2 := by
  exact le_inf inf_le_left
    ((le_inf (inf_le_left.trans hVI)
      (inf_le_right.trans (pCoreIn_mono_of_normalizes hXH hHX))).trans
        (inf_pCoreIn_le_of_le 2 hIH))

variable [Finite G]

/-- The k=1 clause expressed as the binary dimension of the literal quotient. -/
theorem pair_quotient_rank_one (I H V : Subgroup G) [IsElementaryAbelian 2 V]
    (hIH : I ≤ H) (hVI : V ≤ I) (hP : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2) :
    Module.finrank (ZMod 2) (Additive (V ⧸ (V ⊓ H.pCoreIn 2).subgroupOf V)) = 1 := by
  apply (relIndex_eq_two_pow_iff_quotient_finrank V _ 1).mp
  rw [← pair_core_intersection I H V hIH hVI hP]
  simpa using hk

/-- The table gives |V:U| ≤ 64 and |V:B|=2. Every subgroup of B,
including V∩O₂(X), therefore has quotient dimension at most five modulo U. -/
theorem table_section_rank (V U B C : Subgroup G) [IsElementaryAbelian 2 C]
    (hUB : U ≤ B) (hBV : B ≤ V) (hCB : C ≤ B)
    (hVB : B.relIndex V = 2) (hVU : U.relIndex V ≤ 64) :
    Module.finrank (ZMod 2) (Additive (C ⧸ U.subgroupOf C)) ≤ 5 := by
  have hmul := relIndex_mul_relIndex U B V hUB hBV
  rw [hVB] at hmul
  have hUBcard : U.relIndex B ≤ 32 := by omega
  have hCcard : U.relIndex C ≤ 32 :=
    (relIndex_le_of_le_right hCB (U.subgroupOf B).index_ne_zero_of_finite).trans hUBcard
  rw [relIndex_eq_two_pow_quotient_finrank] at hCcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ Module.finrank (ZMod 2) (Additive (C ⧸ U.subgroupOf C)) ≤ 2 ^ 5 from hCcard)

omit [Finite G] in
/-- The two surviving rows have |U|=16 and |V|=512 or 1024. -/
theorem table_relative_index (V U : Subgroup G) (hUV : U ≤ V)
    (hU : Nat.card U = 16) (hV : Nat.card V = 512 ∨ Nat.card V = 1024) :
    U.relIndex V ≤ 64 := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) U V bot_le hUV
  rw [relIndex_bot_left, relIndex_bot_left, hU] at hc
  rcases hV with hV | hV <;> omega

/-- The bound needed by SectionBound, using the actual B=V∩O₂(I) and
only monotonicity for V∩O₂(X). -/
theorem residual_core_table_rank (X H I V U : Subgroup G)
    [IsElementaryAbelian 2 (V ⊓ X.pCoreIn 2 : Subgroup G)]
    (hXH : X ≤ H) (hHX : H ≤ normalizer (X : Set G)) (hIH : I ≤ H)
    (hVI : V ≤ I) (hUB : U ≤ V ⊓ I.pCoreIn 2)
    (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2) (hVU : U.relIndex V ≤ 64) :
    Module.finrank (ZMod 2)
      (Additive ((V ⊓ X.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ X.pCoreIn 2))) ≤ 5 :=
  table_section_rank V U (V ⊓ I.pCoreIn 2) (V ⊓ X.pCoreIn 2) hUB inf_le_left
    (residual_core_intersection_le X H I V hXH hHX hIH hVI) hk hVU

omit [Finite G] in
private theorem two_subgroup_le_core (X C : Subgroup G) (hCX : C ≤ X)
    (hC : IsPGroup 2 C) (hodd : Odd (Nat.card (X ⧸ pCore 2 X))) :
    C ≤ X.pCoreIn 2 := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let Cbar := (C.subgroupOf X).map π
  have hCb : IsPGroup 2 Cbar := hC.comap_subtype.map π
  have hCbodd : Odd (Nat.card Cbar) := hodd.of_dvd_nat Cbar.card_subgroup_dvd_card
  have hCb1 : Nat.card Cbar = 1 := hCb.card_eq_or_dvd.resolve_right
    (by simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hCbodd)
  have hCb0 : Cbar = ⊥ := (eq_bot_iff_card _).mpr hCb1
  intro c hc
  have hm : π ⟨c, hCX hc⟩ ∈ Cbar := mem_map_of_mem π hc
  rw [hCb0, mem_bot] at hm
  exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp hm)

omit [Finite G] in
/-- The source P=[P,O²(I)]U identity puts P in O₂(H). This uses the
valid residual containment and the odd quotient X/O₂(X), not I≤X. -/
theorem pair_core_le (I H X U : Subgroup G)
    (hIH : I ≤ H) (hX : X = (pResidual 2 H).map H.subtype)
    (hUI : U ≤ I) (hU : IsPGroup 2 U) (hHU : H ≤ normalizer (U : Set G))
    (hodd : Odd (Nat.card (X ⧸ pCore 2 X)))
    (hP : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) :
    I.pCoreIn 2 ≤ H.pCoreIn 2 := by
  have hXH : X ≤ H := hX ▸ map_subtype_le _
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hX]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hRX := pair_residual_le I H X hIH hX
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcommP : ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ≤ I.pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hIP)
  have hcommX : ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ≤ X :=
    (commutator_mono le_rfl hRX).trans
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 I).trans (hIH.trans hHX)))
  have hcomm := two_subgroup_le_core X _ hcommX
    ((isPGroup_pCoreIn 2 I).to_le hcommP) hodd
  rw [hP]
  exact sup_le (hcomm.trans (pCoreIn_mono_of_normalizes hXH hHX))
    (le_pCoreIn_of_normalizes hU (hUI.trans hIH) hHU)

/-- The core and rank conclusions with the corrected residual argument
applied to the literal source pair. -/
theorem pair_core_and_rank (I H X U V : Subgroup G) [IsElementaryAbelian 2 V]
    (hIH : I ≤ H) (hX : X = (pResidual 2 H).map H.subtype)
    (hUI : U ≤ I) (hU : IsPGroup 2 U) (hHU : H ≤ normalizer (U : Set G))
    (hodd : Odd (Nat.card (X ⧸ pCore 2 X)))
    (hP : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hVI : V ≤ I) (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2) :
    I.pCoreIn 2 ≤ H.pCoreIn 2 ∧ V ⊓ I.pCoreIn 2 = V ⊓ H.pCoreIn 2 ∧
      Module.finrank (ZMod 2) (Additive (V ⧸ (V ⊓ H.pCoreIn 2).subgroupOf V)) = 1 := by
  have hc := pair_core_le I H X U hIH hX hUI hU hHU hodd hP
  exact ⟨hc, pair_core_intersection I H V hIH hVI hc,
    pair_quotient_rank_one I H V hIH hVI hc hk⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
