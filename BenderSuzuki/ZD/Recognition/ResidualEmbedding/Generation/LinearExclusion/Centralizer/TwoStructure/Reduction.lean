module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces
public import Theory.GroupTheory.PCoreOddIndex
public import Theory.GroupTheory.PCoreSurjective

/-!
# Relative core intersections and the corrected quotient reduction

For the original distinguished A, point two-core V, pair group D and
centralizer J, normality of A inside M puts A in V. The existing
source 15.2(h) calculation puts V in C₀=C_M(A). Consequently D∩V lies
in J; its normality inside J puts it in the embedded O₂(J).

If C₀=VY for an odd subgroup Y of J, then V has odd index in C₀.
Every two-subgroup of C₀ lies in V, so O₂(J) lies in V and D∩V=O₂(J)
with the literal subtype embeddings. This proves the intersection clause
of 15.5 once its odd supplement has been constructed.

The shared growth predicate records the outstanding conclusion of 15.3.
It implies V=A when every involution of V lies in A. Factoring by this
actual A leaves trivial two-core in M/A. All normality here is relative
to M; no claim that O₂(M) itself is trivial is made.

Source: refs/KGroup/GLS4/Chapter2.tex, Lemmas 15.3–15.5, using 15.2(e,h).
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "D" => residualPairStabilizer M t
local notation "J" => centralizer (L : Set G)
local notation "C₀" => M ⊓ centralizer (A : Set G)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)
local notation "U" => Subgroup.map (Subgroup.subtype J) (pCore 2 J)

public theorem Context.distinguished_le_point_twoCore : A ≤ V := by
  let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  let : IsElementaryAbelian 2 ((A).subgroupOf M) :=
    IsElementaryAbelian.subgroupOf (show A ≤ M from distinguishedClosure_le)
  have h : (A).subgroupOf M ≤ pCore 2 M :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 _⟩
  have hmap := map_mono (f := M.subtype) h
  rwa [map_subgroupOf_eq_of_le (show A ≤ M from distinguishedClosure_le)] at hmap

public theorem Context.point_twoCore_le_distinguished_centralizer : V ≤ C₀ := by
  rintro x ⟨v, hv, rfl⟩
  refine ⟨v.property, ?_⟩
  intro a ha
  exact congrArg Subtype.val (mem_centralizer_iff.mp
    (linear_twoCore_le_distinguished_centralizer d.minimal.disconnected d.reduction hv)
    ⟨a, distinguishedClosure_le ha⟩ ha)

public theorem Context.pair_inf_point_twoCore_le_centralizer_twoCore : D ⊓ V ≤ U := by
  have hJM : J ≤ M :=
    (centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M).trans
      inf_le_left
  let i : J →* M := inclusion hJM
  have hW : (pCore 2 M).comap i ≤ pCore 2 J :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i (inclusion_injective hJM)⟩
  rintro x ⟨hxD, v, hv, rfl⟩
  have hvJ : (v : G) ∈ J := d.centralizer_pair_eq ▸
    (show (v : G) ∈ C₀ ⊓ D from ⟨Context.point_twoCore_le_distinguished_centralizer d ⟨v, hv, rfl⟩, hxD⟩)
  exact ⟨⟨v, hvJ⟩, hW hv, rfl⟩

private theorem odd_index_of_supplement {Y : Subgroup G}
    (hYJ : Y ≤ J) (hodd : Odd (Nat.card Y))
    (hprod : (C₀ : Set G) = (V : Set G) * (Y : Set G)) :
    ¬ 2 ∣ (pCore 2 M).relIndex ((C₀).subgroupOf M) := by
  have hYM : Y ≤ M := hYJ.trans
    ((centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M).trans
      inf_le_left)
  let C : Subgroup M := (C₀).subgroupOf M
  let E : Subgroup M := Y.subgroupOf M
  have he : pCore 2 M ⊔ E = C := by
    apply (map_injective M.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hYM,
      map_subgroupOf_eq_of_le (show C₀ ≤ M from inf_le_left)]
    apply SetLike.coe_injective
    refine Eq.trans ?_ hprod.symm
    apply coe_mul_of_right_le_normalizer_left
    have hn : M ≤ normalizer (V : Set G) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 M).le_normalizer_map M.subtype
    exact hYM.trans hn
  have hi : (pCore 2 M).relIndex C = (pCore 2 M).relIndex E := by
    rw [← he]
    exact relIndex_sup_left E (pCore 2 M)
  have heodd : Odd (Nat.card E) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv]
    exact hodd
  rw [hi]
  exact fun ht => (Nat.not_even_iff_odd.mpr heodd)
    (even_iff_two_dvd.mpr (ht.trans (relIndex_dvd_card _ _)))

public theorem Context.centralizer_twoCore_le_point_twoCore_of_odd_supplement {Y : Subgroup G}
    (hYJ : Y ≤ J) (hodd : Odd (Nat.card Y))
    (hprod : (C₀ : Set G) = (V : Set G) * (Y : Set G)) : U ≤ V := by
  have hJM : J ≤ M :=
    (centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M).trans
      inf_le_left
  have hUC : U ≤ C₀ := (map_subtype_le _).trans
    (le_inf hJM (centralizer_le d.distinguished_le))
  have hUV : (U).subgroupOf M ≤ pCore 2 M := IsPGroup.le_pCore_of_le_oddIndexOverCore
    (((pCore_isPGroup (p := 2) (G := J)).map (J).subtype).comap_subtype (K := M))
    (show pCore 2 M ≤ (C₀).subgroupOf M from fun v hv =>
      Context.point_twoCore_le_distinguished_centralizer d ⟨v, hv, rfl⟩)
    (odd_index_of_supplement d hYJ hodd hprod)
    (show (U).subgroupOf M ≤ (C₀).subgroupOf M from fun _ hx => hUC hx)
  have hmap := map_mono (f := M.subtype) hUV
  rwa [map_subgroupOf_eq_of_le (hUC.trans inf_le_left)] at hmap

public theorem Context.pair_core_eq_of_odd_supplement {Y : Subgroup G}
    (hYJ : Y ≤ J) (hodd : Odd (Nat.card Y))
    (hprod : (C₀ : Set G) = (V : Set G) * (Y : Set G)) : D ⊓ V = U := by
  apply le_antisymm (Context.pair_inf_point_twoCore_le_centralizer_twoCore d)
  exact le_inf ((map_subtype_le _).trans
    (centralizer_residualGenerated_le_pair d.minimal.disconnected d.z_mem d.z_mem_M))
    (Context.centralizer_twoCore_le_point_twoCore_of_odd_supplement d hYJ hodd hprod)

/-- The source 15.3 conclusion, in the involution-witness form used by 15.4.
Its construction from the model interface is still a separate obligation. -/
@[expose] public def CentralizerTwoCoreGrowth (_d : Context Z M z t n) : Prop :=
  A < V → ∃ v : M, v ∈ pCore 2 M ∧ PFAppendixIII.IsInvolution v ∧ (v : G) ∉ A

public theorem Context.point_twoCore_eq_distinguished_of_involutions (hgrowth : CentralizerTwoCoreGrowth d)
    (hinv : ∀ v : M, v ∈ pCore 2 M → PFAppendixIII.IsInvolution v → (v : G) ∈ A) :
    V = A := by
  by_contra hne
  obtain ⟨v, hv, hi, ha⟩ := hgrowth (lt_of_le_of_ne (Context.distinguished_le_point_twoCore d) (Ne.symm hne))
  exact ha (hinv v hv hi)

public theorem Context.distinguished_quotient_twoCore_eq_bot_of_point_core_eq (hcore : V = A) :
    letI : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    pCore 2 (M ⧸ (A).subgroupOf M) = ⊥ := by
  let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  have heq : pCore 2 M = (A).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show A ≤ M from distinguishedClosure_le)]
    exact hcore
  let q := QuotientGroup.mk' ((A).subgroupOf M)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', ← heq]
    exact pCore_isPGroup
  have he := q.comap_pCore_of_ker_isPGroup hq hk
  have hm := congrArg (map q) he
  rw [map_comap_eq_self_of_surjective hq, heq] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
end BenderSuzuki.ZD.LinearExclusion
