module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Reduction
public import Theory.Mathieu.M24.LocalGeometry.OctadOrder
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Reduction of the local L₄(2) sections in M₂₄ to octad geometry

Suppose B/O₂(B) is L₄(2) and B is a C-component of the subgroup generated
with an ambient Sylow two-subgroup S. If B and S preserve one octad, their
join has order divisible by lcm(20160,1024) = 322560, so it fills the octad
stabilizer. Its index over B divides sixteen. Perfectness of the octad
stabilizer then excludes a proper subnormal B: any proper normal overgroup
of B would give a nontrivial perfect two-group quotient.

Once B equals this stabilizer, elementary abelianness of its two-core and
the supplied quotient order give an actual E16 kernel. A basis over F₂
constructs the model equivalence; the normal kernel is the intrinsic
O₂(B), and the quotient identification is the original hypothesis.

The common-octad placement and the perfect/elementary-core structure are
separate unproved contracts below. The final source assembly must discharge
both. Cardinality alone does not prove the placement or elementary structure.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.12(14)
and its proof through sporadic Sylow overgroups, printed pp.47–48;
GLS, volume 3, Table 5.3e. Octad cardinalities are proved on the native
Witt-design carrier in `Theory.Mathieu.M24.LocalGeometry.OctadOrder`.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections

open Subgroup
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open Sporadic.Mathieu
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1

open Sporadic.Mathieu.M24LocalGeometry

/-- The required Sylow-overgroup placement retains the actual common octad.
It assumes neither the extension nor the elementary kernel. -/
@[expose] def OctadPlacement : Prop :=
  ∀ (B : Subgroup M24) (S : Sylow 2 M24),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    B ∈ ChapterA.Section03.localCComponents S →
    ∃ O : Octad, B ⊔ S.toSubgroup ≤ octadStabilizer O

/-- Exactly the remaining intrinsic octad facts consumed by the assembly.
The kernel order and quotient model will come from the source section. -/
@[expose] def OctadCoreStructure : Prop :=
  ∀ O : Octad, Group.IsPerfect (octadStabilizer O) ∧
    IsElementaryAbelian 2 (pCore 2 (octadStabilizer O))


private theorem elementary_model {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 16) : ElementaryModel 2 4 E := by
  have hc : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
  have hr : Module.finrank (ZMod 2) (Additive E) = 4 := by
    apply Nat.pow_right_injective (a := 2) (by decide)
    simpa only [hcard] using hc.symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hr
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

private theorem sylow_card (S : Sylow 2 M24) : Nat.card (S : Subgroup M24) = 1024 := by
  rw [Sylow.card_eq_multiplicity, m24_order]
  have hf : (244823040 : ℕ).factorization 2 = 10 := by
    apply Nat.le_antisymm
    · by_contra hn
      have hd : 2 ^ 11 ∣ 244823040 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (by decide)).mpr (by omega)
      norm_num at hd
    · exact (Nat.prime_two.pow_dvd_iff_le_factorization (by decide)).mp (by norm_num)
  rw [hf]
  rfl

private theorem subnormal_eq_top {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (C : Subgroup H) (hs : C.IsSubnormal) (hi : C.index ∣ 16) : C = ⊤ := by
  by_contra hne
  obtain ⟨N, hN, hCN, hNt⟩ := hs.exists_normal_and_le_and_lt_top_of_ne hne
  let := hN
  have hd : Nat.card (H ⧸ N) ∣ 2 ^ 4 := (index_dvd_of_le hCN).trans hi
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hp : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card hn
  have : Subsingleton (H ⧸ N) := by
    by_contra! h
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply hNt.ne
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)


private theorem section_card {G : Type*} [Group G] (h : ClassicalGroup.IsPSL G 4 2) :
    Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

/-- The specified section forces divisibility by the order of L₄(2). -/
theorem section_order_dvd (B : Subgroup M24)
    (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2) : 20160 ∣ Nat.card B := by
  rw [← section_card hB]
  exact card_quotient_dvd_card (pCore 2 B)

/-- Inside a perfect overgroup of the octad-stabilizer order, local membership
forces equality. Subnormality is used inside the generated overgroup. -/
theorem eq_of_local_of_join_le (B H : Subgroup M24) (S : Sylow 2 M24)
    (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2)
    (hlocal : B ∈ CFSG.Quasithin.ChapterA.Section03.localCComponents S)
    (hle : B ⊔ S.toSubgroup ≤ H) (hcard : Nat.card H = 322560)
    (hperfect : Group.IsPerfect H) : B = H := by
  have hjoin : B ⊔ S.toSubgroup = H := by
    apply eq_of_le_of_card_ge hle
    rw [hcard]
    have h₁ : 20160 ∣ Nat.card ↥(B ⊔ S.toSubgroup) :=
      (section_order_dvd B hB).trans (card_dvd_of_le le_sup_left)
    have h₂ : 1024 ∣ Nat.card ↥(B ⊔ S.toSubgroup) := by
      rw [← sylow_card S]
      exact card_dvd_of_le le_sup_right
    have hd : 322560 ∣ Nat.card ↥(B ⊔ S.toSubgroup) := by
      simpa only [show Nat.lcm 20160 1024 = 322560 by decide] using Nat.lcm_dvd h₁ h₂
    exact Nat.le_of_dvd Nat.card_pos hd
  have hBH : B ≤ H := le_sup_left.trans hle
  have hcomp : (B.subgroupOf H).IsCComponent := by
    rw [← hjoin]
    exact hlocal
  let := hperfect
  have hi : (B.subgroupOf H).index ∣ 16 := by
    apply (Nat.mul_dvd_mul_iff_left (a := 20160) (by decide)).mp
    have hd := Nat.mul_dvd_mul_right (section_order_dvd B hB) (B.subgroupOf H).index
    have hc : Nat.card (B.subgroupOf H) = Nat.card B :=
      Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv
    rw [← hc, card_mul_index, hcard] at hd
    exact hd
  have he := subnormal_eq_top (B.subgroupOf H) hcomp.subnormal hi
  exact le_antisymm hBH (subgroupOf_eq_top.mp he)

/-- Construct the normal elementary kernel and retain the supplied actual quotient.
The vector-space cardinality formula supplies the model equivalence. -/
theorem extension_of_card_and_elementary_core (B : Subgroup M24) (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2)
    (hcard : Nat.card B = 322560) (hel : IsElementaryAbelian 2 (pCore 2 B)) :
    HasExtension B (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2) := by
  have hc : Nat.card (pCore 2 B) = 16 := by
    have h := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
    rw [hcard, section_card hB] at h
    omega
  let := hel
  exact ⟨pCore 2 B, inferInstance, elementary_model hc, hB⟩

/-- The two-core has order at most sixteen, so the subgroup has order at most 322560. -/
theorem source_order_bounds (B : Subgroup M24) (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2) :
    Nat.card (pCore 2 B) ≤ 16 ∧ Nat.card B ≤ 322560 := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  have hc : Nat.card B = 20160 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 B), section_card hB, hn]
  have hd : 20160 * 2 ^ n ∣ 244823040 := by
    rw [← hc, ← m24_order]
    exact card_subgroup_dvd_card B
  have hnle : n ≤ 4 := by
    by_contra h
    have hp : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have hh : 20160 * 2 ^ 5 ∣ 244823040 := (Nat.mul_dvd_mul_left 20160 hp).trans hd
    norm_num at hh
  have hp : 2 ^ n ≤ 16 := by
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hnle)
  constructor
  · rwa [hn]
  · rw [hc]
    omega

/-- A source-local L₄(2) section generates a proper overgroup with the Sylow subgroup. -/
theorem source_join_ne_top (B : Subgroup M24) (S : Sylow 2 M24)
    (hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2)
    (hlocal : B ∈ CFSG.Quasithin.ChapterA.Section03.localCComponents S) :
    B ⊔ S.toSubgroup ≠ ⊤ := by
  intro he
  have hcomp : (B.subgroupOf (⊤ : Subgroup M24)).IsCComponent := by
    change (B.subgroupOf (B ⊔ S.toSubgroup)).IsCComponent at hlocal
    rwa [he] at hlocal
  have hcomp' : B.IsCComponent :=
    (Subgroup.IsCComponent.subgroupOf_iff Subgroup.IsSubnormal.top le_top).mp hcomp
  rcases hcomp'.subnormal.eq_bot_or_top_of_isSimpleGroup m24_isSimpleGroup with hb | ht
  · exact hcomp'.ne_bot hb
  · have hc := (source_order_bounds B hB).2
    rw [ht, card_top, m24_order] at hc
    omega

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections
