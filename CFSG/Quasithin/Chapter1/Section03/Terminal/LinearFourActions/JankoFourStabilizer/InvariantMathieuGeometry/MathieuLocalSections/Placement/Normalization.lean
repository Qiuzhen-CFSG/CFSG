module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement.Reduction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Relative normalization of the local L₄(2) component in M₂₄

Work inside H = B ∨ S, where the source-local hypothesis says that B is a
C-component. Distinct conjugates of B normalize one another. Their intersection
is a proper normal subgroup of B and hence solvable. Its image in the actual
simple quotient B/O₂(B) is trivial, so the intersection has two-power order.
The product-order formula would then make 25 divide |H| and therefore |M₂₄|,
contrary to the native Mathieu group order. Thus B is normal in H.

Simplicity is transported from the supplied PSL₄ model using the proved
higher-rank projective-linear simplicity theorem. No identification by order
and no ambient normality of B in M₂₄ are used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.3(1),(6) and the M₂₄ case of A.3.12(14), printed pp.42–43 and 47–48;
GLS, volume 3, Table 5.3e. This supplies the normalization step in the
common-octad placement argument; the permutation-action step is separate.
-/

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections

open Subgroup
open CFSG.Quasithin.Chapter1

/-- Simplicity follows from the actual projective matrix-group model. -/
private theorem section_simple {G : Type*} [Group G]
    (h : ClassicalGroup.IsPSL G 4 2) : IsSimpleGroup G := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
  let := Atlas.psl_simple_high_rank (F := F) 4 (by decide)
  exact e.isSimpleGroup

/-- A solvable normal subgroup dies in the nontrivial perfect simple quotient. -/
private theorem solvable_normal_le_twoCore {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : B.IsCComponent)
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (I : Subgroup B) [I.Normal] [Group.IsSolvable I] : I ≤ pCore 2 B := by
  let q := QuotientGroup.mk' (pCore 2 B)
  let := hB.perfect
  have hn : (I.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hs : Group.IsSolvable (I.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective I)
  have he : I.map q = ⊥ := by
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have : Group.IsSolvable (B ⧸ pCore 2 B) := by
        rw [ht] at hs
        exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (B ⧸ pCore 2 B)).subtype)
          (MonoidHom.range_eq_top.mp (range_subtype ⊤))
      exact (Group.IsPerfect.not_isSolvable (B ⧸ pCore 2 B) this).elim
  simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using he

/-- Two distinct conjugates would require two factors of five in the ambient order. -/
private theorem component_normal_of_five_square_not_dvd {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : B.IsCComponent)
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hfive : 5 ∣ Nat.card B) (horder : ¬ 25 ∣ Nat.card G) : B.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  let C := B.map (MulAut.conj g).toMonoidHom
  have hC : C.IsCComponent := hB.map_equiv (MulAut.conj g)
  by_contra hne
  have hCB : C ≤ normalizer (B : Set G) :=
    (le_cComponentLayer hC).trans (cComponentLayer_le_normalizer hB)
  have hBC : B ≤ normalizer (C : Set G) :=
    (le_cComponentLayer hB).trans (cComponentLayer_le_normalizer hC)
  let I := C.subgroupOf B
  let : I.Normal := normal_subgroupOf_of_le_normalizer hBC
  have hIt : I ≠ ⊤ := fun ht => hne (hB.eq_of_le hC (subgroupOf_eq_top.mp ht)).symm
  let : Group.IsSolvable I := hB.isSolvable_of_subnormal_lt_top
    (inferInstance : I.Normal).isSubnormal hIt
  have hIcore : I ≤ pCore 2 B := solvable_normal_le_twoCore B hB I
  have hIp : IsPGroup 2 I :=
    (pCore_isPGroup (p := 2) (G := B)).of_injective
      (inclusion hIcore) (inclusion_injective hIcore)
  obtain ⟨n, hn⟩ := hIp.exists_card_eq
  have hicard : Nat.card (B ⊓ C : Subgroup G) = 2 ^ n := by
    rw [← hn, ← card_map_of_injective (K := I) B.subtype_injective]
    simp only [I, subgroupOf_map_subtype, inf_comm]
  have hc : Nat.card C = Nat.card B := card_map_of_injective (MulAut.conj g).injective
  have hd : 25 ∣ Nat.card (B ⊓ C : Subgroup G) * Nat.card (B ⊔ C : Subgroup G) := by
    rw [← card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hCB, hc]
    exact Nat.mul_dvd_mul hfive hfive
  rw [hicard] at hd
  have hcop : Nat.Coprime 25 (2 ^ n) := (by decide : Nat.Coprime 25 2).pow_right n
  exact horder ((hcop.dvd_of_dvd_mul_left hd).trans (card_subgroup_dvd_card (B ⊔ C)))

/-- The ambient Sylow two-subgroup normalizes the source-local L₄(2) component.
Normality is established inside B ∨ S. -/
public theorem localNormalization : LocalNormalization := by
  intro B S hB hlocal
  let H := B ⊔ S.toSubgroup
  let C := B.subgroupOf H
  have hC : C.IsCComponent := hlocal
  let e : C ≃* B := subgroupOfEquivOfLe le_sup_left
  let eQ := QuotientGroup.congr (pCore 2 C) (pCore 2 B) e (pCore_map_iso 2 e)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := section_simple hB
  let : IsSimpleGroup (C ⧸ pCore 2 C) := eQ.isSimpleGroup
  have hfive : 5 ∣ Nat.card C := by
    rw [Nat.card_congr e.toEquiv]
    exact (by decide : 5 ∣ 20160).trans (section_order_dvd B hB)
  have horder : ¬ 25 ∣ Nat.card H := by
    intro h
    have hd := h.trans (card_subgroup_dvd_card H)
    rw [Sporadic.Mathieu.m24_order] at hd
    norm_num at hd
  have hn : C.Normal := component_normal_of_five_square_not_dvd C hC hfive horder
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections
