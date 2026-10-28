module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.CentralizerGeometry
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# Sharp maxima in the selected S₃ preimage

Let E be a maximum elementary abelian subgroup of G_v whose star image is
sharp and meets a normal marked S₃ subgroup H nontrivially. Put U = U_v,
N = H.comap starMk and C = C_U(N). We prove that (E ∩ N) C is itself a
global maximum, and hence supplies a moving maximum in the full preimage N.

Maximality gives C_U(E) = E ∩ U, so sharpness says
|U| = |E ∩ U| |E*|. The faithful S₃ action splits U into its moved plane W
and C, giving |U| = 4 |C|. Since H is normal, E acts on W. Orbit counting
produces a nonidentity vector in C_W(E), which maximality places in E.
The direct sum makes this vector lie outside C. Thus
|E ∩ U| ≥ 2 |E ∩ C|, while |E*| ≥ 2 [E* : E* ∩ H]. These two bounds give
[E : E ∩ N] ≤ [C : E ∩ C], exactly the replacement order comparison.

This is the conditional sharp-offender transfer used to obtain H* = J(H)*
in the singleton branch of 13.6.13. It retains the original conjugation
representation, star quotient and full preimage. The parent construction
supplies the sharp global maximum, normal S₃ marking and support order;
no additional lifting, kernel-rank or Thompson premise is imposed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
printed pp.75–76, and the construction in 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]

private noncomputable def sharpFixedEquiv (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (A : Subgroup (Gv v)) :
    fixedSpace (starRepresentation z v) (A.map (starMk z v)) ≃
      (internalUv z v ⊓ centralizer (A : Set (Gv v)) : Subgroup (Gv v)) where
  toFun w := ⟨⟨w.val.toMul, Uv_le_Gv z v hz w.val.toMul.property⟩,
    w.val.toMul.property, by
      intro a ha
      have hh := w.property ⟨starMk z v a, mem_map_of_mem _ ha⟩
      have he := congrArg (fun t : Additive (Uv z v) => (t.toMul : G)) hh
      change ((starRepresentation z v (starMk z v a) w.val).toMul : G) = _ at he
      rw [starRepresentation_mk_apply] at he
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he)⟩
  invFun w := ⟨Additive.ofMul ⟨w.val, w.property.1⟩, by
    intro a
    obtain ⟨b, hb, he⟩ := a.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((starRepresentation z v (a : Gstar z v)
      (Additive.ofMul ⟨w.val, w.property.1⟩)).toMul : G) = _
    rw [← he, starRepresentation_mk_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val (w.property.2 b hb))⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Finite G] in
private theorem sharpFixed_card (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (H : Subgroup (Gstar z v)) :
    Nat.card (singletonFixed z v H) =
      Nat.card (fixedSpace (starRepresentation z v) H) := by
  have he := Nat.card_congr (sharpFixedEquiv z v hz (H.comap (starMk z v)))
  rw [map_comap_eq_self_of_surjective (starMk_surjective z v)] at he
  exact he.symm

omit [Finite G] in
private theorem sharp_internal_card (z v : G) (hz : z ∈ Gv v) :
    Nat.card (internalUv z v) = Nat.card (Additive (Uv z v)) :=
  Nat.card_congr (subgroupOfEquivOfLe (Uv_le_Gv z v hz)).toEquiv

private theorem sharp_split_card (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4) :
    Nat.card (internalUv z v) = 4 * Nat.card (singletonFixed z v H) := by
  have he := Nat.card_congr (Submodule.prodEquivOfIsCompl _ _
    (singleton_moved_fixed_isCompl z v H e hcard)).toEquiv
  rw [Nat.card_prod, ← ambientSpace_card, moved_ambientSpace, hcard] at he
  rw [sharp_internal_card z v hz, sharpFixed_card z v hz H]
  exact he.symm

private theorem sharp_maximum_card (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ≠ ⊥)
    (hsharp : fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
      rank (E.map (starMk z v))) :
    Nat.card (internalUv z v) =
      Nat.card (E ⊓ internalUv z v : Subgroup (Gv v)) * Nat.card (E.map (starMk z v)) := by
  let : IsElementaryAbelian 2 E := hE.2.1
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  let F := internalUv z v ⊓ centralizer (E : Set (Gv v))
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  have hFE : F ≤ E := maxElementary_contains_elementary_centralizer ⊤ E F hE
    le_top inf_le_right
  have hF : F = E ⊓ internalUv z v := by
    apply le_antisymm (le_inf hFE inf_le_left)
    exact le_inf inf_le_right (inf_le_left.trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  have hc := Nat.card_congr (sharpFixedEquiv z v hz E)
  change Nat.card (fixedSpace (starRepresentation z v) (E.map (starMk z v))) = Nat.card F at hc
  rw [hF] at hc
  have hd := fixedCodim_add_finrank (starRepresentation z v) (E.map (starMk z v))
  rw [hsharp] at hd
  rw [sharp_internal_card z v hz, ← hc,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Uv z v)),
    Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace (starRepresentation z v) (E.map (starMk z v))), Nat.card_zmod,
    (show IsElementaryTwo (E.map (starMk z v)) from
      ⟨hne, IsElementaryAbelian.map _⟩).card_eq_two_pow_rank,
    ← pow_add, add_comm, hd]

omit [Finite G] in
private theorem sharp_plane_map (z v : G) (hz : z ∈ Gv v)
    (H : Subgroup (Gstar z v)) :
    (⁅internalUv z v, H.comap (starMk z v)⁆).map (Gv v).subtype = movedSubgroup z v H := by
  rw [map_commutator, show (internalUv z v).map (Gv v).subtype = Uv z v from
    map_subgroupOf_eq_of_le (Uv_le_Gv z v hz)]
  rfl

private theorem sharp_plane_disjoint (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4) :
    Disjoint ⁅internalUv z v, H.comap (starMk z v)⁆ (singletonFixed z v H) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  let w := (sharpFixedEquiv z v hz (H.comap (starMk z v))).symm ⟨x, hx.2⟩
  have hw : w.val ∈ fixedSpace (starRepresentation z v) H := by
    have hh := w.property
    simpa only [map_comap_eq_self_of_surjective (starMk_surjective z v)] using hh
  have hm : w.val ∈ subspaceCommutator (starRepresentation z v) ⊤ H := by
    apply (mem_ambientSpace z v _ w.val.toMul).mp
    rw [moved_ambientSpace, ← sharp_plane_map z v hz H]
    exact mem_map_of_mem _ hx.1
  have hzero : w.val = 0 :=
    Submodule.disjoint_def.mp (singleton_moved_fixed_isCompl z v H e hcard).disjoint _ hm hw
  exact Subtype.ext (congrArg (fun t : Additive (Uv z v) => (t.toMul : G)) hzero)

private theorem sharp_maximum_outside_fixed (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4)
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v))) :
    ¬ E ⊓ internalUv z v ≤ singletonFixed z v H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 E := hE.2.1
  let : IsElementaryAbelian 2 (internalUv z v) :=
    IsElementaryAbelian.subgroupOf (Uv_le_Gv z v hz)
  let W := ⁅internalUv z v, H.comap (starMk z v)⁆
  let F := W ⊓ centralizer (E : Set (Gv v))
  have hWU : W ≤ internalUv z v := commutator_le_left _ _
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (inf_le_left.trans hWU)
  have hW : Nat.card W = 4 := by
    rw [← card_map_of_injective (K := W) (Gv v).subtype_injective,
      sharp_plane_map z v hz H, hcard]
  have hc := card_modEq_card_inf_centralizer E W (IsElementaryAbelian.isPGroup 2 E)
    (show E ≤ normalizer (W : Set (Gv v)) by rw [normalizer_eq_top]; exact le_top)
  have hF : F ≠ ⊥ := by
    intro hf
    change Nat.card W % 2 = Nat.card F % 2 at hc
    rw [hW, hf, card_bot] at hc
    norm_num at hc
  obtain ⟨x, hx1⟩ := ne_bot_iff_exists_ne_one.mp hF
  have hx := x.property
  have hxE : x.val ∈ E :=
    maxElementary_contains_elementary_centralizer ⊤ E F hE le_top inf_le_right hx
  intro hEC
  have hxC := hEC ⟨hxE, hWU hx.1⟩
  have hb := (sharp_plane_disjoint z v hz H e hcard).eq_bot
  apply hx1
  exact Subtype.ext (mem_bot.mp
    (hb ▸ (show x.val ∈ W ⊓ singletonFixed z v H from ⟨hx.1, hxC⟩)))

omit [Finite G] in
private theorem sharp_card_inf_index (A B : Subgroup G) :
    Nat.card (A ⊓ B : Subgroup G) * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left, inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ B) B bot_le inf_le_right

private theorem sharp_index_bound {D : Type*} [Group D] [Finite D]
    (U C E : Subgroup G) (f : G →* D) (H : Subgroup D)
    (hCU : C ≤ U)
    (hU : Nat.card U = 4 * Nat.card C)
    (hsharp : Nat.card U = Nat.card (E ⊓ U : Subgroup G) * Nat.card (E.map f))
    (hproper : ¬ E ⊓ U ≤ C) (hne : E.map f ⊓ H ≠ ⊥) :
    (H.comap f).relIndex E ≤ E.relIndex C := by
  let P := E ⊓ U
  let Q := E ⊓ C
  have hQP : Q ≤ P := inf_le_inf_left E hCU
  have hPQ : ¬ P ≤ Q := fun h => hproper (h.trans inf_le_right)
  have hcP : Nat.card Q * Q.relIndex P = Nat.card P := by
    simpa only [inf_eq_left.mpr hQP] using sharp_card_inf_index Q P
  have hp : 0 < Q.relIndex P := by
    have hh : 0 < Nat.card P := Nat.card_pos
    nlinarith
  have hi : Q.relIndex P ≠ 1 := mt relIndex_eq_one.mp hPQ
  have hP : 2 * Nat.card Q ≤ Nat.card P := by
    have hh : 2 ≤ Q.relIndex P := by omega
    calc
      _ = Nat.card Q * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card Q * Q.relIndex P := Nat.mul_le_mul_left _ hh
      _ = _ := hcP
  have hcA := sharp_card_inf_index H (E.map f)
  have hA : 2 * H.relIndex (E.map f) ≤ Nat.card (E.map f) := by
    have hh : 2 ≤ Nat.card (H ⊓ E.map f : Subgroup D) := by
      have hn := (one_lt_card_iff_ne_bot (E.map f ⊓ H)).mpr hne
      rwa [inf_comm] at hn
    exact (Nat.mul_le_mul_right _ hh).trans_eq hcA
  have hcC : Nat.card Q * E.relIndex C = Nat.card C := sharp_card_inf_index E C
  have hb : 4 * (Nat.card Q * H.relIndex (E.map f)) ≤ 4 * Nat.card C := calc
    _ = (2 * Nat.card Q) * (2 * H.relIndex (E.map f)) := by ring
    _ ≤ Nat.card P * Nat.card (E.map f) := Nat.mul_le_mul hP hA
    _ = Nat.card U := hsharp.symm
    _ = _ := hU
  have hb' := Nat.le_of_mul_le_mul_left hb (by decide : 0 < 4)
  rw [← hcC] at hb'
  rw [relIndex_comap]
  exact Nat.le_of_mul_le_mul_left hb' Nat.card_pos

/-- A sharp global maximum retains maximum order after restriction to the
selected S₃ preimage and replacement by its fixed part. -/
theorem singleton_replacement_mem_global_maximum_of_sharp
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4)
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hsharp : fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
      rank (E.map (starMk z v))) :
    (E ⊓ H.comap (starMk z v)) ⊔ singletonFixed z v H ∈
      elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)) := by
  apply singleton_replacement_mem_global_maximum z v hz H E hE
  apply sharp_index_bound (internalUv z v) (singletonFixed z v H) E (starMk z v) H
    inf_le_left (sharp_split_card z v hz H e hcard)
  · apply sharp_maximum_card z v hz E hE _ hsharp
    intro hzero
    exact hne (by rw [hzero, bot_inf_eq])
  · exact sharp_maximum_outside_fixed z v hz H e hcard E hE
  · exact hne

/-- The literal star-preimage witness required in the mixed singleton case.
Sharpness, the normal S₃ marking and its moved plane discharge all replacement
order premises. No lifting or kernel-structure hypothesis is required. -/
theorem star_maximum_of_singleton_sharp
    (z v : G) (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4)
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥)
    (hsharp : fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
      rank (E.map (starMk z v))) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      B.map (starMk z v) ≠ ⊥ := by
  let N := H.comap (starMk z v)
  let C := singletonFixed z v H
  let B := (E ⊓ N) ⊔ C
  have hB : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)) :=
    singleton_replacement_mem_global_maximum_of_sharp z v hz H e hcard E hE hne hsharp
  have hCN : C ≤ N := by
    intro x hx
    change starMk z v x ∈ H
    rw [show starMk z v x = 1 from singletonFixed_le_ker z v hz H hx]
    exact H.one_mem
  refine ⟨B, ⟨sup_le inf_le_right hCN, hB.2.1,
    fun A _ hA => hB.2.2 A le_top hA⟩, ?_⟩
  have hmap : E.map (starMk z v) ⊓ H ≤ B.map (starMk z v) := by
    rintro x ⟨⟨a, ha, rfl⟩, hx⟩
    exact mem_map_of_mem _ ((show E ⊓ N ≤ B from le_sup_left) ⟨ha, hx⟩)
  intro hb
  exact hne (le_bot_iff.mp (hmap.trans hb.le))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products

end
