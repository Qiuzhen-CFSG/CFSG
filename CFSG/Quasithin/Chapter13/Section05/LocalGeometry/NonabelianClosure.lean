module

public import CFSG.Quasithin.Chapter13.Section05.LocalSteps
public import Theory.GroupTheory.OrderTwoImagePair

/-!
# The nonabelian-closure reduction in 13.5.13

F.9.2 and F.9.4 give V∩Q_H=V₃ and |V*|=2 when U_H is nonabelian.
Equal starred conjugates generate a two-group. Different starred conjugates
have intersection in V₃. Transitivity on V₃/V₁ then moves an intersection
larger than V₁ onto V₂, where the earlier plane-normalization assertion
makes the join a two-group. The F.9.5(6) centralizer bound follows from
the ambient normalizer control, using the A₅ equality when applicable.

This proves the deduction from F.9.1 and the indicated earlier geometry,
not those inputs. Genuine F.9.1 is the 13.5.7 obligation; plane control is
13.5.6(3)/13.5.11; the transport is the natural action from 13.2/13.3.
The source assembly must discharge them. Left conjugates are used in the
universal pair assertion, equivalently inverting the book's conjugator.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.12–13, printed pp.918–919; F.9.5(5–6), printed p.319.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.LocalGeometry
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G}

/-- Nonabelian U_H and the index-two seed force V ∩ O₂(H) = V₊. -/
theorem seed_eq_intersection_core (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH) : D.V ⊓ D.QH = D.Vplus := by
  have hvnot : ¬ D.V ≤ D.QH := fun hv => hU (h.UH_elementary_of_V_le_QH hv).toIsMulCommutative
  have hseed : D.Vplus ≤ D.V ⊓ D.QH :=
    le_inf h.plus_le ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hm := relIndex_mul_relIndex D.Vplus (D.V ⊓ D.QH) D.V hseed inf_le_left
  rw [hindex] at hm
  have hd : D.Vplus.relIndex (D.V ⊓ D.QH) ∣ 2 := ⟨_, hm.symm⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with hone | htwo
  · exact le_antisymm (relIndex_eq_one.mp hone) hseed
  · rw [htwo] at hm
    have hi : (D.V ⊓ D.QH).relIndex D.V = 1 := by omega
    exact (hvnot ((relIndex_eq_one.mp hi).trans inf_le_right)).elim

omit [Finite G] in
private theorem starImage_card_eq_relIndex (H A : Subgroup G) (ha : A ≤ H) :
    Nat.card (Section08.Source.starImage H A) = (H.pCoreIn 2).relIndex A := by
  rw [Section08.Source.starImage, ← relIndex_ker, QuotientGroup.ker_mk']
  have hm := relIndex_map_map_of_injective (pCore 2 H) (A.subgroupOf H) H.subtype_injective
  rw [map_subgroupOf_eq_of_le ha] at hm
  exact hm.symm

/-- The literal image of V in H/O₂(H) has order two. -/
theorem star_V_card_two (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH) :
    Nat.card (Section08.Source.starImage D.H D.V) = 2 := by
  rw [starImage_card_eq_relIndex _ _ h.V_le_H]
  change D.QH.relIndex D.V = 2
  rw [← inf_relIndex_left D.V D.QH,
    seed_eq_intersection_core h hindex hU, hindex]

omit [Finite G] in
private theorem conjugate_le_of_mem (H A : Subgroup G) (ha : A ≤ H) {g : G} (hg : g ∈ H) :
    A.map (MulAut.conj g).toMonoidHom ≤ H := by
  have he : H.map (MulAut.conj g).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg)
  exact (map_mono ha).trans_eq he

omit [Finite G] in
private theorem starImage_conjugate_card (H A : Subgroup G) (ha : A ≤ H) {g : G} (hg : g ∈ H) :
    Nat.card (Section08.Source.starImage H (A.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (Section08.Source.starImage H A) := by
  rw [starImage_card_eq_relIndex _ _ (conjugate_le_of_mem H A ha hg), starImage_card_eq_relIndex _ _ ha]
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have he := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  conv_lhs => rw [← he]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

omit [Finite G] in
private theorem pair_star_alternative (H A B : Subgroup G) (ha : A ≤ H) (hb : B ≤ H)
    (hcA : Nat.card (Section08.Source.starImage H A) = 2)
    (hcB : Nat.card (Section08.Source.starImage H B) = 2) :
    IsPGroup 2 (A ⊔ B : Subgroup G) ∨ A ⊓ B ≤ H.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  by_cases he : Section08.Source.starImage H A = Section08.Source.starImage H B
  · left
    have hk : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have hp := isTwoGroup_sup_of_equal_order_two_images q (A.subgroupOf H) (B.subgroupOf H) hk hcA he
    have hm := hp.map H.subtype
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le ha, map_subgroupOf_eq_of_le hb] at hm
  · right
    have hi := inf_le_ker_of_distinct_order_two_images q (A.subgroupOf H) (B.subgroupOf H) hcA hcB he
    intro x hx
    have hk : (⟨x, ha hx.1⟩ : H) ∈ q.ker := hi ⟨hx.1, hx.2⟩
    have hxq : (⟨x, ha hx.1⟩ : H) ∈ pCore 2 H := by
      rwa [QuotientGroup.ker_mk'] at hk
    exact mem_map_of_mem H.subtype hxq

/-- Either the conjugate pair generates a two-group, or its intersection lies in V₊. -/
theorem conjugate_pair_reduction (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH) {g : G} (hg : g ∈ D.H) :
    IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) ∨
      D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≤ D.Vplus := by
  have hc := star_V_card_two h hindex hU
  have hcg : Nat.card (Section08.Source.starImage D.H
      (D.V.map (MulAut.conj g).toMonoidHom)) = 2 :=
    (starImage_conjugate_card D.H D.V h.V_le_H hg).trans hc
  rcases pair_star_alternative D.H D.V _ h.V_le_H
      (conjugate_le_of_mem D.H D.V h.V_le_H hg) hc hcg with hp | hi
  · exact Or.inl hp
  · right
    rw [← seed_eq_intersection_core h hindex hU]
    exact le_inf inf_le_left hi

/-- The deduction of 13.5.13(1) from plane transport and normalization.
The latter input is supplied by 13.5.6(3) or 13.5.11; it remains an assembly
obligation. All quotient and two-group arguments are discharged here. -/
theorem twoGroup_join_of_plane_control (h : D.Hypothesis)
    (V₂ : Subgroup G) (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      D.V.map (MulAut.conj k).toMonoidHom ≤ normalizer (D.V : Set G))
    {g : G} (hg : g ∈ D.H)
    (hinter : D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  rcases conjugate_pair_reduction h hindex hU hg with hp | hi
  · exact hp
  obtain ⟨l, hl, hW⟩ := hmove _ hinter hi
  have hn : D.L₁ ≤ normalizer (D.V : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans (le_sup_left.trans
      ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal)))
  let f := (MulAut.conj l).toMonoidHom
  have hV : D.V.map f = D.V := mem_normalizer_iff_map_conj_eq.mp (hn hl)
  have hconj : (D.V.map (MulAut.conj g).toMonoidHom).map f =
      D.V.map (MulAut.conj (l * g)).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, mul_assoc]
  have hW' : V₂ ≤ D.V ⊓ D.V.map (MulAut.conj (l * g)).toMonoidHom := by
    rwa [map_inf _ _ _ (MulAut.conj l).injective, hV, hconj] at hW
  have hlg : l * g ∈ D.H := D.H.mul_mem (h.local_le (mem_sup_left hl)) hg
  let := h.elementary
  have hpV := IsElementaryAbelian.isPGroup 2 D.V
  have hp := hpV.to_sup_of_normal_left'
    (hpV.map (MulAut.conj (l * g)).toMonoidHom) (hplane (l * g) hlg hW')
  have hmap : (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom).map f =
      D.V ⊔ D.V.map (MulAut.conj (l * g)).toMonoidHom := by
    rw [Subgroup.map_sup, hV, hconj]
  rw [← hmap] at hp
  exact hp.of_equiv ((D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom).equivMapOfInjective
    f (MulAut.conj l).injective).symm

/-- Transfer the source ambient centralizer bound to the actual H-centralizer,
as required in F.9.5(6). -/
theorem seed_centralizer_commutator_bound (h : D.Hypothesis) (M : Subgroup G)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁) :
    ⁅D.V, D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁ := by
  apply le_trans (commutator_mono le_rfl ?_) hc
  intro x hx
  refine ⟨hbound ⟨?_, Subgroup.centralizer_le_normalizer _ hx.2⟩, hx.2⟩
  exact Subgroup.centralizer_le_normalizer _ (h.H_centralizes hx.1)

/-- The A₅ centralizer equality supplies the F.9.5(6) commutator bound. -/
theorem a5_seed_centralizer_commutator_bound (h : D.Hypothesis) (M : Subgroup G)
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : M ⊓ centralizer (D.Vplus : Set G) = M ⊓ centralizer (D.V : Set G)) :
    ⁅D.V, D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁ := by
  apply seed_centralizer_commutator_bound h M hbound
  rw [hc, commutator_comm]
  have he : ⁅M ⊓ centralizer (D.V : Set G), D.V⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  rw [he]
  exact bot_le

/-- The exact additional hypotheses of F.9.5(5–6), on the literal starred
image and with right conjugates as in the source. The plane alternatives
are the assertions to be supplied by 13.5.6(3) and 13.5.11. -/
theorem f95_applicability_of_plane_control (h : D.Hypothesis)
    (V₂ M : Subgroup G) (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁) :
    Section08.Source.starImage D.H D.V ≠ ⊥ ∧
      (∀ g ∈ D.H, D.V₁ < D.V ⊓ ChapterG.Section02.Setup.conjugate D.V g →
        IsPGroup 2 (D.V ⊔ ChapterG.Section02.Setup.conjugate D.V g : Subgroup G)) ∧
      ⁅D.V, D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁ := by
  refine ⟨?_, ?_, seed_centralizer_commutator_bound h M hbound hc⟩
  · intro he
    have hh := star_V_card_two h hindex hU
    rw [he] at hh
    simp at hh
  · intro g hg hi
    apply twoGroup_join_of_plane_control h V₂ hindex hU hmove ?_ (D.H.inv_mem hg) hi
    intro k hk hVk
    rcases hplane k hk hVk with hcomm | hn
    · rw [commutator_comm] at hcomm
      exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact hn.trans inf_le_right

end CFSG.Quasithin.Chapter13.Section05.LocalGeometry

end
