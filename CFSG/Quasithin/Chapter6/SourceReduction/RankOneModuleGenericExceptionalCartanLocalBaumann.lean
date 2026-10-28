module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalTorus
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ImagesSource
public import Stellmacher.BaumannIntermediate

/-!
# Baumann normalization and the nonblock torus conclusion

The genuine earlier action theorem identifies the original Thompson and
Baumann images modulo C(W)=O₂(LT). Lift this equality through the two-core.
The natural-left Thompson bound places Baum(T) in (T ∩ L)O₂(LT), whose
Baumann subgroup is the original one by heredity. Thus the whole original
Borel normalizes Baum(T), without a block assumption.

This discharges the normalization premise of the characteristic-subgroup
and torus argument. Every noncentral local Cartan configuration therefore
has degree two or a chi-block on the literal right residual. The right
block exclusion and the degree-two case remain open; no unconditional
centralization or classification is asserted.

Source: Aschbacher–Smith E.2.3 and 5.1.13, printed pp.216–217,637–638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
private theorem Input.baumann_reduced_centralizer_core
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    centralizer (W.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let M := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf M
  let U := W.subgroupOf M
  have hr : IsPReduced 2 U := h.reduced_internal
  let := hr.normal
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer h.sylow_normalizes)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 L)
    (subgroupOfEquivOfLe (show L ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show L ≤ M from le_sup_left)))
  let := h.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : e b ∈ center (L ⧸ pCore 2 L) := MulEquivClass.apply_mem_center e hb
    rw [h.quotient_center_eq_bot] at hh
    exact e.injective (by simpa only [mem_bot,map_one] using hh)
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro hh
    apply h.noncentral
    have he := congrArg (map M.subtype) hh
    have hu : U.map M.subtype = W := map_subgroupOf_eq_of_le h.reduced.1
    have hb : B.map M.subtype = L := map_subgroupOf_eq_of_le le_sup_left
    simpa only [map_commutator,hu,hb,Subgroup.map_bot] using he
  apply reduced_quasisimple_centralizer_eq_pCore U B hr hz hm
  apply isPGroup_quotient_of_sup_eq_top B ((T : Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype
  rw [←subgroupOf_sup (show L ≤ M from le_sup_left) (show (T : Subgroup G) ≤ M from le_sup_right)]
  exact subgroupOf_self M


/-- The source image identity upgrades the natural Thompson bound to
normalization of the original Baumann subgroup by the full Borel. -/
theorem Input.borel_normalizes_baumann_of_thompson_bound
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hb : elementaryAbelianMaxJ (T : Subgroup G) ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    localBorel T L ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  let M := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let Q := ((T : Subgroup G) ⊓ L) ⊔ M.pCoreIn 2
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let C := centralizer (U : Set M)
  let q := QuotientGroup.mk' C
  have hk : q.ker = pCore 2 M := (QuotientGroup.ker_mk' C).trans h.baumann_reduced_centralizer_core
  have hSQ : IsSQTK KnownSimple.IsKnownSimple M := by
    have hMM : M ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hMM)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (M.subgroupOf (normalizer (L : Set G))))
  have hSm : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJm : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hSm]
  have hBm : (ChapterB.baumann (S : Subgroup M)).map M.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    unfold ChapterB.baumann ChapterB.thompsonAlpha
    rw [baumann_map_injective M.subtype M.subtype_injective,hSm]
  have hjS : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hc
    apply hj
    rw [←hJm]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg M.subtype (hc hx ⟨v,h.reduced.1 hv⟩ hv)
  have hi := ChapterE.ThompsonAction.source_thompson_baumann_image hSQ S
    h.local_minimal_parabolic U h.reduced_internal hjS
  have hBQ : ChapterB.baumann (T : Subgroup G) ≤ Q := by
    rw [←hBm]
    rintro _ ⟨x,hx,rfl⟩
    have hxq : q x ∈ (elementaryAbelianMaxJ (S : Subgroup M)).map q := by
      rw [hi]
      exact mem_map_of_mem q hx
    obtain ⟨y,hy,he⟩ := hxq
    have hdiff : y⁻¹*x ∈ pCore 2 M := by
      rw [←hk]
      change q (y⁻¹*x) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hyQ : (y : G) ∈ Q := hb (hJm ▸ mem_map_of_mem M.subtype hy)
    have hzQ : ((y⁻¹*x : M) : G) ∈ Q :=
      mem_sup_right (mem_map_of_mem M.subtype hdiff)
    have hh := Q.mul_mem hyQ hzQ
    change M.subtype (y * (y⁻¹*x)) ∈ Q at hh
    simpa only [mul_inv_cancel_left] using hh
  have hQT : Q ≤ (T : Subgroup G) := sup_le inf_le_left (by
    change (pCore 2 M).map M.subtype ≤ (T : Subgroup G)
    rw [←hSm]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S))
  have hBe : ChapterB.baumann Q = ChapterB.baumann (T : Subgroup G) :=
    baumann_eq_of_intermediate (T : Subgroup G) Q hBQ hQT
  have hQN : localBorel T L ≤ normalizer (Q : Set G) := by
    apply (le_inf inf_le_right ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hm : M ≤ normalizer (M.pCoreIn 2 : Set G) :=
      M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
    exact (inf_le_left.trans (show L ≤ M from le_sup_left)).trans hm
  exact hQN.trans (hBe ▸ normalizer_le_normalizer_baumann Q)

/-- The original Cartan normalizes the original Baumann subgroup in the
A₇ configuration, with no block assumption. -/
theorem LocalA7Configuration.cartan_normalizes_baumann
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  have hn := a.four_left_thompson_natural h hH hgen c d (a.four h hH hgen c d)
  exact c.left_le.trans (h.borel_normalizes_baumann_of_thompson_bound (a.left_thompson_moves h) hn.1)

/-- Without either block exclusion, the nonblock right branch already
forces the original degree two. -/
theorem LocalA7Configuration.degree_two_or_right_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    n = 2 ∨ ChapterC.IsChiBlockIn (pResidual 2 H) := by
  by_cases hb : ChapterC.IsChiBlockIn (pResidual 2 H)
  · exact Or.inr hb
  · exact Or.inl (a.degree_two_of_right_nonblock h hH hgen c d hb
      (a.cartan_normalizes_baumann h hH hgen c d))

/-- The completed FF producer and the actual characteristic/torus
argument leave only degree two or the literal right block. -/
theorem localCartan_noncentral_degree_two_or_right_block
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    n = 2 ∨ ChapterC.IsChiBlockIn (pResidual 2 H) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact a.degree_two_or_right_block h hH hgen c d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
