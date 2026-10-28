module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceSetup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceFixedLines
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Source normalizers and hyperplane uniqueness in 14.7.66–67

The actual quotient maps give 14.7.66. On the original U/V₁, the earlier
14.7.2(1) implication shows that the flag plane has a nonzero image in the
natural quotient. The checked original-action fixed-line calculation then
gives C_G(V₂) ≤ T. Extending automorphisms of a subspace of the natural
L₃(2) module factors its ambient normalizer through L and its centralizer.
This proves G₂ ≤ LT, LT = N_G(V), and uniqueness over every hyperplane.

The natural quotient uses the same p and the actual H → H/O₂(H) → S₅.
Its kernel and the alternating K-image are proved here. U₀ is the actual
fixed-space preimage, is elementary abelian and H-invariant, and meets V
in V₁. No fixed-element fusion or rank-two bound on U₀ is assumed or proved
by these elementary preliminaries.

Earlier inputs remain explicit: `EarlierImages` comes from Notation 14.7.1,
14.7.4(4), and the paragraph before 14.7.65; `ModuleSeparation` is 14.7.2(1).
The sole use of `Structural1222` is T-normalization of L in 14.7.67(1).
The existing qt-14-07 solvable/component and Chapter 12 producers discharge
these earlier implications in source assembly. Clauses 14.7.67(3)–(4)
and 14.7.68–70 remain separate proof obligations.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.2(1), p.1043; 14.7.66–67, pp.1070–1071.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
/-- The source Q really is contained in the domain of the star quotient. -/
theorem Q_le_H (F : InvariantFlag T V 3) : Q T L ≤ F.H := by
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  exact hQT.trans (F.invariant 1)

namespace CriticalPath
variable (c : CriticalPath (L := L) F)

omit [Finite G] in
/-- The critical image is taken of the whole Uα, not merely its intersection with H. -/
theorem Uα_le_H (earlier : c.EarlierImages) : c.Uα ≤ F.H := by
  apply earlier.placement.trans
  apply (pCoreIn_le 2 _).trans
  exact sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)

omit [Finite G] in
/-- 14.7.66 with the literal quotient and a Sylow subgroup of the actual K-image. -/
theorem lemma_14_7_66 (earlier : c.EarlierImages) :
    star F c.Uα ≤ star F (Q T L) ∧
      Chapter1.IsSylowIn 2 (star F (Q T L)) (star F (K F)) := by
  rw [earlier.image_eq]
  exact ⟨map_mono (subgroupOf_mono F.H earlier.placement), earlier.sylow⟩
end CriticalPath

namespace Data
variable (d : Data T L V F W)

omit [Finite G] in
theorem V_le_U (F : InvariantFlag T V 3) : V ≤ F.U := le_conjugateSpanBy V F.H

theorem qH_surjective : Function.Surjective d.qH :=
  d.model.surjective.comp (QuotientGroup.mk'_surjective _)

theorem qH_ker : d.qH.ker = (F.H.pCoreIn 2).subgroupOf F.H := by
  ext x
  change d.model (QuotientGroup.mk' (pCore 2 F.H) x) = 1 ↔ _
  rw [← d.model.map_one, d.model.injective.eq_iff]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  change x ∈ pCore 2 F.H ↔ x.val ∈ (pCore 2 F.H).map F.H.subtype
  exact (mem_map_iff_mem F.H.subtype_injective).symm

/-- The two-residual has the actual alternating image in the same S₅ marking. -/
theorem K_image : ((K F).subgroupOf F.H).map d.qH = alternatingGroup (Fin 5) := by
  change (((pResidual 2 F.H).map F.H.subtype).comap F.H.subtype).map d.qH = _
  rw [comap_map_eq_self_of_injective F.H.subtype_injective,
    map_pResidual_of_surjective 2 d.qH d.qH_surjective,
    Equiv.Perm.twoResidual_eq_alternating]

theorem mem_U₀ (u : F.U) : (u : G) ∈ d.U₀ ↔
    (d.conjugationSection.coordinates u).toAdd ∈ d.projection.toLinearMap.ker := by
  change u.val ∈ (Subgroup.map F.U.subtype _) ↔ _
  refine (mem_map_iff_mem (f := F.U.subtype) (x := u) F.U.subtype_injective).trans ?_
  change (d.conjugationSection.coordinates u).toAdd ∈ Representation.invariants _ ↔ _
  rw [d.fixed_kernel]

theorem U₀_le_U : d.U₀ ≤ F.U := map_subtype_le _

theorem point_le_U₀ : F.Vi 1 ≤ d.U₀ := by
  intro u hu
  let v : F.U := ⟨u, d.conjugationSection.kernel_le hu⟩
  apply (d.mem_U₀ v).mpr
  have hzero : (d.conjugationSection.coordinates v).toAdd = 0 :=
    (d.conjugationSection.coordinates_eq_one_iff v).mpr hu
  rw [hzero]
  exact Submodule.zero_mem _

theorem projection_ker_ne_top : d.projection.toLinearMap.ker ≠ ⊤ := by
  intro hk
  obtain ⟨v, hv⟩ := exists_ne (0 : Representation.SL2FourNatural.V)
  obtain ⟨w, rfl⟩ := d.projection_onto v
  exact hv (show d.projection w = 0 from (show w ∈ d.projection.toLinearMap.ker by rw [hk]; trivial))

theorem projection_ker_invariant (h : F.H) (w : W)
    (hw : w ∈ d.projection.toLinearMap.ker) :
    d.action h w ∈ d.projection.toLinearMap.ker := by
  change d.projection (d.action h w) = 0
  have he : d.projection (d.action h w) =
      d.naturalQuotient.action (d.qH h) (d.projection w) :=
    LinearMap.congr_fun (d.projection.isIntertwining' h) w
  rw [he, show d.projection w = 0 from hw, map_zero]

/-- H preserves the fixed-space preimage because the original projection is equivariant. -/
theorem H_normalizes_U₀ : F.H ≤ normalizer (d.U₀ : Set G) := by
  apply le_normalizer_iff.mpr
  intro h hh u hu
  let v : F.U := ⟨u, d.U₀_le_U hu⟩
  let v' : F.U := ⟨h * u * h⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized hh) u).mp v.property⟩
  apply (d.mem_U₀ v').mpr
  rw [d.conjugationSection.equivariant ⟨h, hh⟩ v]
  exact d.projection_ker_invariant ⟨h, hh⟩ _ ((d.mem_U₀ v).mp hu)

include d in
theorem U_elementary : IsElementaryAbelian 2 F.U := by
  let := d.natural.chosen.elementary
  let : IsMulCommutative (closure {x : G | ∃ h ∈ F.H, ∃ v ∈ V, h * v * h⁻¹ = x}) := d.abelian
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨h, _, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]

theorem U₀_elementary : IsElementaryAbelian 2 d.U₀ := by
  let := d.U_elementary
  exact IsElementaryAbelian.of_le d.U₀_le_U

theorem z_mem_U₀ : d.z ∈ d.U₀ := by
  apply d.point_le_U₀
  rw [d.point]
  exact mem_zpowers d.z

theorem seed_projection_zero_iff (earlier : d.ModuleSeparation)
    (v : F.U) (hv : (v : G) ∈ V) :
    d.projection (d.conjugationSection.coordinates v).toAdd = 0 ↔ (v : G) ∈ F.Vi 1 :=
  earlier _ d.projection_ker_invariant d.projection_ker_ne_top v hv

/-- The earlier proper-submodule theorem identifies the intersection with the original V. -/
theorem seed_inf_U₀ (earlier : d.ModuleSeparation) : V ⊓ d.U₀ = F.Vi 1 := by
  apply le_antisymm
  · intro v hv
    exact (d.seed_projection_zero_iff earlier ⟨v, V_le_U F hv.1⟩ hv.1).mp
      ((d.mem_U₀ ⟨v, V_le_U F hv.1⟩).mp hv.2)
  · exact le_inf (F.le_seed 1) d.point_le_U₀

theorem exists_plane_point (earlier : d.ModuleSeparation) :
    ∃ v : F.U, (v : G) ∈ F.Vi 2 ∧ d.projection (d.conjugationSection.coordinates v).toAdd ≠ 0 := by
  have hn : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro h
    have hc := Nat.card_le_card_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
    rw [F.card 2 (by decide), F.card 1 (by decide)] at hc
    norm_num at hc
  obtain ⟨v, hv, hv1⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨⟨v, V_le_U F (F.le_seed 2 hv)⟩, hv,
    fun hz => hv1 ((d.seed_projection_zero_iff earlier _ (F.le_seed 2 hv)).mp hz)⟩

/-- The original flag and natural action give C_G(V₂) ≤ T. -/
theorem plane_centralizer_le (earlier : d.ModuleSeparation) :
    centralizer (F.Vi 2 : Set G) ≤ (T : Subgroup G) := by
  let TH : Sylow 2 F.H := T.subtype (F.invariant 1)
  let P : Sylow 2 ChapterJ.S5 := TH.mapSurjective d.qH_surjective
  have hTP : (TH : Subgroup F.H).map d.qH = (P : Subgroup ChapterJ.S5) :=
    (Sylow.coe_mapSurjective d.qH_surjective TH).symm
  obtain ⟨v, hv, hn⟩ := d.exists_plane_point earlier
  have hc := source_plane_centralizer_le d.naturalQuotient d.action d.qH d.conjugationSection
    d.projection TH P hTP d.qH_ker ((F.le_seed 2).trans (V_le_U F))
    (F.monotone (by decide : 1 ≤ 2)) (by simpa using F.card 1 (by decide))
    (by simpa using F.card 2 (by decide))
    (fun t => F.invariant 2 t.property) v hv hn
  have hTH : (TH : Subgroup F.H).map F.H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (F.invariant 1)
  rw [hTH] at hc
  have hz : d.z ∈ F.Vi 2 := by
    apply F.monotone (by decide : 1 ≤ 2)
    rw [d.point]
    exact mem_zpowers d.z
  have hCH : centralizer (F.Vi 2 : Set G) ≤ F.H := by
    rw [d.centralizer_eq]
    exact centralizer_le (Set.singleton_subset_iff.mpr hz)
  exact (le_inf hCH le_rfl).trans hc

/-- The full natural L-action and the plane centralizer give G₂ ≤ LT. -/
theorem plane_normalizer_le (earlier : d.ModuleSeparation) :
    F.Gi 2 ≤ L ⊔ (T : Subgroup G) := by
  let := d.natural.chosen.elementary
  intro g hg
  obtain ⟨c, hc, l, hl, rfl⟩ :=
    (NormalGeometry.normalizer_factorization d.natural.naturalMarking.geometryAction
      (F.Vi 2) (F.le_seed 2)).le hg
  exact (L ⊔ (T : Subgroup G)).mul_mem (mem_sup_right (d.plane_centralizer_le earlier hc))
    (mem_sup_left hl.1)

/-- 14.7.67(1): G₂ lies in the original M = N_G(L). -/
theorem lemma_14_7_67_one (earlier : d.ModuleSeparation)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    F.Gi 2 ≤ normalizer (L : Set G) :=
  (d.plane_normalizer_le earlier).trans
    (sup_le L.le_normalizer (d.natural.sylow_normalizes structural))

/-- 14.7.67(5): the full ambient normalizer of the original V is LT. -/
theorem lemma_14_7_67_five (earlier : d.ModuleSeparation) :
    L ⊔ (T : Subgroup G) = normalizer (V : Set G) := by
  let := d.natural.chosen.elementary
  apply le_antisymm
  · apply sup_le d.natural.chosen.normalizes
    simpa only [F.last] using F.invariant 3
  · intro g hg
    obtain ⟨c, hc, l, hl, rfl⟩ :=
      (NormalGeometry.normalizer_factorization d.natural.naturalMarking.geometryAction V le_rfl).le hg
    exact (L ⊔ (T : Subgroup G)).mul_mem
      (mem_sup_right (d.plane_centralizer_le earlier (centralizer_le (F.le_seed 2) hc)))
      (mem_sup_left hl.1)

omit [Finite G] in
private theorem conjugate_mul (A : Subgroup G) (g h : G) :
    conjugate A (g * h) = conjugate (conjugate A g) h := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- 14.7.67(2): an order-four hyperplane of the rank-three V lies in a unique G-conjugate. -/
theorem lemma_14_7_67_two (earlier : d.ModuleSeparation)
    (A : Subgroup G) (hAV : A ≤ V) (hcard : Nat.card A = 4)
    (g : G) (hAg : A ≤ conjugate V g) : conjugate V g = V := by
  have hplane : ∀ g : G, F.Vi 2 ≤ conjugate V g → conjugate V g = V := by
    intro g hg
    obtain ⟨k, hk, he⟩ := d.natural.flag_transporter F 2 g hg
    exact he.trans ((conjugate_eq_iff V k).mpr
      (d.lemma_14_7_67_five earlier ▸ d.plane_normalizer_le earlier hk))
  obtain ⟨l, hl, hAl⟩ := d.natural.subspace_transitive A (F.Vi 2) hAV (F.le_seed 2)
    (hcard.trans (by simpa using (F.card 2 (by decide)).symm))
  have hg' : F.Vi 2 ≤ conjugate V (g * l) := by
    rw [conjugate_mul, ← hAl]
    exact map_mono hAg
  have he : conjugate (conjugate V g) l = conjugate V l := by
    rw [← conjugate_mul, hplane _ hg',
      (conjugate_eq_iff V l).mpr (d.natural.chosen.normalizes hl)]
  exact (Subgroup.map_injective (MulAut.conj l⁻¹).injective) he

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
