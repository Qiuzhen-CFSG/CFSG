module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEvenComplete
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The full symmetric central cover with the cubic kernel retained

The even-image exclusion makes the original natural action surjective onto
S₆ at every distance in the cubic-kernel case. Full component movement lets
the six-letter perfect-cover theorem identify the entire initial moved
subgroup as the natural four-space or the augmentation five-space. Its fixed
kernel has order one or two. Normality makes this kernel central in the
whole original vertex group, so the quotient is by the actual ambient center.

The graph construction carries the full moved subgroup, two-core, and cubic
kernel through the same conjugated factor embedding. The marked quotient
intertwines the original action at every component vertex. Both orders 16
and 32 are retained. This extends the distance-two cover calculation without
assuming distance two, a Sylow radical, or whole-core exhaustion.
`CubicRadius` uses the cover map to bound radius images on the original graph.
The remaining Section 5 exclusions and final natural/exceptional assembly
stay with qt-e-ms-small-a6-reconstruction.

Source: MS93 (3.2)(vi), (5.0), printed pp.863--864 and912; Aschbacher--Smith
B.3.1--3 and I.1.5--6, pp.83--84 and408. The cover argument adapts the existing
CubicCriticalLine and Natural.Exhaustion.LargeDistance.SectionFive proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open CubicAction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X₀" => centralOmega L R
local notation "W" => (⁅X₀,K⁆ : Subgroup M)
local notation "q" => QuotientGroup.mk' (layerKernel L R)
local notation "π" => projection h e hz hk
local notation "s" => layerSection h
local notation "ρ₆" => BinaryPermutation.naturalRepresentation (Fin 6)
local notation "T" => edge L R

/-- The entire initial moved cover, with its original six-letter marking. -/
theorem moved_cover_model :
    BinaryPermutation.SixCover.IsNaturalOrCore (s).space.toRepresentation
      (permutationAction h e hz hk) := by
  let E : LayerActor L R ≃* Equiv.Perm (Fin 6) :=
    MulEquiv.ofBijective (permutationAction h e hz hk)
      ⟨permutationAction_injective h e hz hk, fun g => by
        obtain ⟨m,hm⟩ := CubicEven.projection_surjective h e hz hk g
        exact ⟨q m,hm⟩⟩
  let c := coordinates h e hz hk
  let p := ((s).coverProjection c).toLinearMap
  have hC : (layerComponent L R).map E.toMonoidHom = alternatingGroup (Fin 6) := by
    change ((K).map q).map (permutationAction h e hz hk) = _
    rw [map_map]
    exact component_image h e hz hk
  have hp (g : LayerActor L R) (v : (s).space.toSubmodule) :
      p ((s).space.toRepresentation g v) = ρ₆ (E g) (p v) := by
    exact ((s).coverProjection_ambient c g v).trans
      (permutationAction_apply h e hz hk g (p v))
  have hsur : Function.Surjective p :=
    ((s).coverProjection_isCover (layer_moved_alternating h e hz hk).1 c).1
  have hker : p.ker ≤ fixedSpace (s).space.toRepresentation (layerComponent L R) := by
    intro v hv
    have hzv : (s).central.toSubmodule.mkQ v = 0 :=
      c.linearEquiv.injective (hv.trans c.linearEquiv.map_zero.symm)
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hzv
    rwa [(s).central_eq] at hm
  have hgen : subspaceCommutator (s).space.toRepresentation ⊤ (layerComponent L R) = ⊤ := by
    have hi := (layer_moved_alternating h e hz hk).1
    have hm : (s).space.toSubmodule ≤
        (subspaceCommutator (s).space.toRepresentation ⊤ (layerComponent L R)).map
          (s).space.toSubmodule.subtype := by
      have hi' : IsIrrPlus (layerAction L R) (layerComponent L R) (s).space.toSubmodule :=
        (s).space_eq.symm ▸ hi
      conv_lhs => rw [←hi'.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,hv,rfl⟩
      exact ⟨(s).space.toRepresentation g ⟨v,hv⟩-⟨v,hv⟩,
        Submodule.subset_span ⟨g,hg,⟨v,hv⟩,Submodule.mem_top,rfl⟩,rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w,hw,he⟩ := hm v.property
    rwa [show w=v from Subtype.ext he] at hw
  exact BinaryPermutation.SixCover.naturalOrCore_symmetric (s).space.toRepresentation E
    (layerComponent L R) hC p hp hsur hker hgen

include h e hz hk in
/-- The exact six-letter marking on the whole moved subgroup, including its fixed line. -/
theorem moved_subgroup_cover_model :
    let := h.relative_normal
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
    BinaryPermutation.SixCover.IsNaturalOrCore
      (NormalElementaryQuotient.representation W π
        (CubicEven.projection_surjective h e hz hk) (moved_projection_kernel h e hz hk))
      (MonoidHom.id _) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  let E := NormalElementaryQuotient.movedEquiv X₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  let ρ := NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (moved_projection_kernel h e hz hk)
  have hE (g : M) (v : Additive W) :
      E (ρ (π g) v) = (layerSection h).space.toRepresentation (q g) (E v) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (moved_projection_kernel h e hz hk) g v).trans
      (NormalElementaryQuotient.representation_apply X₀ q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g (E v).val).symm
  rcases moved_cover_model h e hz hk with ⟨f,hf⟩ | ⟨f,hf⟩
  · left
    refine ⟨E.trans f,?_⟩
    intro a v
    obtain ⟨g,rfl⟩ := CubicEven.projection_surjective h e hz hk a
    exact (congrArg f (hE g v)).trans (hf (q g) (E v))
  · right
    refine ⟨E.trans f,?_⟩
    intro a v
    obtain ⟨g,rfl⟩ := CubicEven.projection_surjective h e hz hk a
    exact (congrArg f (hE g v)).trans (hf (q g) (E v))


include h e hz hk in
/-- Both orders of the original moved cover remain possible at every distance. -/
theorem moved_card : Nat.card W = 16 ∨ Nat.card W = 32 := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  rcases moved_subgroup_cover_model h e hz hk with ⟨E, _⟩ | ⟨E, _⟩
  · left
    change Nat.card (Additive W) = 16
    rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank («K» := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  · right
    change Nat.card (Additive W) = 32
    rw [Nat.card_congr E.toEquiv, Module.natCard_eq_pow_finrank («K» := ZMod 2),
      BinaryPermutation.finrank_core]
    norm_num

/-- The original marked quotient on the entire moved subgroup. -/
@[expose] def coverProjection : W →* Multiplicative (BinaryPermutation.natural (Fin 6)) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  let p := Classical.choose (moved_natural_projection h e hz hk)
  exact p.toAddMonoidHom.toMultiplicative

theorem coverProjection_surjective : Function.Surjective (coverProjection h e hz hk) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  exact (Classical.choose_spec (moved_natural_projection h e hz hk)).1

theorem coverProjection_kernel :
    (coverProjection h e hz hk).ker = (centralizer (K : Set M)).subgroupOf W := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  ext v
  exact (Classical.choose_spec (moved_natural_projection h e hz hk)).2.1 (Additive.ofMul v)

theorem coverProjection_conjugate (g : M) (v w : W)
    (hw : (w : M) = g * (v : M) * g⁻¹) :
    (coverProjection h e hz hk w).toAdd = ρ₆ (π g) (coverProjection h e hz hk v).toAdd := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  have he : w = MulAut.conjNormal g v := Subtype.ext hw
  rw [he]
  exact (Classical.choose_spec (moved_natural_projection h e hz hk)).2.2 g (Additive.ofMul v)

include h e hz hk in
/-- The full fixed kernel has order at most two. -/
theorem coverProjection_kernel_card :
    Nat.card (coverProjection h e hz hk).ker = 1 ∨
      Nat.card (coverProjection h e hz hk).ker = 2 := by
  let f := coverProjection h e hz hk
  have hr : Nat.card f.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr (coverProjection_surjective h e hz hk),
      Nat.card_congr (topEquiv).toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank («K» := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hc := f.ker.card_mul_index
  rw [index_ker, hr] at hc
  have hm := moved_card h e hz hk
  change Nat.card f.ker = 1 ∨ Nat.card f.ker = 2
  omega

include h e hz hk in
/-- The component-fixed attachment is central in the whole original vertex group. -/
theorem moved_fixed_le_center : W ⊓ centralizer (K : Set M) ≤ center M := by
  let := h.relative_normal
  let C := W ⊓ centralizer (K : Set M)
  have he : (coverProjection h e hz hk).ker.map (W).subtype = C := by
    rw [coverProjection_kernel]
    change ((centralizer (K : Set M)).comap (W).subtype).map (W).subtype = C
    rw [map_comap_eq, range_subtype]
  have hc : Nat.card C = 1 ∨ Nat.card C = 2 := by
    rw [←he,card_map_of_injective (W).subtype_injective]
    exact coverProjection_kernel_card h e hz hk
  rcases hc with hc | hc
  · exact (Subgroup.card_eq_one.mp hc).le.trans bot_le
  · exact central_of_normal_card_two C hc

include h e hz hk in
/-- The quotient retains precisely the actual ambient-center attachment. -/
theorem coverProjection_kernel_center :
    (coverProjection h e hz hk).ker = (center M).subgroupOf W := by
  rw [coverProjection_kernel]
  ext v
  constructor
  · intro hv
    exact moved_fixed_le_center h e hz hk ⟨v.property,hv⟩
  · intro hv
    exact center_le_centralizer (K : Set M) hv


include h e hz in
/-- The literal graph moving layer is the image of the entire initial commutator. -/
theorem graph_U_map : (W).map (embedM T) = U T (alpha T) := by
  rw [graph_U_eq_X_commutator h e hz,graph_X h,graph_component h,←map_commutator]

include h e hz hk in
/-- The actual moving layer at every component vertex retains both cover orders. -/
theorem graph_U_card (a : Vertex T) (ha : color T a = false) :
    Nat.card (U T a) = 16 ∨ Nat.card (U T a) = 32 := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  have hu := U_act T g (alpha T)
  simp only [alpha,act_mVertex,one_mul] at hu
  rw [hu,card_map_of_injective (MulAut.conj g⁻¹).injective]
  change Nat.card (U T (alpha T)) = 16 ∨ Nat.card (U T (alpha T)) = 32
  rw [←graph_U_map h e hz,card_map_of_injective (embedM_injective T)]
  exact moved_card h e hz hk

include h e hz hk in
/-- Source (5.0)'s central quotient at every vertex, with the original action
and cubic kernel carried by the same embedding. -/
theorem graph_cover (a : Vertex T) (ha : color T a = false) :
    ∃ i : M →* FreeAmalgam T, Function.Injective i ∧
      i.range = stabilizer T a ∧ (pCore 2 M).map i = Q T a ∧
      (extensionKernel h).map i =
        stabilizer T a ⊓ centralizer (X T a : Set (FreeAmalgam T)) ∧
      (W).map i = U T a ∧
      ∃ p : U T a →* Multiplicative (BinaryPermutation.natural (Fin 6)),
        Function.Surjective p ∧
        p.ker = (centralizer (stabilizer T a : Set (FreeAmalgam T))).subgroupOf (U T a) ∧
        ∀ (g : M) (v w : U T a),
          (w : FreeAmalgam T) = i g * v * (i g)⁻¹ →
            (p w).toAdd = ρ₆ (π g) (p v).toAdd := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective T)
  have hr : i.range = stabilizer T (mVertex T g) := by
    rw [MonoidHom.range_comp]
    change (Mbar T).map _ = _
    rw [←stabilizer_m_base T]
    simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act T g (alpha T)).symm
  have hQ : (pCore 2 M).map i = Q T (mVertex T g) := by
    rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    simpa only [alpha,act_mVertex,one_mul] using (Q_act T g (alpha T)).symm
  have hX : (X₀).map i = X T (mVertex T g) := by
    rw [←map_map,←graph_X h]
    simpa only [alpha,act_mVertex,one_mul] using (X_act T g (alpha T)).symm
  have hW : (W).map i = U T (mVertex T g) := by
    rw [←map_map,graph_U_map h e hz]
    simpa only [alpha,act_mVertex,one_mul] using (U_act T g (alpha T)).symm
  have hE : (extensionKernel h).map i =
      stabilizer T (mVertex T g) ⊓ centralizer (X T (mVertex T g) : Set (FreeAmalgam T)) := by
    rw [←hk,←hX,←hr]
    apply le_antisymm
    · exact le_inf (map_le_range _ _) (map_centralizer_le_centralizer_image _ _)
    · rintro x ⟨⟨y,rfl⟩,hx⟩
      refine ⟨y,?_,rfl⟩
      intro z hz
      exact hi (by simpa only [map_mul] using hx _ (mem_map_of_mem i hz))
  let E : W ≃* U T (mVertex T g) :=
    ((W).equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hW)
  have hEv (v : U T (mVertex T g)) : i (E.symm v) = v :=
    congrArg Subtype.val (E.apply_symm_apply v)
  let p := (coverProjection h e hz hk).comp E.symm.toMonoidHom
  refine ⟨i,hi,hr,hQ,hE,hW,p,(coverProjection_surjective h e hz hk).comp E.symm.surjective,?_,?_⟩
  · ext v
    change E.symm v ∈ (coverProjection h e hz hk).ker ↔ _
    rw [coverProjection_kernel_center]
    constructor
    · intro hv y hy
      obtain ⟨z,rfl⟩ := hr.symm ▸ hy
      change i z * (v : FreeAmalgam T) = (v : FreeAmalgam T) * i z
      rw [←hEv v,←map_mul,←map_mul]
      exact congrArg i (mem_center_iff.mp hv z)
    · intro hv
      apply mem_center_iff.mpr
      intro z
      apply hi
      change i (z * (E.symm v : M)) = i ((E.symm v : M) * z)
      rw [map_mul,map_mul,hEv]
      exact hv (i z) (hr ▸ (show i z ∈ i.range from ⟨z,rfl⟩))
  · intro z v w hw
    apply coverProjection_conjugate h e hz hk z (E.symm v) (E.symm w)
    apply hi
    rw [map_mul,map_mul,map_inv,hEv,hEv]
    exact hw

include h e hz hk in
/-- The cubic action always lies in the still-unresolved larger-distance case. -/
theorem distance_gt_two : 2 < sourceDistance h := by
  by_contra! hb
  exact cubic_distanceTwo_impossible h e hz hk (sourceDistance_eq_two h hb)

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
