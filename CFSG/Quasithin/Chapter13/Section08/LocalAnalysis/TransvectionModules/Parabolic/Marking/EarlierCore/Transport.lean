module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.NaturalSetup

/-!
# Natural coordinates for the ordinary source residuals

Equivariance identifies relative normalizers with actual subspace stabilizers.
Finite residual-image transport then computes the image of L₁ as the residual
of the point stabilizer, retaining the distinction between the A₄ residual
and the larger duad intersection. Actual commutators lift linear displacement,
and the ambient Sylow subgroup supplies the Sylow action on the flag.

This specializes the transport argument used for the covered natural section
to the ordinary A₆ quotient, with an equivalence on the literal V.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Notations
13.2.1 and 13.3.3, printed pp.877 and 885; 13.8.6, printed p.948.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup
noncomputable section
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

/-- The literal natural six-letter representation, with its original quotient model. -/
abbrev naturalAction := BinaryPermutation.naturalRepresentation (Fin 6)

/-- Permutation image after restricting an ambient subgroup to LT. -/
def permutationImage (A : Subgroup G) : Subgroup (Equiv.Perm (Fin 6)) :=
  (A.subgroupOf (L ⊔ T)).map d.permutation

/-- Compatibility with the ordinary quotient identifies the full alternating image. -/
theorem permutationImage_L : d.permutationImage L = alternatingGroup (Fin 6) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    let l : L := ⟨g.val, hg⟩
    have he := d.model_compatible l
    change d.permutation g = _ at he
    rw [he]
    exact (d.model _).property
  · intro a ha
    obtain ⟨q, hq⟩ := d.model.surjective ⟨a, ha⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    refine ⟨inclusion le_sup_left l, l.property, ?_⟩
    rw [d.model_compatible, hl, hq]

/-- The actual permutation image contains A₆. -/
theorem alternating_le_range : alternatingGroup (Fin 6) ≤ d.permutation.range := by
  rw [← d.permutationImage_L]
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

/-- An element normalizes a flag preimage exactly when its permutation preserves the subspace. -/
theorem flag_normalizer_iff (P : Submodule (ZMod 2) Natural)
    (g : (L ⊔ T : Subgroup G)) :
    g.val ∈ normalizer (flagPreimage d.coordinate P : Set G) ↔
      d.permutation g ∈ subspaceStabilizer naturalAction P := by
  constructor
  · intro hg w
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have hv' : (d.coordinate v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [← hv', ← d.conjugation]
    rw [← mem_flagPreimage_iff, ← mem_flagPreimage_iff]
    exact ((mem_normalizer_iff.mp hg) v.val).symm
  · intro hg
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      let v : V := ⟨x, flagPreimage_le _ _ hx⟩
      have hp : (d.coordinate v).toAdd ∈ P := (mem_flagPreimage_iff _ _ v).mp hx
      have hc := (hg (d.coordinate v).toAdd).mpr hp
      rw [← d.conjugation] at hc
      exact (mem_flagPreimage_iff _ _ _).mpr hc
    · intro hx
      have hv : x ∈ V :=
        (mem_normalizer_iff.mp (d.normalizes_V g.property) x).mpr
          (flagPreimage_le _ _ hx)
      let v : V := ⟨x, hv⟩
      have hc : (d.coordinate (V.normalizerMonoidHom
          ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd ∈ P :=
        (mem_flagPreimage_iff _ _ _).mp hx
      rw [d.conjugation] at hc
      exact (mem_flagPreimage_iff _ _ v).mpr ((hg _).mp hc)

/-- The relative normalizer maps onto the actual point stabilizer in the image of LT. -/
theorem parabolic_image : d.permutationImage (((L ⊔ T) ⊓ normalizer (V₁ : Set G))) =
    d.permutation.range ⊓ subspaceStabilizer naturalAction d.point := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr ⟨g, rfl⟩, ?_⟩
    apply (d.flag_normalizer_iff d.point g).mp
    rw [← d.line_eq]
    exact hg.2
  · rintro a ⟨ha, hp⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp ha
    refine ⟨g, ⟨g.property, ?_⟩, rfl⟩
    rw [d.line_eq]
    exact (d.flag_normalizer_iff d.point g).mpr hp

/-- The other relative normalizer is the plane stabilizer in the same action image. -/
theorem plane_normalizer_image :
    d.permutationImage ((L ⊔ T) ⊓ normalizer (V₂ : Set G)) =
      d.permutation.range ⊓ subspaceStabilizer naturalAction d.plane := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    apply (d.flag_normalizer_iff d.plane g).mp
    rw [← d.plane_eq]
    exact hg.2
  · rintro a ⟨⟨g, rfl⟩, hp⟩
    refine ⟨g, ⟨g.property, ?_⟩, rfl⟩
    rw [d.plane_eq]
    exact (d.flag_normalizer_iff d.plane g).mpr hp

/-- T preserves the actual plane as well as the point and hyperplane. -/
theorem sylow_plane_stable :
    d.permutationImage T ≤ subspaceStabilizer naturalAction d.plane := by
  rintro _ ⟨g, hg, rfl⟩
  apply (d.flag_normalizer_iff d.plane g).mp
  rw [← d.plane_eq]
  exact d.plane_stable hg

/-- The given Sylow subgroup preserves the two actual quotient subspaces. -/
theorem sylow_flag_stable :
    d.permutationImage T ≤ subspaceStabilizer naturalAction d.point ∧
      d.permutationImage T ≤ subspaceStabilizer naturalAction d.hyperplane := by
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    apply (d.flag_normalizer_iff d.point g).mp
    rw [← d.line_eq]
    exact d.line_stable hg
  · rintro _ ⟨g, hg, rfl⟩
    apply (d.flag_normalizer_iff d.hyperplane g).mp
    rw [← d.seed_eq]
    exact d.seed_stable hg

/-- The image of an ambient subgroup on the genuine natural section. -/
def naturalImage (B : Subgroup G) : Submodule (ZMod 2) Natural :=
  AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm ((B.subgroupOf V).map d.coordinate.toMonoidHom))

theorem mem_naturalImage (B : Subgroup G) (w : Natural) :
    w ∈ d.naturalImage B ↔ ∃ v : V, v.val ∈ B ∧ (d.coordinate v).toAdd = w := by
  rfl

theorem point_le_naturalImage_line : d.point ≤ d.naturalImage V₁ := by
  intro w hw
  obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
  have he : (d.coordinate v).toAdd = w := congrArg Multiplicative.toAdd hv
  refine (d.mem_naturalImage V₁ w).mpr ⟨v, ?_, he⟩
  rw [d.line_eq]
  exact (mem_flagPreimage_iff _ _ v).mpr (he.symm ▸ hw)

theorem displacement_le_naturalImage_commutator (A : Subgroup G) :
    subspaceCommutator naturalAction d.hyperplane (d.permutationImage A) ≤
      d.naturalImage ⁅A, V₃⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨g, hg, rfl⟩, w, hw, rfl⟩
  obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
  have he : (d.coordinate v).toAdd = w := congrArg Multiplicative.toAdd hv
  have hv3 : v.val ∈ V₃ := by
    rw [d.seed_eq]
    exact (mem_flagPreimage_iff _ _ v).mpr (he.symm ▸ hw)
  let c : V := V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v * v⁻¹
  refine (d.mem_naturalImage _ _).mpr ⟨c, ?_, ?_⟩
  · exact commutator_mem_commutator hg hv3
  · change (d.coordinate
      (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v * v⁻¹)).toAdd = _
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    change (d.coordinate (V.normalizerMonoidHom
      ⟨g.val, d.normalizes_V g.property⟩ v)).toAdd - (d.coordinate v).toAdd = _
    rw [d.conjugation, he]

theorem naturalImage_mono {A B : Subgroup G} (h : A ≤ B) :
    d.naturalImage A ≤ d.naturalImage B := by
  intro w hw
  obtain ⟨v, hv, he⟩ := (d.mem_naturalImage A w).mp hw
  exact (d.mem_naturalImage B w).mpr ⟨v, h hv, he⟩

/-- Faithfulness of the coordinates lifts any image containment inside V. -/
theorem le_of_naturalImage_le {A B : Subgroup G} (hA : A ≤ V)
    (h : d.naturalImage A ≤ d.naturalImage B) : A ≤ B := by
  intro a ha
  let x : V := ⟨a, hA ha⟩
  obtain ⟨y, hy, he⟩ := h (show (d.coordinate x).toAdd ∈ d.naturalImage A from
    ⟨x, ha, rfl⟩)
  have hxy : y = x := d.coordinate.injective he
  have hx : x.val ∈ B := hxy ▸ hy
  exact hx

/-- Every natural vector represents an element of the literal V. -/
theorem naturalImage_self : d.naturalImage V = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨w, rfl⟩ := d.coordinate.surjective (Multiplicative.ofAdd v)
  exact ⟨w, w.property, rfl⟩

/-- General displacement transport for ambient subgroups in natural coordinates. -/
theorem displacement_image (A B : Subgroup G) :
    subspaceCommutator naturalAction (d.naturalImage B) (d.permutationImage A) ≤
      d.naturalImage ⁅A, B⁆ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨g, hg, rfl⟩, w, ⟨v, hv, rfl⟩, rfl⟩
  let c : V := V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v * v⁻¹
  refine ⟨c, commutator_mem_commutator hg hv, ?_⟩
  change (d.coordinate
    (V.normalizerMonoidHom ⟨g.val, d.normalizes_V g.property⟩ v * v⁻¹)).toAdd = _
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg, d.conjugation]
  rfl

/-- Lift section generation using that the whole kernel lies in the line preimage. -/
theorem seed_le_of_naturalImage (B : Subgroup G) (hline : V₁ ≤ B)
    (hseed : d.hyperplane ≤ d.naturalImage B) : V₃ ≤ B := by
  intro v hv
  let x : V := ⟨v, d.seed_le hv⟩
  have hx : (d.coordinate x).toAdd ∈ d.hyperplane := by
    apply (mem_flagPreimage_iff _ _ x).mp
    rwa [← d.seed_eq]
  obtain ⟨y, hy, he⟩ := (d.mem_naturalImage B _).mp (hseed hx)
  have hk : d.coordinate (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, show d.coordinate x = d.coordinate y from he.symm]
    exact mul_inv_cancel _
  have hxy : ((x * y⁻¹ : V) : G) ∈ V₁ := by
    rw [d.line_eq]
    apply (mem_flagPreimage_iff _ _ (x * y⁻¹)).mpr
    rw [hk]
    exact d.point.zero_mem
  have hm := B.mul_mem (hline hxy) hy
  simpa only [coe_mul, coe_inv, inv_mul_cancel_right] using hm

/-- Linear generation by the actual action lifts to an ambient subgroup commutator. -/
theorem seed_le_commutator_sup_of_displacement (A : Subgroup G)
    (hgen : d.hyperplane ≤
      subspaceCommutator naturalAction d.hyperplane (d.permutationImage A) ⊔ d.point) :
    V₃ ≤ ⁅A, V₃⁆ ⊔ V₁ := by
  apply d.seed_le_of_naturalImage _ le_sup_right
  exact hgen.trans (sup_le
    ((d.displacement_le_naturalImage_commutator A).trans
      (d.naturalImage_mono le_sup_left))
    (d.point_le_naturalImage_line.trans (d.naturalImage_mono le_sup_right)))

/-- Stabilization of the section lifts through its actual inverse image. -/
theorem normalizes_seed_of_image (A : Subgroup G) (hA : A ≤ L ⊔ T)
    (hstable : d.permutationImage A ≤ subspaceStabilizer naturalAction d.hyperplane) :
    A ≤ normalizer (V₃ : Set G) := by
  intro a ha
  rw [d.seed_eq]
  apply (d.flag_normalizer_iff d.hyperplane ⟨a, hA ha⟩).mpr
  exact hstable ⟨⟨a, hA ha⟩, ha, rfl⟩

variable [Finite G]

/-- The image of the actual ambient Sylow subgroup is Sylow in the action image. -/
theorem image_sylow : ∃ Q : Sylow 2 d.permutation.range,
    (Q : Subgroup d.permutation.range).map d.permutation.range.subtype =
      d.permutationImage T := by
  refine ⟨(T.subtype (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    d.permutation.rangeRestrict_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
  rfl

/-- Finite residuals commute with the permutation image of every subgroup of LT. -/
theorem permutationImage_residual (A : Subgroup G) (hA : A ≤ L ⊔ T) :
    d.permutationImage (residual A) = residual (d.permutationImage A) := by
  have he : (residual A).subgroupOf (L ⊔ T) = residual (A.subgroupOf (L ⊔ T)) := by
    apply map_injective (L ⊔ T).subtype_injective
    rw [map_subgroupOf_eq_of_le ((residual_le A).trans hA)]
    change residual A = ((pResidual 2 (A.subgroupOf (L ⊔ T))).map
      (A.subgroupOf (L ⊔ T)).subtype).map (L ⊔ T).subtype
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hA]
    rfl
  unfold permutationImage
  rw [he]
  exact map_embedded_pResidual 2 _ _

/-- L₁ maps to the actual residual of the point stabilizer. -/
theorem one_image : d.permutationImage (localResidual L V₁) =
    residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.point) := by
  rw [← d.line_residual_eq, d.permutationImage_residual _ inf_le_left, d.parabolic_image]

/-- L₂ maps to the plane stabilizer's two-residual, not its whole stabilizer. -/
theorem two_image : d.permutationImage (localResidual L V₂) =
    residual (d.permutation.range ⊓ subspaceStabilizer naturalAction d.plane) := by
  rw [← d.plane_residual_eq, d.permutationImage_residual _ inf_le_left,
    d.plane_normalizer_image]

end
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore.NaturalSetup
