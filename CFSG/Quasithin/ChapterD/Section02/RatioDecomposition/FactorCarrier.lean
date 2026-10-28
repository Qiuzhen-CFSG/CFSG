module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Embedded
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.ComponentSum
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Literal quotient carrier for a classified factor

A factor embedded in the selected faithful action has an actual normal binary
subgroup of the original local subgroup. Its linear space is carried by an
explicit equivariant equivalence, while the action quotient lifts through the
literal map from the local subgroup. These definitions expose the exact
carrier needed to instantiate the p.1085 component exclusion.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
variable {G D : Type*} [Group G] [Group D]
  {M V : Subgroup G} (hVM : V ≤ M) [IsElementaryAbelian 2 V]
  (ρ : Representation (ZMod 2) D (Additive V))
  (q : M →* D) (hq : Function.Surjective q)
  (hact : ∀ (m : M) (v : Additive V), ((ρ (q m) v).toMul : G) = (m:G) * v.toMul * (m:G)⁻¹)
  (F : Factor ρ)

noncomputable def internalSubgroup : Subgroup M :=
  (Subgroup.toAddSubgroup.symm F.space.toAddSubgroup).map (inclusion hVM)

 theorem internalSubgroup_le : F.internalSubgroup hVM ≤ V.subgroupOf M := by
  rintro x ⟨v,hv,rfl⟩
  exact v.property

instance internalSubgroup_elementary : IsElementaryAbelian 2 (F.internalSubgroup hVM) := by
  let R : Subgroup V := Subgroup.toAddSubgroup.symm F.space.toAddSubgroup
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_injective R.subtype R.subtype_injective
  exact IsElementaryAbelian.map (inclusion hVM)

include hact in
 theorem internalSubgroup_normal [F.actor.Normal] : (F.internalSubgroup hVM).Normal := by
  have hstable : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ F.space := by
    rw [F.space_eq_support]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
  constructor
  intro x hx m
  obtain ⟨v,hv,rfl⟩ := hx
  refine ⟨(ρ (q m) (Additive.ofMul v)).toMul, (hstable (mem_top _) _).2 hv,?_⟩
  exact Subtype.ext (hact m (Additive.ofMul v))

noncomputable def internalSpaceMap : F.Space →ₗ[ZMod 2] Additive (F.internalSubgroup hVM) :=
  (({
    toFun v := Additive.ofMul ⟨inclusion hVM (F.embedding.spaceMap v).toMul,
      ⟨(F.embedding.spaceMap v).toMul,⟨v,rfl⟩,rfl⟩⟩
    map_zero' := by apply Additive.toMul.injective; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun v : Additive V => (v.toMul : G)) (map_zero F.embedding.spaceMap)
    map_add' v w := by apply Additive.toMul.injective; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun v : Additive V => (v.toMul : G)) (map_add F.embedding.spaceMap v w)
  } : F.Space →+ Additive (F.internalSubgroup hVM)).toZModLinearMap 2)

 theorem internalSpaceMap_bijective : Function.Bijective (F.internalSpaceMap hVM) := by
  constructor
  · intro v w h
    apply F.embedding.space_injective
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun v : Additive (F.internalSubgroup hVM) => ((v.toMul : M) : G)) h
  · intro w
    obtain ⟨v,hv,hvw⟩ := w.toMul.property
    obtain ⟨y,hy⟩ := hv
    refine ⟨y,?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun v : Additive V => (v.toMul : G)) hy).trans (congrArg Subtype.val hvw)

noncomputable def internalSpaceEquiv : F.Space ≃ₗ[ZMod 2] Additive (F.internalSubgroup hVM) :=
  LinearEquiv.ofBijective (F.internalSpaceMap hVM) (F.internalSpaceMap_bijective hVM)

include hact in
 theorem kernel_le_internalCentralizer : q.ker ≤ centralizer (F.internalSubgroup hVM : Set M) := by
  intro g hg v hv
  obtain ⟨v,hv,rfl⟩ := hv
  have hh := hact g (Additive.ofMul v)
  rw [show q g = 1 from hg,map_one,Module.End.one_apply] at hh
  exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

variable [(F.internalSubgroup hVM).Normal]

noncomputable def internalProjection : D →* M ⧸ centralizer (F.internalSubgroup hVM : Set M) :=
  q.liftOfSurjective hq ⟨QuotientGroup.mk' _,
    by rw [QuotientGroup.ker_mk']; exact F.kernel_le_internalCentralizer hVM ρ q hact⟩

 theorem internalProjection_apply (m : M) :
    F.internalProjection hVM ρ q hq hact (q m) = QuotientGroup.mk' _ m := by
  unfold internalProjection
  rw [MonoidHom.liftOfRightInverse_comp_apply]

 theorem internalProjection_surjective : Function.Surjective (F.internalProjection hVM ρ q hq hact) := by
  intro x
  obtain ⟨m,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (F.internalSubgroup hVM : Set M)) x
  exact ⟨q m,F.internalProjection_apply hVM ρ q hq hact m⟩

 theorem internalProjection_intertwines (g : F.Carrier) (v : F.Space) :
    F.internalSpaceEquiv hVM ρ (F.action g v) =
      NormalElementaryQuotient.representation (F.internalSubgroup hVM)
        (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        (F.internalProjection hVM ρ q hq hact (F.embedding.groupMap g))
        (F.internalSpaceEquiv hVM ρ v) := by
  obtain ⟨m,hm⟩ := hq (F.embedding.groupMap g)
  rw [← hm, F.internalProjection_apply hVM ρ q hq hact]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [NormalElementaryQuotient.representation_apply]
  change ((F.embedding.spaceMap (F.action g v)).toMul : G) =
    (m : G) * (F.embedding.spaceMap v).toMul * (m : G)⁻¹
  rw [F.embedding.equivariant,← hm]
  exact hact m (F.embedding.spaceMap v)

 theorem internalProjection_factor_injective :
    Function.Injective ((F.internalProjection hVM ρ q hq hact).comp F.embedding.groupMap) := by
  intro g h he
  apply F.faithful
  ext v
  apply (F.internalSpaceEquiv hVM ρ).injective
  rw [F.internalProjection_intertwines hVM ρ q hq hact,
    F.internalProjection_intertwines hVM ρ q hq hact]
  exact congrArg (fun a => NormalElementaryQuotient.representation (F.internalSubgroup hVM)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    a (F.internalSpaceEquiv hVM ρ v)) he


 theorem internalProjection_core_normal [F.actor.Normal] (p : ℕ) :
    ((pCore p F.Carrier).map
      ((F.internalProjection hVM ρ q hq hact).comp F.embedding.groupMap)).Normal := by
  have he : (pCore p F.Carrier).map F.embedding.groupMap = F.actor.pCoreIn p :=
    (pCoreIn_range_of_injective p _ F.embedding.group_injective).symm
  rw [← map_map,he]
  let : (F.actor.pCoreIn p).Normal := inferInstanceAs ((pCore p F.actor).map F.actor.subtype).Normal
  exact Subgroup.Normal.map inferInstance _ (F.internalProjection_surjective hVM ρ q hq hact)

end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
