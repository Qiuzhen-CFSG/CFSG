module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativePlane
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Residual

/-!
# The literal native point–line parabolic

In the native trio coordinates, the intersection of the octad and trio
cores consists of translations `(0,v,v)`, so it has order eight. Its two
nontrivial orbits are the other two octads of the trio. Consequently its
normalizer inside the octad group is exactly the point–line stabilizer.
Transport through the natural four-space coordinates identifies this group
with the hyperplane parabolic, without a group-order comparison.

The native common four lies in this common eight: sextet translations fix
all three trio parts, and pointwise fixation of the first octad forces the
common affine linear part to be trivial. The resulting nested pair is used
by `AlignFlags` to align both source flags with one vertex isomorphism.

Source: Aschbacher, *Sporadic Groups* (1994), 19.8–20.2, pp.96–98,
and 41.4, p.222. The underlying native affine coordinates and their source
attribution are documented in `ChapterHStabilizers.TrioAction`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativeLine
open M24ChapterHStabilizers M24ChapterHStabilizers.OctadAction
open PairOvergroups PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation

private theorem standardOctad_eq : standardOctad.val = standardTrioOctad 0 := by decide +kernel

/-- The common eight in the literal octad and trio cores. -/
@[expose] def common : Subgroup M24 := AmbientCore standardOctad ⊓ TrioAction.core

private theorem ambientTranslation_point (t : Multiplicative TrioAction.translationSpace)
    (i : Fin 3) (v : Vector) :
    (TrioAction.ambientTranslationEquiv t).val.val (point (i,v)) =
      point (i,v + t.toAdd.val i) := TrioAction.translation_point t i v

/-- In trio coordinates the common eight consists of translations vanishing
on the marked octad. -/
theorem translation_mem_common (t : Multiplicative TrioAction.translationSpace) :
    (TrioAction.ambientTranslationEquiv t).val ∈ common ↔ t.toAdd.val 0 = 0 := by
  change _ ∈ AmbientCore standardOctad ∧ _ ∈ TrioAction.core ↔ _
  rw [show AmbientCore standardOctad = octadPointwiseKernel standardOctad from
    octad_core_map_eq_pointwise standardOctad]
  simp only [(TrioAction.ambientTranslationEquiv t).property, and_true,
    mem_octadPointwiseKernel]
  constructor
  · intro h
    have he := h (point (0,0)) (standardOctad_eq ▸ point_mem_octad 0 0)
    change (TrioAction.ambientTranslationEquiv t).val.val _ = _ at he
    rw [ambientTranslation_point] at he
    simpa using congrArg Prod.snd (point.injective he)
  · intro h x hx
    obtain ⟨⟨i,v⟩, rfl⟩ := point.surjective x
    rw [standardOctad_eq] at hx
    have hi := (point_mem_octad_iff i 0 v).mp hx
    subst i
    change (TrioAction.ambientTranslationEquiv t).val.val _ = _
    rw [ambientTranslation_point, h, add_zero]

private def translationAt (v : Vector) : TrioAction.translationSpace :=
  ⟨![0,v,v], by
    change (∑ i : Fin 3, ![0,v,v] i) = 0
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      zero_add]
    funext j
    exact CharTwo.add_self_eq_zero (v j)⟩

private theorem translationAt_apply (v : Vector) (i : Fin 3) :
    (translationAt v).val i = if i = 0 then 0 else v := by
  fin_cases i <;> simp [translationAt]

private def commonEquiv : Vector ≃ common where
  toFun v := ⟨TrioAction.ambientTranslationEquiv (Multiplicative.ofAdd (translationAt v)),
    (translation_mem_common _).mpr (translationAt_apply v 0)⟩
  invFun a := (TrioAction.ambientTranslationEquiv.symm ⟨a,a.property.2⟩).toAdd.val 1
  left_inv v := by
    change (TrioAction.ambientTranslationEquiv.symm
      (TrioAction.ambientTranslationEquiv _)).toAdd.val 1 = v
    rw [MulEquiv.symm_apply_apply]
    exact translationAt_apply v 1
  right_inv a := by
    let t := TrioAction.ambientTranslationEquiv.symm ⟨a,a.property.2⟩
    have ht : (TrioAction.ambientTranslationEquiv t).val = a :=
      congrArg Subtype.val (TrioAction.ambientTranslationEquiv.apply_symm_apply _)
    have hz : t.toAdd.val 0 = 0 := (translation_mem_common t).mp (ht ▸ a.property)
    have he : translationAt (t.toAdd.val 1) = t.toAdd := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact (translationAt_apply _ 0).trans hz.symm
      · exact translationAt_apply _ 1
      · change (translationAt (t.toAdd.val 1)).val 2 = t.toAdd.val 2
        rw [translationAt_apply, TrioAction.translationSpace_last, hz, zero_add]
        rfl
    apply Subtype.ext
    change (TrioAction.ambientTranslationEquiv
      (Multiplicative.ofAdd (translationAt (t.toAdd.val 1)))).val = a
    rw [he]
    exact ht

/-- The intersection has order eight. -/
theorem common_card : Nat.card common = 8 := by
  rw [← Nat.card_congr commonEquiv]
  simp [QuotientConstruction.Vector, Nat.card_eq_fintype_card]

private theorem common_fixes_parts {b : M24} (hb : b ∈ common) (i : Fin 3) :
    b • standardTrioOctad i = standardTrioOctad i := by
  obtain ⟨k,hk,rfl⟩ := hb.2
  exact standardTwoCore_fixes_octad k hk i

private theorem common_transitive (i : Fin 3) (hi : i ≠ 0) (v w : Vector) :
    ∃ b : M24, b ∈ common ∧ b.val (point (i,v)) = point (i,w) := by
  let t := Multiplicative.ofAdd (translationAt (w-v))
  refine ⟨(TrioAction.ambientTranslationEquiv t).val,
    (translation_mem_common _).mpr (translationAt_apply _ 0), ?_⟩
  rw [ambientTranslation_point]
  change point (i,v + (translationAt (w-v)).val i) = _
  rw [translationAt_apply, if_neg hi, add_comm v, sub_add_cancel]

/-- The common eight determines the marked trio among partitions into octads.
Its two nontrivial orbits are the other two octads. -/
theorem normalizer_common_le_trio :
    octadStabilizer standardOctad ⊓ normalizer (common : Set M24) ≤
      trioStabilizer standardTrio := by
  rintro g ⟨hO,hN⟩
  apply (mem_trioStabilizer_iff standardTrio g).mpr
  intro A hA
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
  by_cases hi : i = 0
  · subst i
    have h := hO
    change g • standardOctad.val = standardOctad.val at h
    rw [standardOctad_eq] at h
    rw [h]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
  · obtain ⟨⟨j,w⟩,hw⟩ := point.surjective (g.val (point (i,0)))
    have he : g • standardTrioOctad i = standardTrioOctad j := by
      apply Finset.eq_of_subset_of_card_le ?_ (by
        rw [Finset.card_smul_finset]
        have hc : ∀ k : Fin 3, (standardTrioOctad k).card = 8 := by decide +kernel
        rw [hc,hc])
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_smul_finset.mp hx
      obtain ⟨⟨k,v⟩,rfl⟩ := point.surjective y
      have hk := (point_mem_octad_iff k i v).mp hy
      subst k
      obtain ⟨b,hb,he⟩ := common_transitive i hi 0 v
      have hc : g * b * g⁻¹ ∈ common := (mem_normalizer_iff.mp hN b).mp hb
      have hp := (MulAction.mem_stabilizer_finset'.mp
        (show g * b * g⁻¹ ∈ MulAction.stabilizer M24 (standardTrioOctad j) from
          common_fixes_parts hc j)) (point_mem_octad j w)
      change (g * b * g⁻¹).val (point (j,w)) ∈ _ at hp
      rw [hw] at hp
      change g.val (point (i,v)) ∈ _
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul,
        Equiv.Perm.coe_inv, Function.comp_apply, Equiv.symm_apply_apply, he] using hp
    rw [he]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

private theorem stabilizer_normalizes_core (H : Subgroup M24) :
    H ≤ normalizer (((pCore 2 H).map H.subtype : Subgroup M24) : Set M24) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨⟨g,hg⟩ * y * (⟨g,hg⟩ : H)⁻¹,
    (inferInstance : (pCore 2 H).Normal).conj_mem y hy ⟨g,hg⟩,rfl⟩

/-- The normalizer of the common eight in the octad group is precisely the
literal point–line intersection. -/
theorem normalizer_common :
    octadStabilizer standardOctad ⊓ normalizer (common : Set M24) =
      octadStabilizer standardOctad ⊓ trioStabilizer standardTrio := by
  apply le_antisymm
  · exact le_inf inf_le_left normalizer_common_le_trio
  · rintro g ⟨hO,hT⟩
    exact ⟨hO, inf_normalizer_le_normalizer_inf
      ⟨stabilizer_normalizes_core _ hO, stabilizer_normalizes_core _ hT⟩⟩

private theorem sextet_core_fixes_trio_parts {a : M24} (ha : a ∈ SextetCore.core)
    (i : Fin 3) : a • standardTrioOctad i = standardTrioOctad i := by
  have h : a ∈ SextetCore.partFixers := SextetCore.standardCandidate_le_partFixers
    (SextetCore.standardCandidate_eq_core.symm ▸ ha)
  have ht (j : Fin 6) : a • standardTetrad j = standardTetrad j :=
    mem_iInf.mp h j
  fin_cases i <;> simp only [standardTrioOctad, Finset.smul_finset_union, ht]

/-- Coordinates of the common eight in the natural octad module. -/
@[expose] def commonSubspace : Submodule (ZMod 2) Space where
  carrier := {v | ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v) :
    M24) ∈ TrioAction.core}
  zero_mem' := by
    change ((ambientCoordinates standardOctad).symm 1 : M24) ∈ TrioAction.core
    simp
  add_mem' := by
    intro v w hv hw
    change ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v *
      Multiplicative.ofAdd w) : M24) ∈ TrioAction.core
    simpa only [map_mul, Subgroup.coe_mul] using TrioAction.core.mul_mem hv hw
  smul_mem' := by
    intro c v hv
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · simpa only [one_smul] using hv

@[simp] theorem coordinates_mem_commonSubspace (a : AmbientCore standardOctad) :
    (ambientCoordinates standardOctad a).toAdd ∈ commonSubspace ↔
      (a : M24) ∈ TrioAction.core := by
  change ((ambientCoordinates standardOctad).symm (ambientCoordinates standardOctad a) :
    M24) ∈ TrioAction.core ↔ _
  rw [MulEquiv.symm_apply_apply]

private def commonSubspaceEquiv : commonSubspace ≃ common where
  toFun v := ⟨(ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v.val),
    ((ambientCoordinates standardOctad).symm _).property, v.property⟩
  invFun a := ⟨(ambientCoordinates standardOctad ⟨a,a.property.1⟩).toAdd,
    (coordinates_mem_commonSubspace _).mpr a.property.2⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((ambientCoordinates standardOctad).apply_symm_apply (Multiplicative.ofAdd v.val))
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun x : AmbientCore standardOctad => (x : M24))
      ((ambientCoordinates standardOctad).symm_apply_apply ⟨a,a.property.1⟩)

/-- The native common four lies in the native common eight, retaining the
same octad, sextet and trio. -/
theorem plane_common_le_common : NativePlane.commonSubspace ≤ commonSubspace := by
  intro v hv
  let a := (ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v)
  have hA : (a : M24) ∈ SextetCore.core := hv
  have hp (i : Fin 3) : (a : M24) • standardTrioOctad i = standardTrioOctad i :=
    sextet_core_fixes_trio_parts hA i
  have hT : (a : M24) ∈ trioStabilizer standardTrio := by
    apply (mem_trioStabilizer_iff _ _).mpr
    intro A hA
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    rw [hp]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  let g : trioStabilizer standardTrio := ⟨a,hT⟩
  have ho : ∀ x ∈ standardOctad.val, (a : M24).val x = x := by
    apply (mem_octadPointwiseKernel _ _).mp
    rw [← octad_core_map_eq_pointwise]
    exact a.property
  obtain ⟨t,ht⟩ := affineQuotient_spec affineCoverage g
  change HasAffineForm g (standardAffineHom g) t at ht
  have hperm : (standardAffineHom g).1 = 1 := by
    apply Equiv.ext
    intro i
    have hh := (MulAction.mem_stabilizer_finset'.mp
      (show (a : M24) ∈ MulAction.stabilizer M24 (standardTrioOctad i) from hp i))
      (point_mem_octad i 0)
    change g.val.val (point (i,0)) ∈ standardTrioOctad i at hh
    rw [ht] at hh
    exact (point_mem_octad_iff _ _ _).mp hh
  have hpoint (w : QuotientConstruction.Vector) :
      Matrix.SpecialLinearGroup.toLin' (standardAffineHom g).2 w + t 0 = w := by
    have hh := ho (point (0,w)) (standardOctad_eq ▸ point_mem_octad 0 w)
    change g.val.val (point (0,w)) = _ at hh
    rw [ht] at hh
    exact congrArg Prod.snd (point.injective hh)
  have ht0 : t 0 = 0 := by simpa using hpoint 0
  have hlin : (standardAffineHom g).2 = 1 := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    ext w j
    have hh := hpoint w
    rw [ht0,add_zero] at hh
    simpa only [map_one, LinearEquiv.coe_one, id_eq] using congrFun hh j
  have hg : g ∈ pCore 2 (trioStabilizer standardTrio) := by
    rw [← standardAffineHom_ker]
    exact Prod.ext hperm hlin
  exact ⟨g,hg,rfl⟩

/-- The common eight is a hyperplane in the natural four-space. -/
theorem commonSubspace_finrank : Module.finrank (ZMod 2) commonSubspace = 3 := by
  have hc := (Nat.card_congr commonSubspaceEquiv).trans common_card
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc.trans (by decide : 8 = 2 ^ 3))

/-- The literal point–line group is the preimage of the common-eight parabolic. -/
theorem line_parabolic_comap :
    (BinaryLinear.parabolic commonSubspace).comap (linearAction standardOctad) =
      (trioStabilizer standardTrio).subgroupOf (Stabilizer standardOctad) := by
  ext g
  have hn : g.val ∈ normalizer (common : Set M24) ↔ g.val ∈ trioStabilizer standardTrio := by
    have he := congrArg (fun H : Subgroup M24 => g.val ∈ H) normalizer_common
    simpa only [mem_inf, g.property, true_and] using (Iff.of_eq he)
  change linearAction standardOctad g ∈ BinaryLinear.parabolic commonSubspace ↔
    g.val ∈ trioStabilizer standardTrio
  rw [← hn]
  change (∀ v : Space, linearAction standardOctad g v ∈ commonSubspace ↔
    v ∈ commonSubspace) ↔ _
  constructor
  · intro h
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · rintro ⟨haO,haT⟩
      let a' : AmbientCore standardOctad := ⟨a,haO⟩
      let v := (ambientCoordinates standardOctad a').toAdd
      have hv : v ∈ commonSubspace := (coordinates_mem_commonSubspace a').mpr haT
      have hh := (h v).mpr hv
      change ((ambientCoordinates standardOctad).symm
        (Multiplicative.ofAdd (linearAction standardOctad g v)) : M24) ∈ TrioAction.core at hh
      have hc := ambientCoordinates_conjugation standardOctad g v
      rw [naturalAction_quotientEquiv] at hc
      have ha : ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v) : M24) = a :=
        congrArg Subtype.val ((ambientCoordinates standardOctad).symm_apply_apply a')
      rw [← hc,ha] at hh
      exact ⟨(mem_normalizer_iff.mp (stabilizer_normalizes_core _ g.property) a).mp haO,hh⟩
    · intro ha
      have haO := (mem_normalizer_iff.mp (stabilizer_normalizes_core _ g.property) a).mpr ha.1
      let a' : AmbientCore standardOctad := ⟨a,haO⟩
      let v := (ambientCoordinates standardOctad a').toAdd
      have hc := ambientCoordinates_conjugation standardOctad g v
      rw [naturalAction_quotientEquiv] at hc
      have he : ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v) : M24) = a :=
        congrArg Subtype.val ((ambientCoordinates standardOctad).symm_apply_apply a')
      have hv : linearAction standardOctad g v ∈ commonSubspace := by
        change ((ambientCoordinates standardOctad).symm
          (Multiplicative.ofAdd (linearAction standardOctad g v)) : M24) ∈ TrioAction.core
        rw [← hc,he]
        exact ha.2
      exact ⟨haO,(coordinates_mem_commonSubspace a').mp ((h v).mp hv)⟩
  · intro h v
    have hc := ambientCoordinates_conjugation standardOctad g v
    rw [naturalAction_quotientEquiv] at hc
    change ((ambientCoordinates standardOctad).symm
      (Multiplicative.ofAdd (linearAction standardOctad g v)) : M24) ∈ TrioAction.core ↔
        ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v) : M24) ∈ TrioAction.core
    rw [← hc]
    have hh := (mem_normalizer_iff.mp h
      ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v))).symm
    have hO := ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v)).property
    have hO' := (mem_normalizer_iff.mp (stabilizer_normalizes_core _ g.property) _).mp hO
    simpa only [common, mem_inf, hO, hO', true_and] using hh

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativeLine
