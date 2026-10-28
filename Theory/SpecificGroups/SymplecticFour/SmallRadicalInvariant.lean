module
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics.Exact
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# Small invariant sets for symplectic two-radicals

A nontrivial affine orbit contains a full field's worth of nonzero vectors.
It cannot fit in a set of at most q vectors containing zero. The point and
plane radicals have affine matrix families through each element; together
they generate the standard Sylow. Radical classification and actual
symplectic conjugation give the assertion for every nontrivial two-radical.
No closure under field scalars is assumed of the invariant set.

Source: MS93 (3.7), printed p.872, the small-normal-factor contradiction.
The original marked-star application is in NonbinarySymplectic.OriginalStar.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SmallRadicalInvariant
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem affine_fixes (W : Set (Vector F)) (h0 : 0 ∈ W)
    (hc : Nat.card W ≤ Nat.card F) (g : F → Sp F) (v : Vector F)
    (hm : ∀ t, g t • v ∈ W)
    (he : ∀ t, g t • v = v+t • (g 1 • v-v)) : g 1 • v=v := by
  by_contra hn
  have hd : g 1 • v-v ≠ 0 := sub_ne_zero.mpr hn
  let f : F → W := fun t => ⟨g t • v,hm t⟩
  have hi : Function.Injective f := by
    intro t s h
    have hh := congrArg Subtype.val h
    change g t • v=g s • v at hh
    rw [he t,he s,add_right_inj] at hh
    exact (smul_left_injective F hd) hh
  obtain ⟨t,ht⟩ := (hi.bijective_of_nat_card_le hc).surjective ⟨0,h0⟩
  have hv : v=0 := by
    have hh : g t • v=0 := congrArg Subtype.val ht
    exact (smul_eq_zero_iff_eq (g t)).mp hh
  simp [hv] at hn

theorem point_fixes (W : Set (Vector F)) (h0 : 0 ∈ W)
    (hc : Nat.card W ≤ Nat.card F)
    (hn : ∀ g ∈ pointRadicalAmbient (F := F), ∀ v ∈ W, g • v ∈ W) :
    ∀ g ∈ pointRadicalAmbient (F := F), ∀ v ∈ W, g • v=v := by
  rintro g ⟨a,ha,rfl⟩ v hv
  change (a : Sp F) • v=v
  rw [pointRadical_eq_element a ha]
  generalize a.val.val (.inl 1) (.inr 0)=u
  generalize a.val.val (.inr 1) (.inr 0)=w
  generalize a.val.val (.inl 0) (.inr 0)=z
  let g : F → Sp F := fun t => (pointRadicalElement (t*u) (t*w) (t*z)).val
  have hg := affine_fixes W h0 hc g v
    (fun t => hn _ (mem_map_of_mem _ (pointRadicalElement_mem _ _ _)) v hv) (by
      intro t
      ext i
      fin_cases i <;>
        simp [g,smul_eq_mulVec,pointRadicalElement,pointRadicalMatrix,mulVec,dotProduct,
          Fintype.sum_sum_type,Fin.sum_univ_two] <;> ring)
  simpa only [g,one_mul] using hg

omit [CharP F 2] in
theorem plane_fixes (W : Set (Vector F)) (h0 : 0 ∈ W)
    (hc : Nat.card W ≤ Nat.card F)
    (hn : ∀ g ∈ planeRadicalAmbient (F := F), ∀ v ∈ W, g • v ∈ W) :
    ∀ g ∈ planeRadicalAmbient (F := F), ∀ v ∈ W, g • v=v := by
  rintro g ⟨a,ha,rfl⟩ v hv
  change (a : Sp F) • v=v
  let B := (Plane.radicalEquiv ⟨a,ha⟩).toAdd
  have he : (Plane.shear B).val=a.val :=
    congrArg Subtype.val (congrArg Subtype.val (Plane.radicalEquiv.symm_apply_apply ⟨a,ha⟩))
  rw [←he]
  let g : F → Sp F := fun t => (Plane.shear (t • B)).val
  have hg := affine_fixes W h0 hc g v
    (fun t => hn _ (mem_map_of_mem _ (show Plane.shear (t • B) ∈ Plane.radical from
      Plane.quotientMap_shear _)) v hv) (by
      intro t
      ext i
      fin_cases i <;>
        simp [g,smul_eq_mulVec,Plane.shear,Plane.shearSp,mulVec,dotProduct,
          Fintype.sum_sum_type,Fin.sum_univ_two] <;> ring)
  simpa only [g,one_smul] using hg

theorem unipotent_fixes (W : Set (Vector F)) (h0 : 0 ∈ W)
    (hc : Nat.card W ≤ Nat.card F)
    (hn : ∀ g ∈ unipotent (F := F), ∀ v ∈ W, g • v ∈ W) :
    ∀ g ∈ unipotent (F := F), ∀ v ∈ W, g • v=v := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hP : pointRadicalAmbient (F := F) ≤ unipotent := by
    change SymplecticConjugatePair.pointRadical ≤ unipotent
    rw [SymplecticConjugatePair.pointRadical_eq_wing]
    exact map_subtype_le _
  have hQ : planeRadicalAmbient (F := F) ≤ unipotent := by
    change SymplecticConjugatePair.planeRadical ≤ unipotent
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    exact map_subtype_le _
  have hgen : pointRadicalAmbient (F := F) ⊔ planeRadicalAmbient=unipotent := by
    change SymplecticConjugatePair.pointRadical ⊔ SymplecticConjugatePair.planeRadical=unipotent
    rw [SymplecticConjugatePair.pointRadical_eq_wing,
      SymplecticConjugatePair.planeRadical_eq_wing,←Subgroup.map_sup,
      CentralRootGeometry.wings_generate,←MonoidHom.range_eq_map,range_subtype]
  have hfix : unipotent (F := F) ≤ fixingSubgroup (Sp F) W := by
    rw [←hgen]
    exact sup_le (fun x hx => (mem_fixingSubgroup_iff _).mpr
      (point_fixes W h0 hc (fun y hy => hn y (hP hy)) x hx))
      (fun x hx => (mem_fixingSubgroup_iff _).mpr
        (plane_fixes W h0 hc (fun y hy => hn y (hQ hy)) x hx))
  exact fun x hx => (mem_fixingSubgroup_iff _).mp (hfix hx)

omit [Finite F] [CharP F 2] in
private theorem conjugate_fixes (A B : Subgroup (Sp F)) (g : Sp F)
    (he : A.map (MulAut.conj g).toMonoidHom=B)
    (hB : ∀ W : Set (Vector F), 0 ∈ W → Nat.card W ≤ Nat.card F →
      (∀ b ∈ B, ∀ v ∈ W, b • v ∈ W) → ∀ b ∈ B, ∀ v ∈ W, b • v=v)
    (W : Set (Vector F)) (h0 : 0 ∈ W) (hc : Nat.card W ≤ Nat.card F)
    (hn : ∀ a ∈ A, ∀ v ∈ W, a • v ∈ W) :
    ∀ a ∈ A, ∀ v ∈ W, a • v=v := by
  let W' := (fun v : Vector F => g • v) '' W
  have h0' : 0 ∈ W' := ⟨0,h0,smul_zero g⟩
  have hc' : Nat.card W' ≤ Nat.card F := by
    rw [←Nat.card_congr (Equiv.Set.image (fun v : Vector F => g • v) W
      (MulAction.injective g))]
    exact hc
  have hn' : ∀ b ∈ B, ∀ v ∈ W', b • v ∈ W' := by
    rintro b hb v ⟨w,hw,rfl⟩
    obtain ⟨a,ha,rfl⟩ := he.symm ▸ hb
    refine ⟨a • w,hn a ha w hw,?_⟩
    simp [MulAut.conj_apply,mul_smul]
  intro a ha v hv
  have hh := hB W' h0' hc' hn' _ (he ▸ mem_map_of_mem _ ha) _ ⟨v,hv,rfl⟩
  change (g*a*g⁻¹) • (g • v)=g • v at hh
  apply MulAction.injective g
  simpa only [MulAut.conj_apply,mul_smul,inv_smul_smul] using hh

/-- A two-radical of Sp4 fixes every invariant set of at most q vectors
that contains zero. The set need not be closed under field scalars. -/
theorem radical_fixes (A : Subgroup (Sp F)) (hA : A.IsPRadical 2)
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (W : Set (Vector F)) (h0 : 0 ∈ W) (hc : Nat.card W ≤ Nat.card F)
    (hW : ∀ a ∈ A, ∀ v ∈ W, a • v ∈ W) :
    ∀ a ∈ A, ∀ v ∈ W, a • v=v := by
  rcases radical_normalizer_parabolic_or_sylow A hA hF (by omega) with ⟨g,hg⟩ | ⟨S,hS⟩
  · have hm := map_pCoreIn_of_injective 2 (normalizer (A : Set (Sp F)))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hcore : (normalizer (A : Set (Sp F))).pCoreIn 2=A := hA.2
    rw [hcore] at hm
    rcases hg with hg | hg
    · rw [hg] at hm
      exact conjugate_fixes A pointRadicalAmbient g
        (hm.trans (pointParabolic_core_map_eq_radical hF hn)) point_fixes W h0 hc hW
    · rw [hg] at hm
      exact conjugate_fixes A planeRadicalAmbient g
        (hm.trans (planeParabolic_core_map_eq_radical hF hn)) plane_fixes W h0 hc hW
  · obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF (by omega))
    have he : A.map (MulAut.conj g).toMonoidHom=unipotent := by
      rw [←hS]
      exact congrArg Sylow.toSubgroup hg
    exact conjugate_fixes A unipotent g he unipotent_fixes W h0 hc hW

end Theory.SpecificGroups.SymplecticFour.SmallRadicalInvariant
