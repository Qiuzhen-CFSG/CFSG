module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Flags
public import Mathlib.GroupTheory.Index

/-!
# Intrinsic descriptions of rank-three residues

At a vertex of type `i`, the vertices of type `j` in its residue are the
cosets of `F i ⊓ F j` in `F i`.  This file records the resulting equivariant
identification and the elementary consequences for kernels and cardinalities.
Incidence reflection uses the common representative for three vertices supplied
by the middle product condition; cardinalities are transported from the base
residue and require no ambient finiteness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.5.3(3–5) and I.5.4(3), printed pp. 419–420.
-/

@[expose] public section
namespace Subgroup.CosetGeometry
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The two types different from `i`. -/
abbrev otherType (i : Fin 3) := {j : Fin 3 // j ≠ i}

/-- The subgroup of `F i` fixing a vertex of type `j` in the base residue. -/
def intrinsicPair (F : Fin 3 → Subgroup G) (i : Fin 3) (j : otherType i) :
    Subgroup (F i) := (F j.1).subgroupOf (F i)

/-- The intrinsic rank-two family at the base vertex of type `i`. -/
abbrev intrinsicFamily (F : Fin 3 → Subgroup G) (i : Fin 3) :
    otherType i → Subgroup (F i) := intrinsicPair F i

/-- The common subgroup of all intrinsic residue types. -/
def intrinsicIntersection (F : Fin 3 → Subgroup G) (i : Fin 3) :
    Subgroup (F i) := ⨅ j : otherType i, intrinsicPair F i j

theorem intrinsicIntersection_eq (F : Fin 3 → Subgroup G) (i : Fin 3) :
    intrinsicIntersection F i = (⨅ j : Fin 3, F j).subgroupOf (F i) := by
  ext x
  simp only [intrinsicIntersection, Subgroup.mem_iInf, Subgroup.mem_subgroupOf,
    intrinsicPair]
  constructor
  · intro h j
    by_cases hj : j = i
    · rw [hj]
      exact x.property
    · let k : otherType i := ⟨j, hj⟩
      exact h k
  · intro h j
    exact h j.1

lemma intrinsicPair_mem_iff (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) (a : F i) :
    a ∈ intrinsicPair F i j ↔ (a : G) ∈ F j.1 := Iff.rfl

def intrinsicCosetMap (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) :
    (F i ⧸ intrinsicPair F i j) → G ⧸ F j.1 :=
  Quotient.lift (fun a : F i => ((a : G) : G ⧸ F j.1)) (by
    intro a b hab
    apply QuotientGroup.eq.mpr
    have hab' := QuotientGroup.eq.mp (Quotient.sound hab)
    have hm : ((a⁻¹ * b : F i) : G) ∈ F j.1 :=
      (intrinsicPair_mem_iff F i j (a⁻¹ * b)).mp hab'
    change ((a : G)⁻¹ * (b : G)) ∈ F j.1 at hm
    exact hm)

lemma intrinsicCosetMap_mk (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) (a : F i) :
    intrinsicCosetMap F i j (a : F i ⧸ intrinsicPair F i j) =
      ((a : G) : G ⧸ F j.1) := by
  simp [intrinsicCosetMap]

lemma intrinsicCosetMap_surjective (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) (q : G ⧸ F j.1)
    (hq : ∃ a : F i, ((a : G) : G ⧸ F j.1) = q) :
    ∃ x : F i ⧸ intrinsicPair F i j, intrinsicCosetMap F i j x = q := by
  obtain ⟨a, rfl⟩ := hq
  exact ⟨a, rfl⟩

lemma residue_base_rep (F : Fin 3 → Subgroup G) (i : Fin 3)
    (v : Residue F (base F i)) :
    ∃ a : F i, ((a : G) : G ⧸ F v.val.type) = v.val.coset := by
  obtain ⟨g, hg, hq⟩ := (incident_base_iff F i v.val).mp v.property.2
  exact ⟨⟨g, hg⟩, hq⟩

/-- The map from intrinsic typed cosets to the base residue. -/
noncomputable def residueIntrinsicMap (F : Fin 3 → Subgroup G) (i : Fin 3) :
    Vertex (intrinsicFamily F i) → Residue F (base F i) := fun v => by
  let j : otherType i := v.type
  refine ⟨⟨v.type.1, intrinsicCosetMap F i j v.coset⟩, ?_⟩
  refine ⟨v.type.2, ?_⟩
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective v.coset
  apply (incident_base_iff F i _).mpr
  refine ⟨(a : G), a.property, ?_⟩
  exact (intrinsicCosetMap_mk F i j a).trans
    (congrArg (intrinsicCosetMap F i j) ha)

private lemma residueIntrinsicMap_type (F : Fin 3 → Subgroup G) (i : Fin 3)
    (v : Vertex (intrinsicFamily F i)) :
    (residueIntrinsicMap F i v).val.type = v.type.1 := rfl

noncomputable def residueIntrinsicInv (F : Fin 3 → Subgroup G) (i : Fin 3) :
    Residue F (base F i) → Vertex (intrinsicFamily F i) := fun v =>
  let j : otherType i := ⟨v.val.type, v.property.1⟩
  let a : F i := Classical.choose (residue_base_rep F i v)
  ⟨j, (a : F i ⧸ intrinsicPair F i j)⟩

lemma residueIntrinsicInv_map (F : Fin 3 → Subgroup G) (i : Fin 3)
    (v : Residue F (base F i)) :
    residueIntrinsicMap F i (residueIntrinsicInv F i v) = v := by
  classical
  let j : otherType i := ⟨v.val.type, v.property.1⟩
  let a : F i := Classical.choose (residue_base_rep F i v)
  have hav : ((a : G) : G ⧸ F v.val.type) = v.val.coset :=
    Classical.choose_spec (residue_base_rep F i v)
  apply Subtype.ext
  change (⟨v.val.type, _⟩ : Vertex F) = ⟨v.val.type, _⟩
  congr 1

lemma residueIntrinsicMap_inv (F : Fin 3 → Subgroup G) (i : Fin 3)
    (v : Vertex (intrinsicFamily F i)) :
    residueIntrinsicInv F i (residueIntrinsicMap F i v) = v := by
  classical
  let j : otherType i := v.type
  obtain ⟨a₀, ha₀⟩ := QuotientGroup.mk_surjective v.coset
  let r : Residue F (base F i) := residueIntrinsicMap F i v
  let a₁ : F i := Classical.choose (residue_base_rep F i r)
  have ha₁ := Classical.choose_spec (residue_base_rep F i r)
  have hmap : intrinsicCosetMap F i j (a₀ : F i ⧸ intrinsicPair F i j) =
      intrinsicCosetMap F i j v.coset := congrArg (intrinsicCosetMap F i j) ha₀
  have hamb : ((a₁ : G) : G ⧸ F j.1) = ((a₀ : G) : G ⧸ F j.1) := by
    exact ha₁.trans hmap.symm
  change (⟨j, (a₁ : F i ⧸ intrinsicPair F i j)⟩ : Vertex (intrinsicFamily F i)) = v
  apply congrArg (fun q => (⟨j, q⟩ : Vertex (intrinsicFamily F i)))
  rw [← ha₀]
  apply QuotientGroup.eq.mpr
  exact (intrinsicPair_mem_iff F i j _).mpr (QuotientGroup.eq.mp hamb)

/-- Equivariant identification of the intrinsic typed cosets with the residue. -/
noncomputable def residueIntrinsicEquiv (F : Fin 3 → Subgroup G) (i : Fin 3) :
    Vertex (intrinsicFamily F i) ≃ Residue F (base F i) :=
  { toFun := residueIntrinsicMap F i
    invFun := residueIntrinsicInv F i
    left_inv := residueIntrinsicMap_inv F i
    right_inv := residueIntrinsicInv_map F i }

@[simp] theorem residueIntrinsicEquiv_type (F : Fin 3 → Subgroup G) (i : Fin 3)
    (v : Vertex (intrinsicFamily F i)) :
    (residueIntrinsicEquiv F i v).val.type = v.type.1 :=
  rfl

/-- The kernel of the intrinsic action on the two typed parts of a residue. -/
theorem intrinsic_action_kernel (F : Fin 3 → Subgroup G) (i : Fin 3) :
    (MulAction.toPermHom (F i) (Vertex (intrinsicFamily F i))).ker =
      (⨅ j, intrinsicPair F i j).normalCore :=
  action_kernel (intrinsicFamily F i)

/-- The residue identification intertwines the canonical `F i` actions. -/
theorem residueIntrinsicEquiv_smul (F : Fin 3 → Subgroup G) (i : Fin 3)
    (a : F i) (v : Vertex (intrinsicFamily F i)) :
    (residueIntrinsicMap F i (a • v)).val =
      (a : G) • (residueIntrinsicMap F i v).val := by
  change Vertex.mk _ _ = Vertex.mk _ _
  congr 1
  change intrinsicCosetMap F i v.type (a • v.coset) =
    (a : G) • intrinsicCosetMap F i v.type v.coset
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective v.coset
  rw [← hb]
  change (((a * b : F i) : G) : G ⧸ F v.type.1) =
    (a : G) • (((b : F i) : G) : G ⧸ F v.type.1)
  rw [MulAction.Quotient.smul_mk]
  change (((a : G) * (b : G) : G) : G ⧸ F v.type.1) = _
  rfl

/-- The vertices of one intrinsic type are exactly one quotient of `F i`. -/
noncomputable def intrinsicTypeEquiv (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) :
    {v : Vertex (intrinsicFamily F i) // v.type = j} ≃
      F i ⧸ intrinsicPair F i j :=
  { toFun := fun v => v.property ▸ v.1.coset
    invFun := fun q => ⟨⟨j, q⟩, rfl⟩
    left_inv := by
      intro v
      apply Subtype.ext
      change (⟨j, _⟩ : Vertex (intrinsicFamily F i)) = v.1
      cases v with
      | mk v hv =>
        cases v with
        | mk t q =>
          simp at hv
          subst t
          rfl
    right_inv := by intro q; rfl }

theorem intrinsicType_card (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) :
    Nat.card {v : Vertex (intrinsicFamily F i) // v.type = j} =
      Nat.card (F i ⧸ intrinsicPair F i j) :=
  Nat.card_congr (intrinsicTypeEquiv F i j)

theorem residueType_card (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) :
    Nat.card {v : Residue F (base F i) // v.val.type = j.1} =
      Nat.card (F i ⧸ intrinsicPair F i j) := by
  let e : {v : Vertex (intrinsicFamily F i) // v.type = j} ≃
      {v : Residue F (base F i) // v.val.type = j.1} :=
    Equiv.subtypeEquiv (residueIntrinsicEquiv F i) (fun v => by
      rw [residueIntrinsicEquiv_type]
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h)
  rw [← Nat.card_congr e]
  exact intrinsicType_card F i j


/-- The vertex group acts on its base residue by ambient left translation. -/
instance baseResidueMulAction (F : Fin 3 → Subgroup G) (i : Fin 3) :
    MulAction (F i) (Residue F (base F i)) where
  smul a v := ⟨(a : G) • v.val, v.property.1, by
    have hfix : (a : G) • base F i = base F i := by
      have : (a : G) ∈ MulAction.stabilizer G (base F i) := by
        rw [stabilizer_base]
        exact a.property
      exact this
    simpa only [hfix] using v.property.2.smul F (a : G)⟩
  one_smul v := Subtype.ext (one_smul G v.val)
  mul_smul a b v := Subtype.ext (mul_smul (a : G) (b : G) v.val)

@[simp] theorem baseResidue_smul_val (F : Fin 3 → Subgroup G) (i : Fin 3)
    (a : F i) (v : Residue F (base F i)) :
    (a • v).val = (a : G) • v.val := rfl

theorem residueIntrinsicEquiv_equivariant (F : Fin 3 → Subgroup G) (i : Fin 3)
    (a : F i) (v : Vertex (intrinsicFamily F i)) :
    residueIntrinsicEquiv F i (a • v) = a • residueIntrinsicEquiv F i v :=
  Subtype.ext (residueIntrinsicEquiv_smul F i a v)

/-- The kernel on the actual residue equals the kernel on intrinsic cosets. -/
theorem residue_action_kernel (F : Fin 3 → Subgroup G) (i : Fin 3) :
    (MulAction.toPermHom (F i) (Residue F (base F i))).ker =
      (intrinsicIntersection F i).normalCore := by
  rw [intrinsicIntersection, ← intrinsic_action_kernel]
  ext a
  simp only [MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  change (∀ v : Residue F (base F i), a • v = v) ↔
    ∀ v : Vertex (intrinsicFamily F i), a • v = v
  constructor
  · intro h v
    apply (residueIntrinsicEquiv F i).injective
    rw [residueIntrinsicEquiv_equivariant, h]
  · intro h v
    obtain ⟨w, rfl⟩ := (residueIntrinsicEquiv F i).surjective v
    rw [← residueIntrinsicEquiv_equivariant, h]

/-- The kernel is the normal core of the full chamber subgroup inside `F i`. -/
theorem residue_action_kernel_chamber (F : Fin 3 → Subgroup G) (i : Fin 3) :
    (MulAction.toPermHom (F i) (Residue F (base F i))).ker =
      ((⨅ j, F j).subgroupOf (F i)).normalCore := by
  rw [residue_action_kernel, intrinsicIntersection_eq]

lemma intrinsicCosetMap_injective (F : Fin 3 → Subgroup G) (i : Fin 3)
    (j : otherType i) : Function.Injective (intrinsicCosetMap F i j) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  apply QuotientGroup.eq.mpr
  exact (intrinsicPair_mem_iff F i j _).mpr (QuotientGroup.eq.mp h)

/-- Under the middle product hypothesis the equivalence preserves and reflects incidence. -/
theorem residueIntrinsicEquiv_incident_iff (F : Fin 3 → Subgroup G) (i : Fin 3)
    (hprod : MiddleProduct F) (u v : Vertex (intrinsicFamily F i)) :
    Incident F (residueIntrinsicEquiv F i u).val (residueIntrinsicEquiv F i v).val ↔
      Incident (intrinsicFamily F i) u v := by
  constructor
  · intro h
    obtain ⟨g, hg, hu, hv⟩ := common_representative_three F hprod
      (residueIntrinsicEquiv F i u).property.2
      (residueIntrinsicEquiv F i v).property.2 h
    have hgi : g ∈ F i := by
      change (g : G ⧸ F i) = ((1 : G) : G ⧸ F i) at hg
      simpa only [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff] using hg
    refine ⟨⟨g, hgi⟩, ?_, ?_⟩
    · apply intrinsicCosetMap_injective F i u.type
      exact hu
    · apply intrinsicCosetMap_injective F i v.type
      exact hv
  · rintro ⟨g, hu, hv⟩
    exact ⟨(g : G), congrArg (intrinsicCosetMap F i u.type) hu,
      congrArg (intrinsicCosetMap F i v.type) hv⟩

/-- Translation identifies residues and preserves the vertex type. -/
def localResidueTranslate (F : Fin 3 → Subgroup G) (g : G) (b : Vertex F) :
    Residue F b ≃ Residue F (g • b) where
  toFun v := ⟨g • v.val, v.property.1, v.property.2.smul F g⟩
  invFun v := ⟨g⁻¹ • v.val, v.property.1, by
    simpa only [inv_smul_smul] using v.property.2.smul F g⁻¹⟩
  left_inv v := Subtype.ext (inv_smul_smul g v.val)
  right_inv v := Subtype.ext (smul_inv_smul g v.val)

theorem residueType_card_translate (F : Fin 3 → Subgroup G) (g : G)
    (b : Vertex F) (j : Fin 3) :
    Nat.card {v : Residue F (g • b) // v.val.type = j} =
      Nat.card {v : Residue F b // v.val.type = j} :=
  (Nat.card_congr (Equiv.subtypeEquiv (localResidueTranslate F g b)
    (fun _ => Iff.rfl))).symm

/-- Local type cardinalities are intrinsic indices, at any vertex. -/
theorem residueType_card_index (F : Fin 3 → Subgroup G) (b : Vertex F)
    (j : Fin 3) (hj : j ≠ b.type) :
    Nat.card {v : Residue F b // v.val.type = j} =
      ((F j).subgroupOf (F b.type)).index := by
  obtain ⟨g, hg⟩ := exists_smul_base F b
  have hc := residueType_card_translate F g (base F b.type) j
  rw [hg] at hc
  rw [hc]
  exact (residueType_card F b.type ⟨j, hj⟩).trans
    (Subgroup.index_eq_card _).symm

/-- Both typed parts of a line residue have the respective local indices. -/
theorem line_residue_card (F : Fin 3 → Subgroup G) (l : G ⧸ F 1) :
    Nat.card {v : Residue F ⟨1, l⟩ // v.val.type = 0} =
      ((F 0).subgroupOf (F 1)).index ∧
    Nat.card {v : Residue F ⟨1, l⟩ // v.val.type = 2} =
      ((F 2).subgroupOf (F 1)).index :=
  ⟨residueType_card_index F ⟨1, l⟩ 0 (by change (0 : Fin 3) ≠ 1; decide),
    residueType_card_index F ⟨1, l⟩ 2 (by change (2 : Fin 3) ≠ 1; decide)⟩

/-- Index three at both endpoints gives a complete three-by-three line residue. -/
theorem line_residue_three_by_three (F : Fin 3 → Subgroup G)
    (hprod : MiddleProduct F)
    (h0 : ((F 0).subgroupOf (F 1)).index = 3)
    (h2 : ((F 2).subgroupOf (F 1)).index = 3) (l : G ⧸ F 1) :
    Nat.card {v : Residue F ⟨1, l⟩ // v.val.type = 0} = 3 ∧
    Nat.card {v : Residue F ⟨1, l⟩ // v.val.type = 2} = 3 ∧
    ∀ u v : Residue F ⟨1, l⟩, u.val.type ≠ v.val.type → Incident F u.val v.val :=
  ⟨(line_residue_card F l).1.trans h0, (line_residue_card F l).2.trans h2,
    line_residue_complete F hprod l⟩

end Subgroup.CosetGeometry
