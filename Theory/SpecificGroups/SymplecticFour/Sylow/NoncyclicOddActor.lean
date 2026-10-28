module
public import Theory.SpecificGroups.SymplecticFour.FullTorusNormalizer
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerDerived
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# The unipotent core forced by a noncyclic odd actor

A noncyclic subgroup of the split rank-two torus moves each positive root:
the kernel of every root character is cyclic. Scalar commutators therefore
put all four positive root groups inside any subgroup that contains the actor
and is normalized by the unipotent Sylow. Borel conjugacy aligns arbitrary
odd-primary actors, and solvable Sylow control places the original subgroup
in the Borel. Its actual two-core is consequently the specified Sylow.

The resulting normalizer commutator bound is the inner-action calculation
used in Aschbacher–Smith, 13.1.12(3), printed p.874. The source application is
in Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.
CharacteristicTwo.Symplectic; no unipotent marking is assumed there.
-/

public noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.NoncyclicOddActor
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def rootIndex (i : Fin 4) : Fin 8 := ⟨2*i.val, by omega⟩
private def rootWeight (i : Fin 4) (a : Fˣ × Fˣ) : Fˣ :=
  ![a.1^2, a.2^2, a.1*a.2, a.1/a.2] i

omit [Finite F] in
private theorem square_eq_one {a : Fˣ} (ha : a^2 = 1) : a = 1 := by
  apply Units.ext
  apply CharTwo.sq_injective
  simpa using congrArg Units.val ha

private theorem weight_moves (B : Subgroup (Fˣ × Fˣ)) (hnc : ¬ IsCyclic B)
    (i : Fin 4) : ∃ a ∈ B, rootWeight i a ≠ 1 := by
  by_contra! h
  have hfirst (he : ∀ a : B, a.val.1 = 1) : False := by
    apply hnc
    apply isCyclic_of_injective ((MonoidHom.snd Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    exact Prod.ext ((he a).trans (he b).symm) hab
  have hsecond (he : ∀ a : B, a.val.2 = 1) : False := by
    apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    exact Prod.ext hab ((he a).trans (he b).symm)
  fin_cases i
  · exact hfirst (fun a => square_eq_one (h a a.property))
  · exact hsecond (fun a => square_eq_one (h a a.property))
  · apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    have ha : a.val.1 * a.val.2 = 1 := h a a.property
    have hb : b.val.1 * b.val.2 = 1 := h b b.property
    exact mul_left_cancel ((congrArg (fun t => t*a.val.2) hab).symm.trans (ha.trans hb.symm))
  · apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    have ha : a.val.1 = a.val.2 := div_eq_one.mp (h a a.property)
    have hb : b.val.1 = b.val.2 := div_eq_one.mp (h b b.property)
    exact ha.symm.trans (hab.trans hb)

omit [Finite F] [CharP F 2] in
private theorem diagonal_conjugate (i : Fin 4) (a : Fˣ × Fˣ) (t : F) :
    CentralRootGeometry.diagonalTorusHom a * rootElement (rootIndex i) t *
      (CentralRootGeometry.diagonalTorusHom a)⁻¹ =
        rootElement (rootIndex i) ((rootWeight i a : F) * t) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  ext j k
  change ((diagonalTorus a.1 a.2).val * (rootElement (rootIndex i) t).val) j k =
    ((rootElement (rootIndex i) ((rootWeight i a : F) * t)).val *
      (diagonalTorus a.1 a.2).val) j k
  fin_cases i <;>
    simp only [rootIndex, diagonalTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  all_goals dsimp [rootElement, rootMatrix, rootWeight]
  all_goals rcases j with j | j <;> rcases k with k | k <;>
    fin_cases j <;> fin_cases k <;>
    simp [Matrix.fromBlocks, Matrix.single, pow_two, mul_assoc, mul_comm, div_eq_mul_inv]
  all_goals first | (left; field_simp) | field_simp

omit [Finite F] [CharP F 2] in
private theorem scalar_root_le (X : Subgroup (Sp F)) (i : Fin 4)
    (hn : unipotent (F := F) ≤ normalizer (X : Set (Sp F)))
    (a : Fˣ × Fˣ) (ha : CentralRootGeometry.diagonalTorusHom a ∈ X)
    (hw : rootWeight i a ≠ 1) : RootSubgroup.group (F := F) (rootIndex i) ≤ X := by
  rintro x hx
  obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hx
  let c : F := rootWeight i a
  have hc : c ≠ 1 := fun h => hw (Units.ext h)
  let v := t / (c-1)
  have hU : rootElement (rootIndex i) v ∈ unipotent (F := F) := by
    apply positive_root_mem_unipotent
    fin_cases i <;> simp [rootIndex]
  have hh := (mem_normalizer_iff.mp (hn hU)
    (CentralRootGeometry.diagonalTorusHom a)⁻¹).mp (X.inv_mem ha)
  have hmem := X.mul_mem ha hh
  have he : CentralRootGeometry.diagonalTorusHom a *
      (rootElement (rootIndex i) v * (CentralRootGeometry.diagonalTorusHom a)⁻¹ *
        (rootElement (rootIndex i) v)⁻¹) = rootElement (rootIndex i) t := by
    rw [← mul_assoc, ← mul_assoc, diagonal_conjugate]
    have hinv : (rootElement (rootIndex i) v)⁻¹ = rootElement (rootIndex i) (-v) := by
      apply inv_eq_of_mul_eq_one_right
      rw [RootSubgroup.element_add, add_neg_cancel, RootSubgroup.element_zero]
    rw [hinv, RootSubgroup.element_add]
    congr 1
    change c*v + -v = t
    dsimp [v]
    field_simp [sub_ne_zero.mpr hc]
    ring
  rwa [he] at hmem

/-- Noncyclic torus actors force all four positive roots into the normalized subgroup. -/
theorem unipotent_le_of_noncyclic_torus (X P : Subgroup (Sp F))
    (hPX : P ≤ X) (hPT : P ≤ FullTorusNormalizer.torus)
    (hnc : ¬ IsCyclic P) (hn : unipotent (F := F) ≤ normalizer (X : Set (Sp F))) :
    unipotent (F := F) ≤ X := by
  let d := CentralRootGeometry.diagonalTorusHom (F := F)
  let B := P.comap d
  let f : B →* P := (d.comp B.subtype).codRestrict P (fun a => a.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a,ha⟩ := hPT x.property
    refine ⟨⟨(a.1,a.1⁻¹*a.2),?_⟩,Subtype.ext ha⟩
    change diagonalTorus a.1 (a.1⁻¹*a.2) ∈ P
    change diagonalTorus a.1 (a.1⁻¹*a.2) = (x : Sp F) at ha
    rw [ha]
    exact x.property
  have hB : ¬ IsCyclic B := fun h => hnc (by
    let := h
    exact isCyclic_of_surjective f hf)
  have hr (i : Fin 4) : RootSubgroup.group (F := F) (rootIndex i) ≤ X := by
    obtain ⟨a,ha,hw⟩ := weight_moves B hB i
    exact scalar_root_le X i hn a (hPX ha) hw
  intro x hx
  obtain ⟨⟨b,a,w,v⟩,he⟩ := CentralRootGeometry.element_surjective ⟨x,hx⟩
  have he' := congrArg Subtype.val he
  change (CentralRootGeometry.element b a w v : Sp F) = x at he'
  rw [← he']
  change rootElement 6 b * rootElement 0 (a+b*w) * rootElement 4 w * rootElement 2 v ∈ X
  exact X.mul_mem (X.mul_mem (X.mul_mem
    (hr 3 ((RootSubgroup.mem_group_iff _ _).mpr ⟨b,rfl⟩))
    (hr 0 ((RootSubgroup.mem_group_iff _ _).mpr ⟨a+b*w,rfl⟩)))
    (hr 2 ((RootSubgroup.mem_group_iff _ _).mpr ⟨w,rfl⟩)))
    (hr 1 ((RootSubgroup.mem_group_iff _ _).mpr ⟨v,rfl⟩))


omit [CharP F 2] in
/-- Sylow conjugacy in the Borel aligns the actual odd-primary subgroup with the torus. -/
theorem conjugate_into_torus {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hp : Odd p)
    (P : Subgroup (Sp F)) (hP : IsPGroup p P) (hPB : P ≤ borel) :
    ∃ g ∈ borel (F := F), P.map (MulAut.conj g).toMonoidHom ≤ FullTorusNormalizer.torus := by
  obtain ⟨g,hg⟩ := Theory.GroupTheory.exists_conj_le_of_prime_not_dvd_index
    FullTorusNormalizer.torusInBorel (P.subgroupOf borel)
    (FullTorusNormalizer.prime_not_dvd_torusInBorel_index hF hp) hP.comap_subtype
  refine ⟨g,g.property,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨a,ha⟩ := hg ⟨⟨x,hPB hx⟩,hx,rfl⟩
  exact ⟨a,congrArg Subtype.val ha⟩

/-- The full unipotent Sylow is forced by a noncyclic odd actor in the Borel. -/
theorem unipotent_le_of_noncyclic_odd {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hp : Odd p)
    (X P : Subgroup (Sp F)) (hXB : X ≤ borel) (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : unipotent (F := F) ≤ normalizer (X : Set (Sp F))) : unipotent (F := F) ≤ X := by
  obtain ⟨g,hg,hgP⟩ := conjugate_into_torus hF hp P hP (hPX.trans hXB)
  let c := MulAut.conj g
  have hU : (unipotent (F := F)).map c.toMonoidHom = unipotent :=
    mem_normalizer_iff_map_conj_eq.mp (borel_le_normalizer_unipotent hg)
  have hn' : unipotent (F := F) ≤ normalizer (X.map c.toMonoidHom : Set (Sp F)) := by
    rw [← hU,← map_equiv_normalizer_eq X c]
    exact map_mono hn
  have hc : ¬ IsCyclic (P.map c.toMonoidHom) :=
    fun hc => hnc ((P.equivMapOfInjective c.toMonoidHom c.injective).isCyclic.mpr hc)
  have hle := unipotent_le_of_noncyclic_torus (X.map c.toMonoidHom)
    (P.map c.toMonoidHom) (map_mono hPX) hgP hc hn'
  rw [← hU] at hle
  exact (map_le_map_iff_of_injective c.injective).mp hle

/-- The actual two-core, rather than a chosen two-subgroup, is the full unipotent group. -/
theorem twoCore_eq_unipotent {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hnF : 1 ≤ n) (hp : Odd p)
    (X P : Subgroup (Sp F)) (hXB : X ≤ borel) (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : unipotent (F := F) ≤ normalizer (X : Set (Sp F))) :
    X.pCoreIn 2 = unipotent (F := F) := by
  have hUX := unipotent_le_of_noncyclic_odd hF hp X P hXB hPX hP hnc hn
  apply le_antisymm
  · exact (isPGroup_pCoreIn 2 X).le_sylow_of_normalized (unipotentSylow hF hnF)
      (hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  · exact le_pCoreIn_of_normalizes (unipotentSylow hF hnF).isPGroup'
      hUX (hXB.trans borel_le_normalizer_unipotent)

/-- A soluble subgroup normalized by the specified Sylow has precisely that Sylow
as its two-core when it contains a noncyclic odd-primary subgroup. -/
theorem twoCore_eq_sylow {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hnF : 1 < n) (hp : Odd p)
    (X P : Subgroup (Sp F)) [Group.IsSolvable X] (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) (S : Sylow 2 (Sp F))
    (hn : (S : Subgroup (Sp F)) ≤ normalizer (X : Set (Sp F))) :
    X.pCoreIn 2 = (S : Subgroup (Sp F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hnF.le)
  let c := MulAut.conj g
  have hS : (S : Subgroup (Sp F)).map c.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  let Y := X.map c.toMonoidHom
  let B := P.map c.toMonoidHom
  have hUY : unipotent (F := F) ≤ normalizer (Y : Set (Sp F)) := by
    rw [← hS,← map_equiv_normalizer_eq X c]
    exact map_mono hn
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective
    (c.toMonoidHom.subgroupMap_surjective X)
  let : Group.IsNilpotent (unipotent (F := F)) := (unipotentSylow hF hnF.le).isPGroup'.isNilpotent
  let : Group.IsSolvable (Y ⊔ unipotent (F := F) : Subgroup (Sp F)) :=
    Group.isSolvable_sup_of_normalizes Y unipotent hUY
  have hcontrol := solvable_overgroups_of_orthogonal_root_orbits hF hnF
    (solvable_unipotent_point_orbit_orthogonal
      (by rw [hF]; exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hnF)))
  have hYB : Y ≤ borel := by
    rw [borel_eq_normalizer_unipotent]
    exact le_sup_left.trans (hcontrol (unipotentSylow hF hnF.le)
      (Y ⊔ unipotent) inferInstance le_sup_right)
  have hc : ¬ IsCyclic B :=
    fun hc => hnc ((P.equivMapOfInjective c.toMonoidHom c.injective).isCyclic.mpr hc)
  have he := twoCore_eq_unipotent hF hnF.le hp Y B hYB (map_mono hPX)
    (hP.map c.toMonoidHom) hc hUY
  apply (Subgroup.map_injective (f := c.toMonoidHom) c.injective)
  rw [map_pCoreIn_of_injective 2 X c.toMonoidHom c.injective,hS]
  exact he

/-- Inner normalizers act trivially on the actual odd quotient. -/
theorem normalizer_commutator_le_twoCore {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2^n) (hnF : 1 < n) (hp : Odd p)
    (X P : Subgroup (Sp F)) [Group.IsSolvable X] (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) (S : Sylow 2 (Sp F))
    (hn : (S : Subgroup (Sp F)) ≤ normalizer (X : Set (Sp F))) :
    ⁅normalizer (X : Set (Sp F)), X⁆ ≤ X.pCoreIn 2 := by
  have he := twoCore_eq_sylow hF hnF hp X P hPX hP hnc S hn
  have hnX := normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  change normalizer (X : Set (Sp F)) ≤ normalizer (X.pCoreIn 2 : Set (Sp F)) at hnX
  rw [he] at hnX ⊢
  exact (commutator_mono hnX (X.le_normalizer.trans hnX)).trans
    (commutator_sylow_normalizer_le hF hnF.le S)

end Theory.SpecificGroups.SymplecticFour.NoncyclicOddActor
