module
public import Theory.SpecificGroups.SymplecticFour.SelectedGeneration
public import Theory.SpecificGroups.SymplecticFour.GeneratedRootMovement
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# A selected generator preserving the original symplectic plane radical

Align a full long root inside an order-64 plane radical by moving its
one-dimensional displacement with the plane's SL₂ Levi. Apply the checked
standard selector in these simultaneous coordinates. Its two selected fixed
planes are transverse, its three source subgroups generate Sp₄, and the
selector normalizes the original plane radical containing the root.

Source: MS93 (5.6)(b--d), printed pp.917--918. The original full-kernel lift
is SourceComparison.OriginalSelectedGeneration; the actual overlapping-path
application is GenerationTwoSymplecticPositionedSelection.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SelectedPositioning
open CentralRootGeometry TwoLocalCover InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

private theorem wing_displacement_le_plane :
    displacementSpace ((wing true).map (unipotent (F := F)).subtype) ≤ plane F := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩
  have hg : g.val ∈ SymplecticConjugatePair.planeRadical := by
    simpa only [SymplecticConjugatePair.planeRadical_eq_wing] using g.property
  obtain ⟨B,hB⟩ := SymplecticConjugatePair.mem_planeRadical_iff g.val |>.mp hg
  change g.val • v-v ∈ plane F
  rw [←hB]
  intro i
  simp [Plane.shearSp,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.one_apply]

private theorem levi_normalizes_wing (A : SpecialLinearGroup (Fin 2) F) :
    Plane.leviSp A ∈ normalizer ((wing true).map (unipotent (F := F)).subtype : Set (Sp F)) := by
  rw [←SymplecticConjugatePair.planeRadical_eq_wing]
  exact (Plane.radical (F := F)).le_normalizer_map planeLocal.subtype
    (mem_map_of_mem planeLocal.subtype (by rw [normalizer_eq_top]; trivial :
      Plane.levi A ∈ normalizer (Plane.radical (F := F) : Set (planeLocal (F := F)))))

private theorem wing_root_alignment (A : Subgroup (Sp F))
    (hA : A ≤ (wing true).map (unipotent (F := F)).subtype)
    (hc : Nat.card A = Nat.card F) (hd : Module.finrank F (displacementSpace A) = 1) :
    ∃ k : Sp F, k ∈ normalizer ((wing true).map (unipotent (F := F)).subtype : Set (Sp F)) ∧
      A.map (MulAut.conj k).toMonoidHom = RootSubgroup.group 0 := by
  have hn : displacementSpace A ≠ ⊥ := by
    intro h
    rw [h,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  have hdisp : displacementSpace A ≤ plane F := by
    apply le_trans _ wing_displacement_le_plane
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp
      ((wing true).map (unipotent (F := F)).subtype).subtype) ⟨g,hA g.property⟩ w
  have hvp := hdisp hv
  have htop : (fun i => v (.inl i)) ≠ (0 : Fin 2 → F) := by
    intro h
    apply hv0
    ext i
    cases i with
    | inl i => exact congrFun h i
    | inr i => exact hvp i
  have he0 : (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨a,ha⟩ := natural_transitive htop he0
  let k := Plane.leviSp a
  have hkv : k • v = e 0 := by
    ext i
    cases i with
    | inl i =>
      have h := congrFun ha i
      simpa [k,smul_eq_mulVec,Plane.leviSp,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,e,Pi.single_apply] using h
    | inr i =>
      simp [k,Plane.leviSp,Matrix.mulVec,dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,e,hvp 0,hvp 1]
  have hline : (displacementSpace A).map (toLinear k).toLinearMap = point F := by
    rw [hspan,Submodule.map_span]
    simp only [Set.image_singleton]
    change Submodule.span F {k • v} = point F
    rw [hkv]
    rfl
  refine ⟨k,levi_normalizes_wing a,?_⟩
  apply eq_of_le_of_card_ge
  · rintro g ⟨x,hx,rfl⟩
    apply FourLongRoots.mem_root_zero_of_movedSpace_le_point
    change InvolutionTypes.movedSpace (k*x*k⁻¹) ≤ point F
    rw [movedSpace_conj,←hline]
    apply Submodule.map_mono
    rintro w ⟨u,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype) ⟨x,hx⟩ u
  · rw [card_map_of_injective (MulAut.conj k).injective,RootSubgroup.card,hc]

/-- Simultaneously align the original plane radical and its contained full root. -/
theorem plane_root_coordinates (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hAE : A ≤ E) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1) :
    ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype ∧
      A.map (MulAut.conj k).toMonoidHom = RootSubgroup.group 0 := by
  obtain ⟨h,hh⟩ := hE
  have hA : A.map (MulAut.conj h).toMonoidHom ≤ (wing true).map (unipotent (F := F)).subtype :=
    hh ▸ map_mono hAE
  have hcard : Nat.card (A.map (MulAut.conj h).toMonoidHom) = Nat.card F := by
    rw [card_map_of_injective (MulAut.conj h).injective,hc]
  have hdim : Module.finrank F (displacementSpace (A.map (MulAut.conj h).toMonoidHom)) = 1 := by
    rw [displacementSpace_conjugate,(toLinear h).finrank_map_eq,hd]
  obtain ⟨k,hk,hroot⟩ := wing_root_alignment _ hA hcard hdim
  refine ⟨k*h,?_,?_⟩
  · rw [←map_conj_mul,hh]
    exact mem_normalizer_iff_map_conj_eq.mp hk
  · rwa [map_conj_mul] at hroot

/-- The selector preserves the original plane radical containing the root,
while its conjugated mover and the two roots generate and have transverse
paired fixed planes. -/
theorem exists_plane_root_positioned_generators
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hAE : A ≤ E) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (∀ v : Vector F,
        (∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y • v = v) →
        (∀ y ∈ (E.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom, y • v = v) → v = 0) ∧
      x ∈ normalizer (E : Set (Sp F)) := by
  obtain ⟨k,hk,hroot⟩ := plane_root_coordinates E A hE hAE hc hd
  obtain ⟨x₀,hgen,hsep,hpos⟩ := SelectedGeneration.exists_standard_plane_root_selector (F := F)
  let o := TwoConjugate.opposition (F := F)
  let c := o*k
  have h01 : (RootSubgroup.group (F := F) 0).map (MulAut.conj o).toMonoidHom =
      RootSubgroup.group 1 := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
      change o * rootElement 0 t * o⁻¹ ∈ _
      rw [(TwoConjugate.opposition_central_axes t).1]
      exact subset_closure ⟨t,rfl⟩
    · intro hy
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
      exact ⟨rootElement 0 t,subset_closure ⟨t,rfl⟩,(TwoConjugate.opposition_central_axes t).1⟩
  have hAc : A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 := by
    rw [←map_conj_mul,hroot,h01]
  refine ⟨c⁻¹*k,c⁻¹*x₀*c,?_,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_conj_mul,map_conj_mul,hAc]
    rw [show c*(c⁻¹*k)=k by group,
      show c*(c⁻¹*x₀*c)=x₀*c by group,hk,←map_conj_mul,hAc,hgen]
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
  · intro v hv hw
    have hE : (E.map (MulAut.conj (c⁻¹*k)).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        (wing true).map (unipotent (F := F)).subtype := by
      rw [map_conj_mul,show c*(c⁻¹*k)=k by group,hk]
    have hEx : ((E.map (MulAut.conj (c⁻¹*k)).toMonoidHom).map
        (MulAut.conj (c⁻¹*x₀*c)⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        ((wing true).map (unipotent (F := F)).subtype).map
          (MulAut.conj x₀⁻¹).toMonoidHom := by
      rw [←hE]
      simp only [map_conj_mul]
      apply congrArg (fun h : Sp F => E.map (MulAut.conj h).toMonoidHom)
      group
    have transport (K : Subgroup (Sp F)) (hv : ∀ y ∈ K, y • v = v) :
        ∀ y ∈ K.map (MulAut.conj c).toMonoidHom, y • (c • v) = c • v := by
      rintro y ⟨z,hz,rfl⟩
      change (c*z*c⁻¹) • (c • v) = c • v
      rw [←mul_smul,inv_mul_cancel_right,mul_smul,hv z hz]
    have hzero := hsep (c • v) (hE ▸ transport _ hv) (hEx ▸ transport _ hw)
    have hz := congrArg (fun w : Vector F => c⁻¹ • w) hzero
    simpa only [inv_smul_smul,smul_zero] using hz
  · rw [mem_normalizer_iff_map_conj_eq]
    change E.map (MulAut.conj (c⁻¹*x₀*c)).toMonoidHom = E
    apply Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
    rw [map_conj_mul,hk]
    have he : k*(c⁻¹*x₀*c)=(o⁻¹*x₀*o)*k := by dsimp [c]; group
    rw [he,←map_conj_mul,hk]
    exact mem_normalizer_iff_map_conj_eq.mp hpos

/-- The natural small-mover hypotheses retain placement whenever the root
belongs to the original mover; generation and separation hold in all cases. -/
theorem exists_small_mover_positioned_generators
    (hF : Nat.card F = 4)
    (E A : Subgroup (Sp F)) (hE : IsPGroup 2 E) (hc : Nat.card E = 64)
    (hm : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E) ≤ 16)
    (hAc : Nat.card A = 4) (hAd : Module.finrank F (displacementSpace A) = 1)
    (hAq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (∀ v : Vector F,
        (∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y • v = v) →
        (∀ y ∈ (E.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom, y • v = v) → v = 0) ∧
      (A ≤ E → x ∈ normalizer (E : Set (Sp F))) := by
  by_cases hAE : A ≤ E
  · obtain ⟨g,x,hgen,hsep,hpos⟩ := exists_plane_root_positioned_generators E A
      (SelectedGeneration.conjugate_plane_of_small_order hF E hE hc hm) hAE (hAc.trans hF.symm) hAd
    exact ⟨g,x,hgen,hsep,fun _ => hpos⟩
  · obtain ⟨g,x,hgen,hsep⟩ := SelectedGeneration.exists_small_mover_two_root_separated_generators
      hF E A hE hc hm hAc hAd hAq
    exact ⟨g,x,hgen,hsep,fun h => False.elim (hAE h)⟩

end Theory.SpecificGroups.SymplecticFour.SelectedPositioning
