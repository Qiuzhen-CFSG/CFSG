module
public import Theory.SpecificGroups.SymplecticFour.SelectedPositioning
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Degree

/-!
# Simultaneous root and full-plane generation

An explicit symplectic selector interchanges the two lower long roots.
An upper shear carries its conjugated plane radical to the opposite
radical, so the same selector gives both three-subgroup root generation
and generation by the pair of full plane radicals. The latter identity
lifts fixed-layer centrality through arbitrary whole kernels; no central
complement is chosen. Simultaneous root/plane coordinates retain the
original parabolic when the root belongs to it.

A small two-subgroup of order q cubed is also recognized as a full plane
radical at every binary degree. The actual critical-path consumer is
NonbinarySymplectic.CriticalReduction.CubicSelection.
Source: MS93 (5.6)(b--d), printed pp.917--918, full-plane/root branch.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SelectedPlaneGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def selector : Sp F :=
  rootElement 5 1 * (rootElement 6 1 * rootElement 7 1 * rootElement 6 1)

omit [Finite F] in
private theorem selector_matrix : (selector (F := F)).val =
    fromBlocks !![0,1;1,0] 0 1 !![0,1;1,0] := by
  change rootMatrix 5 1 * (rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem selector_inv : (selector (F := F))⁻¹ = selector := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (selector (F := F)).val * (selector (F := F)).val = 1
  rw [selector_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks,CharTwo.add_self_eq_zero]

private theorem upper_mem (r : Fin 8) (hr : r=0 ∨ r=2 ∨ r=4) (t : F) :
    rootElement r t ∈ (wing true).map (unipotent (F := F)).subtype := by
  rcases hr with rfl | rfl | rfl
  · refine ⟨element 0 t 0 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]
  · refine ⟨element 0 0 0 t,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]
  · refine ⟨element 0 0 t 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]

omit [Finite F] in
private theorem selector_lower (t : F) :
    selector * rootElement 1 t * selector⁻¹ = rootElement 3 t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (selector (F := F)).val * rootMatrix 1 t = rootMatrix 3 t * (selector (F := F)).val
  rw [selector_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks]

omit [Finite F] in
private theorem shifted_selector_axes (t : F) :
    (rootElement 4 1 * selector) * rootElement 0 t * (rootElement 4 1 * selector)⁻¹ = rootElement 1 t ∧
    (rootElement 4 1 * selector) * rootElement 4 t * (rootElement 4 1 * selector)⁻¹ = rootElement 5 t := by
  constructor <;> rw [mul_inv_eq_iff_eq_mul] <;> apply Subtype.ext
  all_goals
    change (rootMatrix 4 1 * (selector (F := F)).val) * _ = _ * (rootMatrix 4 1 * (selector (F := F)).val)
    rw [selector_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootElement,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
        Matrix.single,Matrix.fromBlocks,CharTwo.add_self_eq_zero]

private theorem selector_roots_generate :
    ((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
      (RootSubgroup.group 1).map (MulAut.conj (selector (F := F))).toMonoidHom = ⊤ := by
  let H := ((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
    (RootSubgroup.group 1).map (MulAut.conj (selector (F := F))).toMonoidHom
  have hu (r : Fin 8) (hr : r=0 ∨ r=2 ∨ r=4) (t : F) : rootElement r t ∈ H :=
    (show (wing true).map (unipotent (F := F)).subtype ≤ H from le_sup_left.trans le_sup_left) (upper_mem r hr t)
  have h1 (t : F) : rootElement 1 t ∈ H :=
    (show RootSubgroup.group 1 ≤ H from le_sup_right.trans le_sup_left) (subset_closure ⟨t,rfl⟩)
  have h3 (t : F) : rootElement 3 t ∈ H := by
    rw [←selector_lower]
    exact (show (RootSubgroup.group 1).map (MulAut.conj (selector (F := F))).toMonoidHom ≤ H from le_sup_right) (mem_map_of_mem _ (subset_closure ⟨t,rfl⟩))
  have hop : TwoConjugate.opposition (F := F) ∈ H := by
    have he : (rootElement 0 (1:F) * rootElement 1 1 * rootElement 0 1) *
        (rootElement 2 1 * rootElement 3 1 * rootElement 2 1) = TwoConjugate.opposition := by
      apply Subtype.ext
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [rootElement,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
          Matrix.single,Matrix.fromBlocks,TwoConjugate.opposition,CharTwo.add_self_eq_zero]
    rw [←he]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hu 0 (by simp) 1) (h1 1)) (hu 0 (by simp) 1))
      (H.mul_mem (H.mul_mem (hu 2 (by simp) 1) (h3 1)) (hu 2 (by simp) 1))
  apply TwoConjugate.eq_top_of_four_axes H (hu 0 (by simp)) h1 (hu 4 (by simp))
  intro t
  rw [←(TwoConjugate.opposition_central_axes t).2]
  exact H.mul_mem (H.mul_mem hop (hu 4 (by simp) t)) (H.inv_mem hop)

private theorem selector_planes_generate :
    (wing true).map (unipotent (F := F)).subtype ⊔
      ((wing true).map (unipotent (F := F)).subtype).map
        (MulAut.conj (selector (F := F))⁻¹).toMonoidHom = ⊤ := by
  let P := (wing true).map (unipotent (F := F)).subtype
  let H := P ⊔ P.map (MulAut.conj (selector (F := F))⁻¹).toMonoidHom
  have hu (r : Fin 8) (hr : r=0 ∨ r=2 ∨ r=4) (t : F) : rootElement r t ∈ H :=
    (show P ≤ H from le_sup_left) (upper_mem r hr t)
  have hl (r : Fin 8) (hr : r=0 ∨ r=2 ∨ r=4) (t : F) :
      (rootElement 4 1 * selector) * rootElement r t * (rootElement 4 1 * selector)⁻¹ ∈ H := by
    have hc : selector * rootElement r t * selector⁻¹ ∈ H := by
      have hh := (show P.map (MulAut.conj (selector (F := F))⁻¹).toMonoidHom ≤ H from le_sup_right)
        (mem_map_of_mem _ (upper_mem r hr t))
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,selector_inv] using hh
    simpa only [_root_.mul_inv_rev,mul_assoc] using H.mul_mem (H.mul_mem (hu 4 (by simp) 1) hc)
      (H.inv_mem (hu 4 (by simp) 1))
  refine TwoConjugate.eq_top_of_four_axes H (hu 0 (by simp)) ?_ (hu 4 (by simp)) ?_
  · intro t
    rw [←(shifted_selector_axes t).1]
    exact hl 0 (by simp) t
  · intro t
    rw [←(shifted_selector_axes t).2]
    exact hl 4 (by simp) t

private theorem selector_position :
    TwoConjugate.opposition⁻¹*selector*TwoConjugate.opposition ∈
      normalizer ((wing true).map (unipotent (F := F)).subtype : Set (Sp F)) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let o := TwoConjugate.opposition (F := F)
  have hm : (o⁻¹*selector*o).val = fromBlocks !![0,1;1,0] 1 0 !![0,1;1,0] := by
    rw [show o⁻¹=o from TwoConjugate.opposition_inv]
    change o.val*(selector (F := F)).val*o.val = _
    rw [selector_matrix]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [o,TwoConjugate.opposition,Matrix.mul_apply,Fintype.sum_sum_type,
        Matrix.fromBlocks,Matrix.one_apply]
  have hl : o⁻¹*selector*o ∈ planeLocal := by
    apply (Plane.mem_local_iff _).mpr
    refine ⟨?_,?_⟩
    · rw [mem_planeParabolic_iff]
      intro i j
      rw [hm]
      rfl
    · rw [hm]
      simp [Matrix.toBlocks₁₁,Matrix.fromBlocks,Matrix.det_fin_two,CharTwo.neg_eq]
  rw [←SymplecticConjugatePair.planeRadical_eq_wing]
  exact (Plane.radical (F := F)).le_normalizer_map planeLocal.subtype
    (mem_map_of_mem planeLocal.subtype (by rw [normalizer_eq_top]; trivial :
      (⟨_,hl⟩ : planeLocal (F := F)) ∈ normalizer (Plane.radical (F := F) : Set (planeLocal (F := F)))))

/-- One selector supplies root generation and generation by the two whole
plane radicals, while preserving the original opposite plane radical. -/
theorem exists_standard_selector :
    ∃ x : Sp F,
      (((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
        (RootSubgroup.group 1).map (MulAut.conj x).toMonoidHom = ⊤) ∧
      ((wing true).map (unipotent (F := F)).subtype ⊔
        ((wing true).map (unipotent (F := F)).subtype).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      TwoConjugate.opposition⁻¹*x*TwoConjugate.opposition ∈
        normalizer ((wing true).map (unipotent (F := F)).subtype : Set (Sp F)) := by
  exact ⟨selector,selector_roots_generate,selector_planes_generate,selector_position⟩

/-- The same standard selector retains its exact long-root image, so
proper subgroups of the plane radical can use its two generating roots. -/
theorem exists_standard_root_plane_selector :
    ∃ x : Sp F,
      (RootSubgroup.group 1).map (MulAut.conj x).toMonoidHom = RootSubgroup.group 3 ∧
      ((wing true).map (unipotent (F := F)).subtype ⊔
        ((wing true).map (unipotent (F := F)).subtype).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      TwoConjugate.opposition⁻¹*x*TwoConjugate.opposition ∈
        normalizer ((wing true).map (unipotent (F := F)).subtype : Set (Sp F)) := by
  refine ⟨selector,?_,selector_planes_generate,selector_position⟩
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
    change selector * rootElement 1 t * selector⁻¹ ∈ _
    rw [selector_lower]
    exact subset_closure ⟨t,rfl⟩
  · intro hy
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
    exact ⟨rootElement 1 t,subset_closure ⟨t,rfl⟩,selector_lower t⟩

omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

private theorem selection_in_coordinates
    (E A : Subgroup (Sp F)) (k h : Sp F)
    (hk : E.map (MulAut.conj k).toMonoidHom = (wing true).map unipotent.subtype)
    (hh : A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (E.map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      (E.map (MulAut.conj h).toMonoidHom = (wing true).map unipotent.subtype →
        x ∈ normalizer (E : Set (Sp F))) := by
  obtain ⟨x₀,hgen,hpair,hpos⟩ := exists_standard_selector (F := F)
  let o := TwoConjugate.opposition (F := F)
  let c := o*h
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
    rw [←map_conj_mul,hh,h01]
  have htop : (⊤ : Subgroup (Sp F)).map (MulAut.conj c).toMonoidHom = ⊤ := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
  refine ⟨c⁻¹*k,c⁻¹*x₀*c,?_,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_conj_mul,map_conj_mul,hAc,htop]
    rw [show c*(c⁻¹*k)=k by group,
      show c*(c⁻¹*x₀*c)=x₀*c by group,hk,←map_conj_mul,hAc,hgen]
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,map_conj_mul,map_conj_mul,map_conj_mul,htop]
    rw [show c*(c⁻¹*k)=k by group,
      show c*(c⁻¹*x₀*c)⁻¹*(c⁻¹*k)=x₀⁻¹*k by group,hk,←map_conj_mul,hk]
    exact hpair
  · intro he
    rw [mem_normalizer_iff_map_conj_eq]
    change E.map (MulAut.conj (c⁻¹*x₀*c)).toMonoidHom = E
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    rw [map_conj_mul,he]
    have heq : h*(c⁻¹*x₀*c)=(o⁻¹*x₀*o)*h := by dsimp [c]; group
    rw [heq,←map_conj_mul,he]
    exact mem_normalizer_iff_map_conj_eq.mp hpos

variable [Algebra (ZMod 2) F]
/-- A full plane radical and a full long root admit simultaneous source
root generation and full-plane-pair generation. If the root belongs to
the original radical, the same selector normalizes that radical. -/
theorem exists_plane_root_generators
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace A) = 1)
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (E.map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      (A ≤ E → x ∈ normalizer (E : Set (Sp F))) := by
  by_cases hAE : A ≤ E
  · obtain ⟨k,hk,ha⟩ := SelectedPositioning.plane_root_coordinates E A hE hAE hc hd
    obtain ⟨g,x,hgen,hpair,hpos⟩ := selection_in_coordinates E A k k hk ha
    exact ⟨g,x,hgen,hpair,fun _ => hpos hk⟩
  · obtain ⟨k,hk⟩ := hE
    obtain ⟨h,hh⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one A hc hd hq
    obtain ⟨g,x,hgen,hpair,_⟩ := selection_in_coordinates E A k h hk hh
    exact ⟨g,x,hgen,hpair,fun h => (hAE h).elim⟩

/-- A small two-subgroup of order q cubed is a whole plane radical at the original field degree. -/
theorem conjugate_plane_of_cubic_order
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n)
    (E : Subgroup (Sp F)) (hE : IsPGroup 2 E) (hc : Nat.card E = Nat.card F^3)
    (hm : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E) ≤ Nat.card F^2) :
    ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype := by
  obtain ⟨P,hP⟩ := hE.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) P
    (unipotentSylow hF hn)
  have hkP : (P : Subgroup (Sp F)).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let E' := E.map (MulAut.conj k).toMonoidHom
  have hEU : E' ≤ unipotent := hkP ▸ map_mono hP
  let A := E'.subgroupOf unipotent
  have hAm : A.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hEU
  have hAc : Nat.card A = Nat.card F^3 := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hAm,
      card_map_of_injective (MulAut.conj k).injective,hc]
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hdim := BinaryOffender.fixedCodim_map_equivariant σ σ (MulAut.conj k).toMonoidHom
    (SymplecticConjugatePair.Ambient.linearAction σ k)
    (fun g v => by
      change σ k (σ g v) = σ (k*g*k⁻¹) (σ k v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]) E
  have hdim' := BinaryOffender.fixedCodim_map_equivariant
    (σ.comp (unipotent (F := F)).subtype) σ (unipotent (F := F)).subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) A
  rw [hAm] at hdim'
  have hbound : SmallMovers.movingIndex A ≤ Nat.card F^2 := by
    rw [←SmallMovers.binary_movingIndex]
    change 2 ^ BinaryOffender.fixedCodim (σ.comp (unipotent (F := F)).subtype) A ≤ Nat.card F^2
    rw [hdim',←hdim]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hm
    exact hm
  have hs : SmallMovers.Degree.Small A := ⟨hbound.trans (by rw [hAc]; exact Nat.pow_le_pow_right Nat.card_pos (by decide)),hbound⟩
  have hAw : A = wing true := by
    rcases SmallMovers.Degree.small_classification_nonstandard A hs with h | ⟨l,hl⟩
    · apply eq_of_le_of_card_ge h
      rw [card_wing,hAc]
    · have hf : 1 < Nat.card F := by
        rw [hF]
        exact one_lt_pow₀ (by decide) (by omega)
      rw [hl,SmallMovers.card_finitePlane] at hAc
      exact (Nat.pow_lt_pow_right hf (by decide : 2 < 3)).ne hAc |>.elim
  exact ⟨k,hAm.symm.trans (congrArg (Subgroup.map (unipotent (F := F)).subtype) hAw)⟩


end Theory.SpecificGroups.SymplecticFour.SelectedPlaneGeneration
