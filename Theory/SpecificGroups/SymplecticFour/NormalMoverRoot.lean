module
public import Theory.SpecificGroups.SymplecticFour.NormalMoverGeneration
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.TransvectionCommutator

/-!
# Long-root generation above order sixteen

A normal subgroup of the field-four Sylow group, outside its plane radical
and of order greater than sixteen, contains a nonidentity central long-root
element. Otherwise the commutator coordinates force every element into the
point radical and two coordinates inject the subgroup into F4 squared.
The opposite full long root enlarges that element to the full long root;
normality then supplies the central short root. The checked torus argument
extracts the missing point radical and generates Sp4.

This lowers the order threshold in the normal-mover selection, including
the order-thirty-two component intersections needed for outer cross images.
Source: MS93 (5.5), pp.915--917, in the field-four tensor application of
Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SelectedGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
private theorem normal_comm_mem (E : Subgroup (unipotent (F := F))) [E.Normal]
    {b u w v : F} (hx : element b u w v ∈ E) (c a : F) :
    theta (c^2*v+b^2*a) (c*v+b*a) ∈ E := by
  rw [←element_commutator b u w v c 0 0 a]
  exact (commutator_le_left E ⊤) (commutator_mem_commutator hx (mem_top _))

private theorem normal_nonplane_long_root (hF : Nat.card F = 4)
    (E : Subgroup (unipotent (F := F))) [E.Normal] (hc : 16 < Nat.card E)
    (hn : ¬ E ≤ wing true) : ∃ s : F, s ≠ 0 ∧ theta s 0 ∈ E := by
  by_contra! hz
  obtain ⟨x,hx,hxw⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hxw
  have no_mixed {b u w v : F} (he : element b u w v ∈ E) (hb : b ≠ 0) : v = 0 := by
    by_contra hv
    have htwo : 2 < Nat.card F := by omega
    obtain ⟨a,ha0,ha1⟩ : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
      let := Fintype.ofFinite Fˣ
      let : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
        rw [←Nat.card_eq_fintype_card,Nat.card_units]; omega)
      obtain ⟨a,ha⟩ := exists_ne (1 : Fˣ)
      exact ⟨a,a.ne_zero,fun h => ha (Units.ext h)⟩
    have hm := normal_comm_mem E he (a*b) (a*v)
    have hs : (a*b)^2*v+b^2*(a*v) = a*(a+1)*b^2*v := by ring
    have ht : (a*b)*v+b*(a*v) = 0 := by
      rw [show (a*b)*v=b*(a*v) by ring,CharTwo.add_self_eq_zero]
    rw [hs,ht] at hm
    exact hz _ (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0
      (fun h => ha1 (CharTwo.add_eq_zero.mp h))) (pow_ne_zero _ hb)) hv) hm
  have hv : v = 0 := no_mixed hx hb
  subst v
  have all_v {c z t a : F} (hy : element c z t a ∈ E) : a = 0 := by
    by_cases hc : c = 0
    · subst c
      have hh := E.mul_mem hx hy
      rw [element_mul] at hh
      simpa using no_mixed hh (by simpa using hb)
    · exact no_mixed hy hc
  let f : E → F × F := fun y =>
    (y.val.val.val (.inl 0) (.inl 1),y.val.val.val (.inl 1) (.inr 0))
  have hf : Function.Injective f := by
    intro y z he
    obtain ⟨⟨c,s,t,a⟩,hy⟩ := element_surjective y.val
    obtain ⟨⟨c',s',t',a'⟩,hz'⟩ := element_surjective z.val
    have hyE : element c s t a ∈ E := by simpa only [hy] using y.property
    have hzE : element c' s' t' a' ∈ E := by simpa only [hz'] using z.property
    have ha := all_v hyE
    have ha' := all_v hzE
    subst a a'
    have hct : c=c' ∧ t=t' := by
      change (_,_) = (_,_) at he
      simp only [←hy,←hz',element_matrix,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
        Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] at he
      exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
    rcases hct with ⟨rfl,rfl⟩
    have hh := E.mul_mem hyE hzE
    have heq : element c s t 0 * element c s' t 0 = theta (s+s') 0 := by
      rw [element_mul,theta,element_eq_iff]
      simp [CharTwo.add_self_eq_zero,mul_comm,add_assoc]
    rw [heq] at hh
    have hs : s = s' := CharTwo.add_eq_zero.mp (by
      by_contra h
      exact hz _ h hh)
    apply Subtype.ext
    rw [←hy,←hz',hs]
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,hF] at hle
  omega


omit [Finite F] in
private theorem long_swap_matrix (s : F) (hs : s ≠ 0) :
    rootMatrix 0 s * rootMatrix 1 s⁻¹ * rootMatrix 0 s =
      fromBlocks !![0,0;0,1] !![s,0;0,0] !![s⁻¹,0;0,0] !![0,0;0,1] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero,hs]

omit [Finite F] in
private theorem long_swap (s t : F) (hs : s ≠ 0) :
    (rootElement 0 s * rootElement 1 s⁻¹ * rootElement 0 s) * rootElement 1 t *
      (rootElement 0 s * rootElement 1 s⁻¹ * rootElement 0 s)⁻¹ = rootElement 0 (s^2*t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (rootMatrix 0 s * rootMatrix 1 s⁻¹ * rootMatrix 0 s) * rootMatrix 1 t =
    rootMatrix 0 (s^2*t) * (rootMatrix 0 s * rootMatrix 1 s⁻¹ * rootMatrix 0 s)
  rw [long_swap_matrix s hs]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero,hs,
      pow_two,mul_assoc,mul_comm,mul_left_comm]
  field_simp

/-- A normal subgroup of order above sixteen outside the plane radical
already generates with the opposite long root over the field of four. -/
theorem normal_nonplane_long_root_generate (hF : Nat.card F = 4)
    (E : Subgroup (unipotent (F := F))) [E.Normal] (hc : 16 < Nat.card E)
    (hn : ¬ E ≤ wing true) :
    E.map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1 = ⊤ := by
  let H := E.map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1
  have hE : ∀ y ∈ E, y.val ∈ H := fun y hy =>
    (show E.map (unipotent (F := F)).subtype ≤ H from le_sup_left) (mem_map_of_mem _ hy)
  have h1 (t : F) : rootElement 1 t ∈ H :=
    (show RootSubgroup.group 1 ≤ H from le_sup_right) (subset_closure ⟨t,rfl⟩)
  obtain ⟨s,hs,hsE⟩ := normal_nonplane_long_root hF E hc hn
  have hsH : rootElement 0 s ∈ H := by
    simpa [theta_val,RootSubgroup.element_zero] using hE _ hsE
  have hw : rootElement 0 s * rootElement 1 s⁻¹ * rootElement 0 s ∈ H :=
    H.mul_mem (H.mul_mem hsH (h1 _)) hsH
  have h0 (t : F) : rootElement 0 t ∈ H := by
    have hh := H.mul_mem (H.mul_mem hw (h1 (t/s^2))) (H.inv_mem hw)
    rw [long_swap _ _ hs,mul_div_cancel₀ _ (pow_ne_zero _ hs)] at hh
    exact hh
  obtain ⟨x,hx,hxw⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hxw
  have h4 (t : F) : rootElement 4 t ∈ H := by
    have hh := hE _ (normal_comm_mem E hx 0 (t/b))
    simp only [zero_pow (by decide : 2 ≠ 0),zero_mul,zero_add,
      mul_div_cancel₀ _ hb,theta_val] at hh
    exact (H.mul_mem_cancel_left (h0 _)).mp hh
  let N := H.comap (unipotent (F := F)).subtype
  have hZ : center (unipotent (F := F)) ≤ N := by
    rw [←theta_range]
    rintro _ ⟨⟨s,t⟩,rfl⟩
    change (theta s.toAdd t.toAdd).val ∈ H
    rw [theta_val]
    exact H.mul_mem (h0 _) (h4 _)
  have hEN : E ≤ N := hE
  have hgen := center_and_nonplane_long_root_generate (by omega : 2 < Nat.card F)
    N hZ (fun hh => hn (hEN.trans hh))
  exact top_unique (hgen ▸ sup_le (map_comap_le _ _) (show RootSubgroup.group 1 ≤ H from le_sup_right))
theorem exists_normal_mover_root_generator
    [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (P : Sylow 2 (Sp F)) (E A : Subgroup (Sp F))
    (hEP : E ≤ P) (hPN : (P : Subgroup (Sp F)) ≤ normalizer (E : Set (Sp F)))
    (hc : 16 < Nat.card E)
    (hm : 16 < Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E))
    (hA : ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g : Sp F, E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) P
    (unipotentSylow (n := 2) hF (by decide))
  have hkP : (P : Subgroup (Sp F)).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let E' := E.map (MulAut.conj k).toMonoidHom
  have hEU : E' ≤ unipotent := hkP ▸ map_mono hEP
  let N := E'.subgroupOf unipotent
  have hNm : N.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hEU
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hEU).mpr
    (hkP ▸ (map_mono hPN).trans (le_normalizer_map _))
  have hNc : Nat.card N = Nat.card E := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hNm,
      card_map_of_injective (MulAut.conj k).injective]
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hdim := BinaryOffender.fixedCodim_map_equivariant σ σ (MulAut.conj k).toMonoidHom
    (SymplecticConjugatePair.Ambient.linearAction σ k)
    (fun g v => by
      change σ k (σ g v) = σ (k*g*k⁻¹) (σ k v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]) E
  have hdim' := BinaryOffender.fixedCodim_map_equivariant
    (σ.comp (unipotent (F := F)).subtype) σ (unipotent (F := F)).subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) N
  rw [hNm] at hdim'
  have hbound : 16 < SmallMovers.movingIndex N := by
    rw [←SmallMovers.binary_movingIndex]
    change 16 < 2 ^ BinaryOffender.fixedCodim (σ.comp (unipotent (F := F)).subtype) N
    rw [hdim',←hdim]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hm
    exact hm
  have hn : ¬ N ≤ wing true := by
    intro hh
    have hh := SmallMovers.movingIndex_le_field_sq_of_le_wing N hh
    rw [hF] at hh
    omega
  have hgen : E' ⊔ RootSubgroup.group 1 = ⊤ := by
    rw [←hNm]
    exact normal_nonplane_long_root_generate hF N (hNc.symm ▸ hc) hn
  obtain ⟨h,hh⟩ := hA
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
  have hmaps (B : Subgroup (Sp F)) (g h : Sp F) :
      (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        B.map (MulAut.conj (g*h)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hAc : A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 := by
    rw [←hmaps,hh,h01]
  refine ⟨c⁻¹*k,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [Subgroup.map_sup,hmaps,hAc,show c*(c⁻¹*k)=k by group,hgen]
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
end Theory.SpecificGroups.SymplecticFour.SelectedGeneration
