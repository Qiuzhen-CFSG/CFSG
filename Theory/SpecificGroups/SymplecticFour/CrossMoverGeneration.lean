module
public import Theory.SpecificGroups.SymplecticFour.NormalMoverRoot
public import Theory.GroupTheory.SmallMoverNormalizer
/-!
# Generation by the join of unequal symplectic movers

A Sylow-normal plane subgroup of order at least q squared contains a
nonidentity central long-root element. Otherwise its remaining coordinates
embed it into a set of size at most 2q, impossible for q greater than two.
Small natural movement puts a Sylow-normal subgroup in the standard plane.
The opposite full long root enlarges the nonidentity long-root element;
a torus then enlarges a nonzero short-root element. Any overgroup escaping
the plane now generates Sp4 with that opposite long root.

The overgroup need not be Sylow-normal. This distinction permits the literal
join of two neighboring movers in the replacement graph. The full-kernel
application is NonbinarySymplectic.CriticalReduction.CrossSelection.
Source: MS93 (5.5)(a), printed pp.915--917. This proves generation by the
join; it does not assert the separate individual-mover clauses (b,c).
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CrossMoverGeneration
open CentralRootGeometry CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
omit [Finite F] in
private theorem normal_comm_mem (E : Subgroup (unipotent (F := F))) [E.Normal]
    {b u w v : F} (hx : element b u w v ∈ E) (c a : F) :
    theta (c^2*v+b^2*a) (c*v+b*a) ∈ E := by
  rw [←element_commutator b u w v c 0 0 a]
  exact (commutator_le_left E ⊤) (commutator_mem_commutator hx (mem_top _))

private def scaleFirst (s : Fˣ) : Sp F :=
  (rootElement 0 (s : F) * rootElement 1 ((s⁻¹ : Fˣ) : F) * rootElement 0 (s : F)) *
    (rootElement 0 1 * rootElement 1 1 * rootElement 0 1)

omit [Finite F] in
private theorem scaleFirst_matrix (s : Fˣ) :
    (scaleFirst s).val = diagonal (Sum.elim ![(s : F),1] ![((s⁻¹ : Fˣ) : F),1]) := by
  change (rootMatrix 0 (s : F) * rootMatrix 1 ((s⁻¹ : Fˣ) : F) * rootMatrix 0 (s : F)) *
    (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      Matrix.diagonal]

omit [Finite F] in
private theorem scaleFirst_element (s : Fˣ) (b u w v : F) :
    scaleFirst s * (element b u w v).val * (scaleFirst s)⁻¹ =
      (element ((s:F)*b) ((s:F)^2*u) ((s:F)*w) v).val := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (scaleFirst s).val * (element b u w v).val.val =
    (element ((s:F)*b) ((s:F)^2*u) ((s:F)*w) v).val.val * (scaleFirst s).val
  rw [scaleFirst_matrix,element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks,
      pow_two,mul_add,mul_assoc,mul_comm,mul_left_comm]

omit [Finite F] [CharP F 2] in
private theorem scaleFirst_mem (H : Subgroup (Sp F))
    (h0 : ∀ t, rootElement 0 t ∈ H) (h1 : ∀ t, rootElement 1 t ∈ H) (s : Fˣ) :
    scaleFirst s ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem (h0 _) (h1 _)) (h0 _))
    (H.mul_mem (H.mul_mem (h0 _) (h1 _)) (h0 _))

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


/-- A Sylow-normal plane subgroup of order at least q squared has a
nonidentity central long-root element at every q greater than two. -/
theorem normal_plane_has_long_root (hq : 2 < Nat.card F)
    (E : Subgroup (unipotent (F := F))) [E.Normal]
    (hplane : E ≤ wing true) (hc : Nat.card F^2 ≤ Nat.card E) :
    ∃ s : F, s ≠ 0 ∧ theta s 0 ∈ E := by
  classical
  by_contra! hz
  have zero_of_mem (s : F) (hs : theta s 0 ∈ E) : s=0 := by
    by_contra hn
    exact hz s hn hs
  obtain ⟨v₀,hv₀⟩ : ∃ v₀ : F, ∀ u w v, element 0 u w v ∈ E → v=0 ∨ v=v₀ := by
    by_cases hex : ∃ u w v, element 0 u w v ∈ E ∧ v≠0
    · obtain ⟨u₀,w₀,v₀,hx,hv₀⟩ := hex
      refine ⟨v₀,?_⟩
      intro u w v hy
      by_cases hv : v=0
      · exact Or.inl hv
      right
      have hh := E.mul_mem (normal_comm_mem E hx v 0) (normal_comm_mem E hy v₀ 0)
      change element 0 _ _ 0 * element 0 _ _ 0 ∈ E at hh
      rw [element_mul] at hh
      have hw : v*v₀+v₀*v=0 := by rw [mul_comm v₀ v,CharTwo.add_self_eq_zero]
      simp only [zero_pow (by decide : 2 ≠ 0),zero_mul,add_zero] at hh
      rw [hw] at hh
      have he := zero_of_mem _ hh
      have hf : v^2*v₀+v₀^2*v = v*v₀*(v+v₀) := by ring
      simp only [mul_zero,add_zero] at he
      rw [hf] at he
      exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero hv hv₀))
    · push Not at hex
      exact ⟨0,fun u w v hv => Or.inl (hex u w v hv)⟩
  let f : E → F × Bool := fun y =>
    (y.val.val.val (.inl 1) (.inr 0),decide (y.val.val.val (.inl 1) (.inr 1)=0))
  have hf : Function.Injective f := by
    intro y z he
    obtain ⟨⟨b,u,w,v⟩,hy⟩ := element_surjective y.val
    obtain ⟨⟨b',u',w',v'⟩,hz'⟩ := element_surjective z.val
    have hyE : element b u w v ∈ E := by simpa only [hy] using y.property
    have hzE : element b' u' w' v' ∈ E := by simpa only [hz'] using z.property
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp (hplane hyE)
    have hb' : b'=0 := (element_mem_wing true _ _ _ _).mp (hplane hzE)
    subst b b'
    change (_,_) = (_,_) at he
    simp only [←hy,←hz',element_matrix,fromBlocks_apply₁₂,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] at he
    have hw : w=w' := congrArg Prod.fst he
    have hd : decide (v=0)=decide (v'=0) := congrArg Prod.snd he
    have hv : v=v' := by
      have hv := hv₀ u w v hyE
      have hv' := hv₀ u' w' v' hzE
      by_cases h0 : v=0 <;> by_cases h0' : v'=0 <;> simp_all
    subst w' v'
    have hh := E.mul_mem hyE hzE
    have heq : element 0 u w v * element 0 u' w v = theta (u+u') 0 := by
      rw [element_mul,theta,element_eq_iff]
      simp [CharTwo.add_self_eq_zero]
    rw [heq] at hh
    have hu : u=u' := CharTwo.add_eq_zero.mp (zero_of_mem _ hh)
    apply Subtype.ext
    rw [←hy,←hz',hu]
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,show Nat.card Bool=2 by simp [Nat.card_eq_fintype_card]] at hle
  nlinarith

/-- A large normal subgroup with small natural movement lies in the
standard plane radical, in the original Sylow coordinates. -/
theorem normal_small_le_plane (E : Subgroup (unipotent (F := F))) [E.Normal]
    (hm : SmallMovers.movingIndex E ≤ Nat.card F^2) : E ≤ wing true := by
  by_contra hn
  obtain ⟨l,hl⟩ := SmallMovers.Degree.exists_plane_coordinates_of_not_le_wing E hm hn
  obtain ⟨x,hx,hout⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b≠0 := by simpa only [element_mem_wing,↓reduceIte] using hout
  have hh := normal_comm_mem E hx 0 1
  change element 0 _ _ 0 ∈ E at hh
  have he := (hl _ _ _ _ hh).2
  simp only [zero_pow (by decide : 2≠0),zero_mul,mul_one,zero_add,mul_zero] at he
  exact hb he

/-- The neighboring cross-join needs no normality of its own. It generates
with the opposite long root as soon as it escapes the plane of the normal
large small mover which it contains. -/
theorem cross_mover_long_root_generate (hq : 2 < Nat.card F)
    (J E : Subgroup (unipotent (F := F))) [J.Normal]
    (hc : Nat.card F^2 ≤ Nat.card J)
    (hm : SmallMovers.movingIndex J ≤ Nat.card F^2)
    (hJE : J ≤ E) (hout : ¬ E ≤ wing true) :
    E.map unipotent.subtype ⊔ RootSubgroup.group 1 = ⊤ := by
  let H := E.map unipotent.subtype ⊔ RootSubgroup.group 1
  have hJ (y : unipotent (F := F)) (hy : y ∈ J) : y.val ∈ H :=
    mem_sup_left (mem_map_of_mem _ (hJE hy))
  have h1 (t : F) : rootElement 1 t ∈ H := mem_sup_right (subset_closure ⟨t,rfl⟩)
  obtain ⟨s,hs,hsJ⟩ := normal_plane_has_long_root hq J (normal_small_le_plane J hm) hc
  have hsH : rootElement 0 s ∈ H := by
    simpa [theta_val,RootSubgroup.element_zero] using hJ _ hsJ
  have hw : rootElement 0 s * rootElement 1 s⁻¹ * rootElement 0 s ∈ H :=
    H.mul_mem (H.mul_mem hsH (h1 _)) hsH
  have h0 (t : F) : rootElement 0 t ∈ H := by
    have hh := H.mul_mem (H.mul_mem hw (h1 (t/s^2))) (H.inv_mem hw)
    rw [long_swap _ _ hs,mul_div_cancel₀ _ (pow_ne_zero _ hs)] at hh
    exact hh
  have hshort : ∃ w : F, w≠0 ∧ rootElement 4 w ∈ H := by
    by_cases hex : ∃ u w v, element 0 u w v ∈ J ∧ v≠0
    · obtain ⟨u,w,v,hv,hv0⟩ := hex
      have hh := hJ _ (normal_comm_mem J hv 1 0)
      simp only [one_pow,one_mul,zero_pow (by decide : 2≠0),zero_mul,add_zero,
        theta_val] at hh
      exact ⟨v,hv0,(H.mul_mem_cancel_left (h0 _)).mp hh⟩
    · push Not at hex
      have hn : ¬ J ≤ root := by
        intro hh
        have he := card_le_of_le hh
        rw [card_root] at he
        nlinarith
      obtain ⟨y,hy,hyr⟩ := SetLike.not_le_iff_exists.mp hn
      obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
      have hb : b=0 := (element_mem_wing true _ _ _ _).mp ((normal_small_le_plane J hm) hy)
      subst b
      have hv : v=0 := hex u w v hy
      subst v
      have hw : w≠0 := by simpa only [element_mem_root,eq_self_iff_true,true_and,and_true] using hyr
      have hh := hJ _ hy
      change (theta u w).val ∈ H at hh
      rw [theta_val] at hh
      exact ⟨w,hw,(H.mul_mem_cancel_left (h0 _)).mp hh⟩
  obtain ⟨w,hw,hwH⟩ := hshort
  have h4 (t : F) : rootElement 4 t ∈ H := by
    by_cases ht : t=0
    · subst t; simp [RootSubgroup.element_zero]
    let r : Fˣ := Units.mk0 (t/w) (div_ne_zero ht hw)
    have he : rootElement 4 w = (element 0 0 w 0).val := by
      simp [element,RootSubgroup.element_zero]
    have hh := H.mul_mem (H.mul_mem (scaleFirst_mem H h0 h1 r) hwH)
      (H.inv_mem (scaleFirst_mem H h0 h1 r))
    rw [he,scaleFirst_element] at hh
    simpa [r,element,RootSubgroup.element_zero,div_mul_cancel₀ _ hw] using hh
  let N := H.comap unipotent.subtype
  have hZ : center (unipotent (F := F)) ≤ N := by
    rw [←theta_range]
    rintro _ ⟨⟨u,w⟩,rfl⟩
    change (theta u.toAdd w.toAdd).val ∈ H
    rw [theta_val]
    exact H.mul_mem (h0 _) (h4 _)
  have hEN : E ≤ N := fun y hy => mem_sup_left (mem_map_of_mem _ hy)
  have hgen := SelectedGeneration.center_and_nonplane_long_root_generate hq N hZ
    (fun hh => hout (hEN.trans hh))
  exact top_unique (hgen ▸ sup_le (map_comap_le _ _) (show RootSubgroup.group 1 ≤ H from le_sup_right))


/-- Place the cross-join relative to a prescribed full long root. -/
theorem exists_cross_mover_root_generator (hq : 2 < Nat.card F)
    (J E : Subgroup (unipotent (F := F))) [J.Normal]
    (hc : Nat.card F^2 ≤ Nat.card J)
    (hm : SmallMovers.movingIndex J ≤ Nat.card F^2)
    (hJE : J ≤ E) (hout : ¬ E ≤ wing true)
    (A : Subgroup (Sp F))
    (hA : ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g : Sp F, (E.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  have hgen := cross_mover_long_root_generate hq J E hc hm hJE hout
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
  refine ⟨c⁻¹,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [Subgroup.map_sup,hmaps,hAc,mul_inv_cancel,show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext y; simp,Subgroup.map_id,hgen]
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
end Theory.SpecificGroups.SymplecticFour.CrossMoverGeneration
