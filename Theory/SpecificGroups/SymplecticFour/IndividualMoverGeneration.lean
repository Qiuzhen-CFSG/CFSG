module
public import Theory.SpecificGroups.SymplecticFour.CrossMoverFixedGeneration

/-!
# Individual generation above the original plane intersection

Let T be a normal subgroup of the standard symplectic Sylow, and let its
plane intersection J have order at least q squared. An individual subgroup
E of T strictly larger than J generates Sp4 with the opposite long root.
If T has at most two first coordinates then E=T. Otherwise two commutator
rows put the entire Sylow center in T; the index bound forces E to meet
that center in more than q elements. A long-root Weyl word and a torus
then recover both central roots. The same selector gives opposite planes.

This uses every nonbinary characteristic-two field degree. Its literal
full-kernel application is NonbinarySymplectic.CriticalReduction.IndividualSelection.
Source: MS93 (5.5)(c), printed pp.915--917, critical-root branch. The local
Weyl and torus calculations reuse those in CrossMoverGeneration.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Matrix Subgroup Representation
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.IndividualMoverGeneration
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



private def firstCoordinate : unipotent (F := F) →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (x.val.val (.inl 0) (.inl 1))
  map_one' := rfl
  map_mul' x y := by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
    change Multiplicative.ofAdd ((element b u w v * element c z t a).val.val (.inl 0) (.inl 1)) = _
    simp only [element_mul,element_matrix]
    rfl
private theorem firstCoordinate_element (b u w v : F) :
    firstCoordinate (element b u w v) = Multiplicative.ofAdd b := by
  change Multiplicative.ofAdd ((element b u w v).val.val (.inl 0) (.inl 1)) = _
  rw [element_matrix]
  rfl
private theorem firstCoordinate_ker : (firstCoordinate (F := F)).ker = wing true := by
  ext y
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
  rw [MonoidHom.mem_ker,firstCoordinate_element,element_mem_wing]
  rfl

private theorem center_le_of_two_first_coordinates
    (T : Subgroup (unipotent (F := F))) [T.Normal]
    {b u w v c z t a : F} (hbT : element b u w v ∈ T)
    (hcT : element c z t a ∈ T) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) :
    center (unipotent (F := F)) ≤ T := by
  have hsum : b+c ≠ 0 := fun hh => hbc (CharTwo.add_eq_zero.mp hh)
  have row (s : F) : theta (b^2*s) (b*s) ∈ T := by
    simpa using normal_comm_mem T hbT 0 s
  have row' (s : F) : theta (c^2*s) (c*s) ∈ T := by
    simpa using normal_comm_mem T hcT 0 s
  have long (s : F) : theta s 0 ∈ T := by
    have hh := T.mul_mem (row (s/(b*(b+c)))) (row' (s/(c*(b+c))))
    rw [theta_add] at hh
    convert hh using 1
    congr 1 <;> field_simp <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  intro x hx
  rw [←theta_range] at hx
  obtain ⟨⟨s,t⟩,rfl⟩ := hx
  have hh := T.mul_mem (long (s.toAdd+b*t.toAdd)) (row (t.toAdd/b))
  rw [theta_add] at hh
  change theta s.toAdd t.toAdd ∈ T
  convert hh using 1
  congr 1 <;> field_simp <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem normal_edge_center_or_small_index
    (T : Subgroup (unipotent (F := F))) [T.Normal] :
    center (unipotent (F := F)) ≤ T ∨ (wing true).relIndex T ≤ 2 := by
  classical
  by_cases hex : ∃ b u w v c z t a : F, element b u w v ∈ T ∧
      element c z t a ∈ T ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c
  · obtain ⟨b,u,w,v,c,z,t,a,hbT,hcT,hb,hc,hbc⟩ := hex
    exact Or.inl (center_le_of_two_first_coordinates T hbT hcT hb hc hbc)
  right
  have hcoords : ∃ b₀ : F, ∀ b u w v, element b u w v ∈ T → b=0 ∨ b=b₀ := by
    by_cases hb : ∃ b u w v : F, element b u w v ∈ T ∧ b ≠ 0
    · obtain ⟨b,u,w,v,hbT,hb⟩ := hb
      refine ⟨b,?_⟩
      intro c z t a hcT
      by_cases hc : c=0
      · exact Or.inl hc
      · exact Or.inr (by by_contra he; exact hex ⟨b,u,w,v,c,z,t,a,hbT,hcT,hb,hc,Ne.symm he⟩)
    · push Not at hb
      exact ⟨0,fun b u w v hv => Or.inl (hb b u w v hv)⟩
  obtain ⟨b₀,hb₀⟩ := hcoords
  rw [←firstCoordinate_ker,relIndex_ker]
  let f : T.map firstCoordinate → Bool := fun x => decide (x.val=1)
  have hf : Function.Injective f := by
    intro x y he
    obtain ⟨x₀,hx₀,hx⟩ := x.property
    obtain ⟨y₀,hy₀,hy⟩ := y.property
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x₀
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y₀
    rw [firstCoordinate_element] at hx hy
    have hb := hb₀ b u w v hx₀
    have hc := hb₀ c z t a hy₀
    apply Subtype.ext
    change decide (x.val=1)=decide (y.val=1) at he
    rw [←hx,←hy] at he ⊢
    change decide (b=0)=decide (c=0) at he
    congr 1
    by_cases hb0 : b=0 <;> by_cases hc0 : c=0 <;> simp_all
  simpa using Nat.card_le_card_of_injective f hf


private theorem larger_than_plane_intersection
    (T E : Subgroup (unipotent (F := F))) [T.Normal]
    (hET : E ≤ T) (hc : Nat.card (wing true ⊓ T : Subgroup (unipotent (F := F))) < Nat.card E) :
    E=T ∨ Nat.card F < Nat.card (E ⊓ center (unipotent (F := F)) : Subgroup _) := by
  let J := wing (F := F) true ⊓ T
  change Nat.card J < Nat.card E at hc
  have hJT : J ≤ T := inf_le_right
  have hj := relIndex_mul_relIndex (⊥ : Subgroup (unipotent (F := F))) J T bot_le hJT
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hj
  have he := relIndex_mul_relIndex (⊥ : Subgroup (unipotent (F := F))) E T bot_le hET
  rw [relIndex_bot_left,relIndex_bot_left] at he
  have hp : 0 < Nat.card E := Nat.card_pos
  have htidx : (wing true).relIndex T ≤ Nat.card F := by
    rw [←firstCoordinate_ker,relIndex_ker]
    exact Nat.card_le_card_of_injective
      (fun x : T.map firstCoordinate => x.val.toAdd)
      (fun x y he => Subtype.ext (congrArg Multiplicative.ofAdd he))
  by_cases het : E=T
  · exact Or.inl het
  right
  obtain hz | hi := normal_edge_center_or_small_index T
  · have hidx : E.relIndex T < Nat.card F := by
      have hbound := Nat.mul_le_mul_left (Nat.card J) htidx
      have hstrict := Nat.mul_lt_mul_of_pos_right hc (Nat.card_pos (α := F))
      nlinarith
    have hzi := relIndex_mul_relIndex (⊥ : Subgroup (unipotent (F := F)))
      (E ⊓ center (unipotent (F := F))) (center (unipotent (F := F))) bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,card_center] at hzi
    have hle := relIndex_le_of_le_right (H := E) hz
      (index_ne_zero_of_finite (H := E.subgroupOf T))
    by_contra! hbad
    nlinarith [Nat.card_pos (α := F)]
  · have hidx : 2 ≤ E.relIndex T := by
      have hn : E.relIndex T ≠ 0 := index_ne_zero_of_finite (H := E.subgroupOf T)
      have hn1 : E.relIndex T ≠ 1 := fun hh => het (le_antisymm hET (relIndex_eq_one.mp hh))
      omega
    exfalso
    nlinarith

private theorem large_center_long_root_generate (hq : 2 < Nat.card F)
    (E : Subgroup (unipotent (F := F)))
    (hc : Nat.card F < Nat.card (E ⊓ center (unipotent (F := F)) : Subgroup _))
    (hout : ¬ E ≤ wing true) :
    E.map unipotent.subtype ⊔ RootSubgroup.group 1 = ⊤ := by
  let H := E.map unipotent.subtype ⊔ RootSubgroup.group 1
  have hE (x : unipotent (F := F)) (hx : x ∈ E) : x.val ∈ H :=
    mem_sup_left (mem_map_of_mem _ hx)
  have h1 (t : F) : rootElement 1 t ∈ H := mem_sup_right (subset_closure ⟨t,rfl⟩)
  obtain ⟨s,hs,hsE⟩ : ∃ s : F, s ≠ 0 ∧ theta s 0 ∈ E := by
    classical
    by_contra! hn
    have zero_of_mem (s : F) (hs : theta s 0 ∈ E) : s=0 := by
      by_contra hh
      exact hn s hh hs
    let I := E ⊓ center (unipotent (F := F))
    let f : I → F := fun x => x.val.val.val (.inl 1) (.inr 0)
    have hf : Function.Injective f := by
      intro x y he
      obtain ⟨⟨b,u,w,v⟩,hx⟩ := element_surjective x.val
      obtain ⟨⟨c,z,t,a⟩,hy⟩ := element_surjective y.val
      have hxI : element b u w v ∈ I := by simpa only [hx] using x.property
      have hyI : element c z t a ∈ I := by simpa only [hy] using y.property
      obtain ⟨rfl,rfl⟩ := (mem_center_iff_coordinates b u w v).mp hxI.2
      obtain ⟨rfl,rfl⟩ := (mem_center_iff_coordinates c z t a).mp hyI.2
      change x.val.val.val (.inl 1) (.inr 0)=y.val.val.val (.inl 1) (.inr 0) at he
      simp only [←hx,←hy,element_matrix] at he
      change w=t at he
      subst t
      have hh := E.mul_mem hxI.1 hyI.1
      change theta u w * theta z w ∈ E at hh
      rw [theta_add,CharTwo.add_self_eq_zero] at hh
      have huz := CharTwo.add_eq_zero.mp (zero_of_mem _ hh)
      apply Subtype.ext
      rw [←hx,←hy,huz]
    exact hc.not_ge (Nat.card_le_card_of_injective f hf)
  have hsH : rootElement 0 s ∈ H := by
    simpa [theta_val,RootSubgroup.element_zero] using hE _ hsE
  have hw : rootElement 0 s * rootElement 1 s⁻¹ * rootElement 0 s ∈ H :=
    H.mul_mem (H.mul_mem hsH (h1 _)) hsH
  have h0 (t : F) : rootElement 0 t ∈ H := by
    have hh := H.mul_mem (H.mul_mem hw (h1 (t/s^2))) (H.inv_mem hw)
    rw [long_swap _ _ hs,mul_div_cancel₀ _ (pow_ne_zero _ hs)] at hh
    exact hh
  obtain ⟨u,w,hwE,hw0⟩ : ∃ u w : F, theta u w ∈ E ∧ w ≠ 0 := by
    by_contra! hn
    have hle : E ⊓ center (unipotent (F := F)) ≤ root := by
      intro x hx
      obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
      obtain ⟨rfl,rfl⟩ := (mem_center_iff_coordinates b u w v).mp hx.2
      have hw := hn u w hx.1
      rw [element_mem_root]
      exact ⟨rfl,hw,rfl⟩
    have hh := card_le_of_le hle
    rw [card_root] at hh
    exact hc.not_ge hh
  have hwH : rootElement 4 w ∈ H := by
    have hh := hE _ hwE
    rw [theta_val] at hh
    exact (H.mul_mem_cancel_left (h0 _)).mp hh
  have h4 (t : F) : rootElement 4 t ∈ H := by
    by_cases ht : t=0
    · subst t; simp [RootSubgroup.element_zero]
    let r : Fˣ := Units.mk0 (t/w) (div_ne_zero ht hw0)
    have he : rootElement 4 w = (element 0 0 w 0).val := by
      simp [element,RootSubgroup.element_zero]
    have hh := H.mul_mem (H.mul_mem (scaleFirst_mem H h0 h1 r) hwH)
      (H.inv_mem (scaleFirst_mem H h0 h1 r))
    rw [he,scaleFirst_element] at hh
    simpa [r,element,RootSubgroup.element_zero,div_mul_cancel₀ _ hw0] using hh
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

theorem individual_long_root_generate (hq : 2 < Nat.card F)
    (T J E : Subgroup (unipotent (F := F))) [T.Normal] [J.Normal]
    (hJ : J = wing true ⊓ T) (hET : E ≤ T)
    (hcJ : Nat.card F^2 ≤ Nat.card J) (hcE : Nat.card J < Nat.card E)
    (hout : ¬ E ≤ wing true) :
    E.map unipotent.subtype ⊔ RootSubgroup.group 1 = ⊤ := by
  obtain he | he := larger_than_plane_intersection T E hET (hJ ▸ hcE)
  · exact CrossMoverGeneration.cross_mover_long_root_generate hq J E hcJ
      (movingIndex_le_field_sq_of_le_wing J (hJ ▸ inf_le_left))
      (he.symm ▸ (hJ ▸ inf_le_right)) hout
  · exact large_center_long_root_generate hq E he hout

/-- For a full root in the original plane, one conjugator gives both
cross-mover generation and generation by the two full plane radicals. -/
theorem exists_individual_plane_root_selector (hq : 2 < Nat.card F)
    (T J E : Subgroup (unipotent (F := F))) [T.Normal] [J.Normal]
    (hJ : J = wing true ⊓ T) (hET : E ≤ T)
    (hcJ : Nat.card F^2 ≤ Nat.card J) (hcE : Nat.card J < Nat.card E)
    (hout : ¬ E ≤ wing true)
    (A : Subgroup (Sp F))
    (hAP : A ≤ (wing true).map unipotent.subtype)
    (hcA : Nat.card A = Nat.card F)
    (hdA : Module.finrank F (displacementSpace A) = 1) :
    let P := (wing true).map (unipotent (F := F)).subtype
    ∃ g : Sp F, ((E.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ⊔ A = ⊤) ∧
      P.map (MulAut.conj g).toMonoidHom ⊔ P = ⊤ := by
  dsimp only
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let P := (wing true).map (unipotent (F := F)).subtype
  have hgen := individual_long_root_generate hq T J E hJ hET hcJ hcE hout
  obtain ⟨h,hP,hh⟩ := SelectedPositioning.plane_root_coordinates P A
    ⟨1,by rw [show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext y; simp,Subgroup.map_id]⟩
    hAP hcA hdA
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
  refine ⟨c⁻¹,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,hmaps,hAc,mul_inv_cancel,show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext y; simp,Subgroup.map_id,hgen]
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
  · have hplane : P.map (MulAut.conj o).toMonoidHom ⊔ P = ⊤ := by
      rw [show P = SymplecticConjugatePair.planeRadical from
        SymplecticConjugatePair.planeRadical_eq_wing.symm]
      apply LargePlaneGeneration.opposite_plane_large_subactor_generate _ le_rfl
      rw [SymplecticConjugatePair.card_planeRadical]
      nlinarith [Nat.zero_le (Nat.card F * (Nat.card F - 1)^2)]
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    rw [Subgroup.map_sup,hmaps,hP]
    have hhc : h*c⁻¹=o := by dsimp [c,o]; rw [_root_.mul_inv_rev, mul_inv_cancel_left,TwoConjugate.opposition_inv]
    rw [hhc,hplane,map_top_of_surjective _ (MulAut.conj h).surjective]

end Theory.SpecificGroups.SymplecticFour.IndividualMoverGeneration
