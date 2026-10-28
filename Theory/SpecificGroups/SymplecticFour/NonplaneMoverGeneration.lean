module
public import Theory.SpecificGroups.SymplecticFour.IndividualMoverGeneration
public import Theory.SpecificGroups.SymplecticFour.PointLargeGeneration

/-!
# Individual generation with a full nonplane critical image

Let T be normal in the standard Sylow, and E be an individual subgroup
whose order is at least that of T's plane intersection. A full nonplane
point-plane subgroup in T forces the entire Sylow center into T. Hence
E meets that center in at least q elements. The opposite point-plane
then recovers the full central roots: a nonzero first central coordinate
uses a rank-one adjustment, while a zero first-coordinate intersection
supplies the full short root and a commutator supplies the long root.
An element of E outside the plane completes generation at every q > 2.

The same selector makes the two full plane radicals generate. The literal
full-kernel and backward-path consumers are NonbinarySymplectic.CriticalReduction.
NonplaneIndividualSelection and NonplaneIndividualPaths. This includes
movers containing the original vertex kernel; no splitting of X is assumed.
Source: MS93 (5.5)(b,c), printed pp.915--917, nonplane-image branch.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Matrix Subgroup Representation
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.NonplaneMoverGeneration
open CentralRootGeometry CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
private def lowerAdjust (u w : F) : Sp F :=
  TwoConjugate.opposition * (element (w/u) u⁻¹ 0 0).val * TwoConjugate.opposition⁻¹
omit [Finite F] in
private theorem lowerAdjust_matrix (u w : F) :
    (lowerAdjust u w).val = fromBlocks !![1,0;w/u,1] 0 !![u⁻¹,0;0,0] !![1,w/u;0,1] := by
  change (TwoConjugate.opposition (F := F)).val * (element (w/u) u⁻¹ 0 0).val.val *
    (TwoConjugate.opposition⁻¹).val = _
  rw [TwoConjugate.opposition_inv,element_matrix]
  simp [TwoConjugate.opposition,Matrix.fromBlocks_multiply]
omit [Finite F] in
private theorem adjusted_matrix (u w v : F) (hu : u≠0) :
    (lowerAdjust u w * (element 0 u w v).val).val =
      fromBlocks !![1,0;w/u,1] !![u,w;0,w*w/u+v]
        !![u⁻¹,0;0,0] !![0,0;0,1] := by
  change (lowerAdjust u w).val * (element 0 u w v).val.val = _
  rw [lowerAdjust_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.fromBlocks,CharTwo.add_self_eq_zero,hu,div_eq_mul_inv,
      mul_assoc,mul_comm,mul_left_comm]
omit [Finite F] in
private theorem adjusted_long_root (u w v s : F) (hu : u≠0) :
    (lowerAdjust u w * (element 0 u w v).val) * rootElement 1 s *
      (lowerAdjust u w * (element 0 u w v).val)⁻¹ = rootElement 0 (u^2*s) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (lowerAdjust u w * (element 0 u w v).val).val * rootMatrix 1 s =
    rootMatrix 0 (u^2*s) * (lowerAdjust u w * (element 0 u w v).val).val
  rw [adjusted_matrix _ _ _ hu]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,hu,
      pow_two,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
  field_simp

omit [Finite F] in
private theorem lowerAdjust_word (u w : F) :
    lowerAdjust u w = rootElement 7 (w/u) * rootElement 1 u⁻¹ := by
  apply Subtype.ext
  change (lowerAdjust u w).val = rootMatrix 7 (w/u) * rootMatrix 1 u⁻¹
  rw [lowerAdjust_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq]

omit [Finite F] in
private theorem lower_short_upper_long (s t : F) :
    ⁅rootElement 7 t,rootElement 0 s⁆ = (element 0 0 (s*t) (s*t^2)).val := by
  rw [commutatorElement_def,mul_inv_eq_iff_eq_mul,mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change rootMatrix 7 t * rootMatrix 0 s = (element 0 0 (s*t) (s*t^2)).val.val * rootMatrix 0 s * rootMatrix 7 t
  rw [element_matrix]
  simp only [rootMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.fromBlocks_multiply,mul_zero,zero_mul,add_zero,zero_add,
    mul_one,one_mul]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,Matrix.vecHead,Matrix.vecTail,CharTwo.neg_eq,CharTwo.add_self_eq_zero,pow_two,
      mul_assoc,mul_comm,mul_left_comm]

omit [Finite F] in
private theorem upper_short_lower_matrix (s t : F) :
    rootMatrix 4 t * rootMatrix 1 s * rootMatrix 4 t =
      fromBlocks !![1,0;s*t,1] !![0,0;0,s*t^2] !![s,0;0,0] !![1,s*t;0,1] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,pow_two,
      mul_assoc,mul_comm,mul_left_comm]

omit [Finite F] in
private theorem mixed_lower_matrix (a b s : F) :
    rootMatrix 7 a * rootMatrix 2 b * rootMatrix 1 s =
      fromBlocks !![1,0;a,1] !![0,0;0,b] !![s,0;0,0] !![1,a;0,1] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem upper_short_lower_long (s t : F) :
    ⁅rootElement 4 t,rootElement 1 s⁆ = rootElement 7 (s*t) * rootElement 2 (s*t^2) := by
  have hi : (rootElement 4 t)⁻¹ = rootElement 4 t := by
    apply inv_eq_of_mul_eq_one_left
    rw [RootSubgroup.element_add,CharTwo.add_self_eq_zero,RootSubgroup.element_zero]
  rw [commutatorElement_def,mul_inv_eq_iff_eq_mul,hi]
  apply Subtype.ext
  change rootMatrix 4 t * rootMatrix 1 s * rootMatrix 4 t =
    rootMatrix 7 (s*t) * rootMatrix 2 (s*t^2) * rootMatrix 1 s
  rw [upper_short_lower_matrix,mixed_lower_matrix]

private theorem short_of_long_and_lower_short (hq : 2 < Nat.card F)
    (H : Subgroup (Sp F))
    (h0 : ∀ s, rootElement 0 s ∈ H) (h7 : ∀ t, rootElement 7 t ∈ H) :
    ∀ s, rootElement 4 s ∈ H := by
  let := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [←Nat.card_eq_fintype_card,Nat.card_units]; omega)
  obtain ⟨t,ht⟩ := exists_ne (1 : Fˣ)
  have ht1 : (t:F) ≠ 1 := fun he => ht (Units.ext he)
  have hc : (t:F)+(t:F)^2 ≠ 0 := by
    intro he
    have hh : (t:F)*(1+(t:F))=0 := by simpa only [mul_add,mul_one,←pow_two] using he
    have hh' := (mul_eq_zero.mp hh).resolve_left t.ne_zero
    exact ht1 (CharTwo.add_eq_zero.mp hh').symm
  intro s
  let r := s/((t:F)+(t:F)^2)
  have hcomm (a b : F) : (element 0 0 (a*b) (a*b^2)).val ∈ H := by
    rw [←lower_short_upper_long]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h7 b) (h0 a)) (H.inv_mem (h7 b))) (H.inv_mem (h0 a))
  have hh := H.mul_mem (hcomm r t) (hcomm (r*(t:F)^2) 1)
  change (element 0 0 (r*(t:F)) (r*(t:F)^2) *
    element 0 0 (r*(t:F)^2*1) (r*(t:F)^2*1^2)).val ∈ H at hh
  rw [element_mul] at hh
  have he : r*(t:F)+r*(t:F)^2=s := by
    rw [←mul_add]
    exact div_mul_cancel₀ _ hc
  simpa [he,element,RootSubgroup.element_zero,CharTwo.add_self_eq_zero] using hh

/-- The full opposite point-plane and a sufficiently large central intersection
recover the whole point radical, even when the individual mover contains no full root. -/
private theorem generate_of_center_index (hq : 2 < Nat.card F)
    (E : Subgroup (unipotent (F := F)))
    (hc : Nat.card F ≤ Nat.card (E ⊓ center (unipotent (F := F)) : Subgroup _))
    (hout : ¬ E ≤ wing true)
    (H : Subgroup (Sp F)) (hE : E.map unipotent.subtype ≤ H)
    (h1 : ∀ s, rootElement 1 s ∈ H) (h7 : ∀ t, rootElement 7 t ∈ H) : H=⊤ := by
  have h0 : ∀ s, rootElement 0 s ∈ H := by
    by_cases hex : ∃ u w : F, theta u w ∈ E ∧ u≠0
    · obtain ⟨u,w,hw,hu⟩ := hex
      have hx : (element 0 u w 0).val ∈ H := hE (mem_map_of_mem _ hw)
      have hk : lowerAdjust u w ∈ H := by
        rw [lowerAdjust_word]
        exact H.mul_mem (h7 _) (h1 _)
      intro s
      have hh := H.mul_mem (H.mul_mem (H.mul_mem hk hx) (h1 (s/u^2)))
        (H.inv_mem (H.mul_mem hk hx))
      rw [adjusted_long_root _ _ _ _ hu,mul_div_cancel₀ _ (pow_ne_zero _ hu)] at hh
      exact hh
    · have hz : ∀ u w : F, theta u w ∈ E → u=0 := by
        intro u w hw
        by_contra hn
        exact hex ⟨u,w,hw,hn⟩
      let C := E ⊓ center (unipotent (F := F))
      have hC : C.map unipotent.subtype ≤ RootSubgroup.group 4 := by
        rintro _ ⟨y,hy,rfl⟩
        obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
        obtain ⟨rfl,rfl⟩ := (mem_center_iff_coordinates _ _ _ _).mp hy.2
        have hu := hz u w hy.1
        subst u
        simpa [element,RootSubgroup.element_zero] using
          (show rootElement 4 w ∈ RootSubgroup.group (F := F) 4 from subset_closure ⟨w,rfl⟩)
      have heq : C.map unipotent.subtype = RootSubgroup.group 4 :=
        eq_of_le_of_card_ge hC (by rw [RootSubgroup.card,card_map_of_injective unipotent.subtype_injective]; exact hc)
      have h4 (s : F) : rootElement 4 s ∈ H := by
        apply hE
        exact map_mono inf_le_left (heq.symm ▸ (show rootElement 4 s ∈ RootSubgroup.group 4 from subset_closure ⟨s,rfl⟩))
      have h2 (s : F) : rootElement 2 s ∈ H := by
        have hh := H.mul_mem (H.mul_mem (H.mul_mem (h4 1) (h1 s))
          (H.inv_mem (h4 1))) (H.inv_mem (h1 s))
        change ⁅rootElement 4 (1:F),rootElement 1 s⁆ ∈ H at hh
        rw [upper_short_lower_long] at hh
        simp only [mul_one,one_pow] at hh
        exact (H.mul_mem_cancel_left (h7 s)).mp hh
      obtain ⟨x,hx,hxp⟩ := SetLike.not_le_iff_exists.mp hout
      obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
      have hb : b≠0 := by simpa only [element_mem_wing,↓reduceIte] using hxp
      intro s
      have hr (a : F) : (element 0 0 0 a).val ∈ H := by
        simpa [element,RootSubgroup.element_zero] using h2 a
      have hh := H.mul_mem (H.mul_mem (H.mul_mem (hE (mem_map_of_mem _ hx)) (hr (s/b^2)))
        (H.inv_mem (hE (mem_map_of_mem _ hx)))) (H.inv_mem (hr (s/b^2)))
      change (⁅element b u w v,element 0 0 0 (s/b^2)⁆).val ∈ H at hh
      rw [element_commutator] at hh
      simp only [zero_pow (by decide : 2≠0),zero_mul,zero_add,mul_div_cancel₀ _ (pow_ne_zero _ hb),theta_val] at hh
      exact (H.mul_mem_cancel_right (h4 _)).mp hh
  have h4 := short_of_long_and_lower_short hq H h0 h7
  let N := H.comap unipotent.subtype
  have hCN : center (unipotent (F := F)) ≤ N := by
    rw [←theta_range]
    rintro _ ⟨⟨u,w⟩,rfl⟩
    change (theta u.toAdd w.toAdd).val ∈ H
    rw [theta_val]
    exact H.mul_mem (h0 _) (h4 _)
  have hEN : E ≤ N := (map_le_iff_le_comap).mp hE
  have hg := SelectedGeneration.center_and_nonplane_long_root_generate hq N hCN
    (fun he => hout (hEN.trans he))
  exact top_unique (hg ▸ sup_le (map_comap_le _ _) ((closure_le _).mpr
    (by rintro _ ⟨s,rfl⟩; exact h1 s)))

omit [Finite F] in
private theorem normal_comm_mem (E : Subgroup (unipotent (F := F))) [E.Normal]
    {b u w v : F} (hx : element b u w v ∈ E) (c a : F) :
    theta (c^2*v+b^2*a) (c*v+b*a) ∈ E := by
  rw [←element_commutator b u w v c 0 0 a]
  exact (commutator_le_left E ⊤) (commutator_mem_commutator hx (mem_top _))

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


private theorem center_le_of_finitePlane (hq : 2 < Nat.card F)
    (T : Subgroup (unipotent (F := F))) [T.Normal]
    (l : F) (ha : finitePlane l ≤ T) : center (unipotent (F := F)) ≤ T := by
  let := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [←Nat.card_eq_fintype_card,Nat.card_units]; omega)
  obtain ⟨s,hs⟩ := exists_ne (1 : Fˣ)
  have hs1 : (s:F) ≠ 1 := fun he => hs (Units.ext he)
  apply center_le_of_two_first_coordinates T
    (ha ((element_mem_finitePlane l 1 0 l 0).mpr (by simp)))
    (ha ((element_mem_finitePlane l s 0 (l*s) 0).mpr ⟨rfl,rfl⟩))
    one_ne_zero s.ne_zero hs1.symm

private theorem center_index_bound
    (T E : Subgroup (unipotent (F := F))) (hET : E ≤ T)
    (hZ : center (unipotent (F := F)) ≤ T)
    (hc : Nat.card (wing true ⊓ T : Subgroup _) ≤ Nat.card E) :
    Nat.card F ≤ Nat.card (E ⊓ center (unipotent (F := F)) : Subgroup _) := by
  let J := wing (F := F) true ⊓ T
  change Nat.card J ≤ Nat.card E at hc
  have hi : (wing (F := F) true).index = Nat.card F := by
    have hh := (wing (F := F) true).card_mul_index
    rw [card_wing,card_unipotent,show Nat.card F^4=Nat.card F^3*Nat.card F by ring] at hh
    exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos _) hh
  have hidx : (wing (F := F) true).relIndex T ≤ Nat.card F := by
    have hh := relIndex_le_of_le_right (H := wing (F := F) true) (le_top : T ≤ ⊤)
      (by rw [relIndex_top_right]; exact index_ne_zero_of_finite)
    simpa [hi] using hh
  have hj := relIndex_mul_relIndex (⊥ : Subgroup (unipotent (F := F))) J T bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hj
  have he := relIndex_mul_relIndex (⊥ : Subgroup (unipotent (F := F))) E T bot_le hET
  rw [relIndex_bot_left,relIndex_bot_left] at he
  have hETidx : E.relIndex T ≤ Nat.card F := by
    have hh := Nat.mul_le_mul hc hidx
    rw [hj,←he] at hh
    exact Nat.le_of_mul_le_mul_left hh Nat.card_pos
  have hz := relIndex_mul_relIndex (⊥ : Subgroup (unipotent (F := F)))
    (E ⊓ center (unipotent (F := F))) (center (unipotent (F := F))) bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,card_center] at hz
  have hzi := (relIndex_le_of_le_right (H := E) hZ
    (index_ne_zero_of_finite (H := E.subgroupOf T))).trans hETidx
  have hh := Nat.mul_le_mul_left (Nat.card (E ⊓ center (unipotent (F := F)) : Subgroup _)) hzi
  rw [hz,pow_two] at hh
  exact Nat.le_of_mul_le_mul_right hh Nat.card_pos

omit [Finite F] in
private theorem last_conj (l b u w v : F) :
    element 0 0 0 l * element b u w v * (element 0 0 0 l)⁻¹ =
      element b u (w+b*l) v := by
  rw [mul_inv_eq_iff_eq_mul,element_mul,element_mul,element_eq_iff]
  simp [mul_comm,add_comm]

private theorem last_preserves_plane (l : F) :
    (wing (F := F) true).map (MulAut.conj (element 0 0 0 l)).toMonoidHom = wing true := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    change element 0 0 0 l * element b u w v * (element 0 0 0 l)⁻¹ ∈ _
    rw [last_conj,element_mem_wing]
    exact (element_mem_wing true _ _ _ _).mp hy
  · exact (card_map_of_injective (MulAut.conj (element 0 0 0 l)).injective).ge

private theorem last_aligns_finitePlane (l : F) :
    (finitePlane l).map (MulAut.conj (element 0 0 0 l)).toMonoidHom = finitePlane 0 := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    obtain ⟨hv,hw⟩ := (element_mem_finitePlane l b u w v).mp hy
    subst v w
    change element 0 0 0 l * element b u (l*b) 0 * (element 0 0 0 l)⁻¹ ∈ _
    rw [last_conj,element_mem_finitePlane]
    simp [mul_comm,CharTwo.add_self_eq_zero]
  · rw [card_map_of_injective (MulAut.conj (element 0 0 0 l)).injective,
      card_finitePlane,card_finitePlane]

omit [Finite F] in
private theorem opposition_short (t : F) :
    TwoConjugate.opposition * rootElement 6 t * TwoConjugate.opposition⁻¹ = rootElement 7 t := by
  rw [TwoConjugate.opposition_inv]
  apply Subtype.ext
  change (TwoConjugate.opposition (F := F)).val * rootMatrix 6 t *
    (TwoConjugate.opposition (F := F)).val = rootMatrix 7 t
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [TwoConjugate.opposition,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq]

omit [CharP F 2] [Finite F] in
private theorem image_conjugate (A : Subgroup (unipotent (F := F)))
    (g : unipotent (F := F)) :
    (A.map (MulAut.conj g).toMonoidHom).map unipotent.subtype =
      (A.map unipotent.subtype).map (MulAut.conj g.val).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1

omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- A nonplane endpoint permits individual generation even at equality of
image orders. One selector also makes the two full plane radicals generate. -/
theorem exists_individual_nonplane_selector (hq : 2 < Nat.card F)
    (T E : Subgroup (unipotent (F := F))) [T.Normal]
    (hET : E ≤ T)
    (hc : Nat.card (wing true ⊓ T : Subgroup _) ≤ Nat.card E)
    (hout : ¬ E ≤ wing true)
    (l : F) (ha : finitePlane l ≤ T) :
    let P := (wing true).map (unipotent (F := F)).subtype
    ∃ g : Sp F,
      (E.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ⊔
        (finitePlane l).map unipotent.subtype = ⊤ ∧
      P.map (MulAut.conj g).toMonoidHom ⊔ P = ⊤ := by
  dsimp only
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let c := element (0:F) 0 0 l
  let E' := E.map (MulAut.conj c).toMonoidHom
  let P := (wing (F := F) true).map unipotent.subtype
  let A := (finitePlane (0:F)).map unipotent.subtype
  let o := TwoConjugate.opposition (F := F)
  have hcenter : Nat.card F ≤ Nat.card (E' ⊓ center (unipotent (F := F)) : Subgroup _) := by
    have hh := center_index_bound T E hET (center_le_of_finitePlane hq T l ha) hc
    have he : E' ⊓ center (unipotent (F := F)) =
        (E ⊓ center (unipotent (F := F))).map (MulAut.conj c).toMonoidHom := by
      rw [map_inf _ _ _ (MulAut.conj c).injective]
      simp only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq]
      rfl
    rwa [he,card_map_of_injective (MulAut.conj c).injective]
  have hout' : ¬ E' ≤ wing true := by
    intro hh
    apply hout
    have hp := last_preserves_plane l
    apply (map_le_map_iff_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective).mp
    exact hp.symm ▸ hh
  have hgen : E'.map unipotent.subtype ⊔ A.map (MulAut.conj o).toMonoidHom = ⊤ := by
    apply generate_of_center_index hq E' hcenter hout' _ le_sup_left
    · intro s
      apply mem_sup_right
      refine ⟨rootElement 0 s,?_,(TwoConjugate.opposition_central_axes s).1⟩
      refine ⟨element 0 s 0 0,(element_mem_finitePlane 0 _ _ _ _).mpr (by simp),?_⟩
      simp [element,RootSubgroup.element_zero]
    · intro s
      apply mem_sup_right
      refine ⟨rootElement 6 s,?_,opposition_short s⟩
      refine ⟨element s 0 0 0,(element_mem_finitePlane 0 _ _ _ _).mpr (by simp),?_⟩
      simp [element,RootSubgroup.element_zero]
  have hpc : P.map (MulAut.conj c.val).toMonoidHom = P := by
    exact (image_conjugate (wing true) c).symm.trans
      (congrArg (Subgroup.map unipotent.subtype) (last_preserves_plane l))
  have hac : ((finitePlane l).map unipotent.subtype).map
      (MulAut.conj c.val).toMonoidHom = A := by
    exact (image_conjugate (finitePlane l) c).symm.trans
      (congrArg (Subgroup.map unipotent.subtype) (last_aligns_finitePlane l))
  have hec : (E.map unipotent.subtype).map (MulAut.conj c.val).toMonoidHom =
      E'.map unipotent.subtype := (image_conjugate E c).symm
  have ho : o⁻¹=o := TwoConjugate.opposition_inv
  have hopp : P.map (MulAut.conj o).toMonoidHom ⊔ P = ⊤ := by
    rw [show P = SymplecticConjugatePair.planeRadical from SymplecticConjugatePair.planeRadical_eq_wing.symm]
    apply LargePlaneGeneration.opposite_plane_large_subactor_generate _ le_rfl
    rw [SymplecticConjugatePair.card_planeRadical]
    exact lt_of_lt_of_le (by nlinarith : Nat.card F < Nat.card F^2)
      (Nat.pow_le_pow_right Nat.card_pos (by decide : 2≤3))
  refine ⟨c.val⁻¹*o*c.val,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj (o*c.val)).toMonoidHom) (MulAut.conj (o*c.val)).injective
    rw [Subgroup.map_sup,map_conj_mul,
      show (o*c.val)*(c.val⁻¹*o*c.val)=c.val by
        have hoo : o*o=1 := (congrArg (o * ·) ho.symm).trans (mul_inv_cancel o)
        calc
          _ = (o*o)*c.val := by group
          _ = _ := by rw [hoo,one_mul],
      hec,←map_conj_mul,hac,hgen,map_top_of_surjective _ (MulAut.conj _).surjective]
  · apply Subgroup.map_injective (f := (MulAut.conj c.val).toMonoidHom) (MulAut.conj c.val).injective
    rw [Subgroup.map_sup,map_conj_mul,
      show c.val*(c.val⁻¹*o*c.val)=o*c.val by group,
      ←map_conj_mul,hpc,hopp,map_top_of_surjective _ (MulAut.conj _).surjective]

end Theory.SpecificGroups.SymplecticFour.NonplaneMoverGeneration
