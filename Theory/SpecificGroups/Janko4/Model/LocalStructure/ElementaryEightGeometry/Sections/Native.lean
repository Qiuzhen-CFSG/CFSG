module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Sections.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.AmbientCentralizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PrimedQuotientCentralizer

/-!
# Native uniqueness of the selected elementary-eight centralizers

Choose the specified lifts inside the given elementary subgroup. The actual square and
commutation equations give the finite correction problem. Conjugation by mask
eight or sixteen places the lifts in the displayed eight. Full quotient and
kernel centralizer bounds then force equality of the entire centralizers.
The primed row is handled without assuming the omitted lift exists.
The ambient theorems keep the original seed, inclusion and quotient map.
Source: Kleidman--Wilson (1988), Propositions 2.3.4(i) and 2.3.5.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Sections
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
open Theory.GroupTheory
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis nativeMask correctedLift
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

private theorem native_cast_unprimed (r : Fin 2) :
    unprimedRow (r.castLE (by decide)) = r.castLE (by decide) := by fin_cases r <;> rfl

private theorem mask_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : nativeMask m = nativeMask n) : m = n := by
  have hh := ((nativeMask_eq_maskEquiv ⟨m,hm⟩).symm.trans h).trans
    (nativeMask_eq_maskEquiv ⟨n,hn⟩)
  have he : e ⟨m,hm⟩ = e ⟨n,hn⟩ := Subtype.ext hh
  exact congrArg Fin.val ((e).injective he)

private theorem shifted_square (i : Fin 6) (m : Fin 2048)
    (hs : (nativeMask m.val * correctedLift i) * (nativeMask m.val * correctedLift i) = 1) :
    starMask (starElement i) m.val = m.val := by
  have he : nativeMask m.val * nativeMask (starMask (starElement i) m.val) = 1 := by
    calc
      _ = (nativeMask m.val * correctedLift i) * (nativeMask m.val * correctedLift i) := by
        calc
          _ = nativeMask m.val * (nativeMask (starMask (starElement i) m.val) * correctedLift i) * correctedLift i := by
            simp only [mul_assoc, correctedLift_square, mul_one]
          _ = nativeMask m.val * (correctedLift i * nativeMask m.val) * correctedLift i := by
            rw [correctedLift_mask_mul]
          _ = _ := by simp only [mul_assoc]
      _ = 1 := hs
  exact mask_injective (starMask_lt _ _) m.isLt
    (mul_left_cancel (he.trans (nativeMask_square m.val).symm))

private theorem shifted_commute (i j : Fin 6) (m n : Fin 2048)
    (hij : Commute (correctedLift i) (correctedLift j))
    (h : Commute (nativeMask m.val * correctedLift i) (nativeMask n.val * correctedLift j)) :
    starMask (starElement i) n.val ^^^ n.val = starMask (starElement j) m.val ^^^ m.val := by
  have eqmul (k h l t a : L) (ha : l * h = a * l) :
      (k * l) * (h * t) = (k * a) * (l * t) := by
    calc
      _ = k * (l * h) * t := by simp only [mul_assoc]
      _ = k * (a * l) * t := by rw [ha]
      _ = _ := by simp only [mul_assoc]
  have hh := h.eq
  rw [eqmul _ _ _ _ _ (correctedLift_mask_mul i n),
      eqmul _ _ _ _ _ (correctedLift_mask_mul j m), hij.eq] at hh
  have hmasks := mul_right_cancel hh
  rw [← nativeMask_xor, ← nativeMask_xor] at hmasks
  have hnum : m.val ^^^ starMask (starElement i) n.val =
      n.val ^^^ starMask (starElement j) m.val :=
    mask_injective (Nat.xor_lt_two_pow (n := 11) m.isLt (starMask_lt _ _))
      (Nat.xor_lt_two_pow (n := 11) n.isLt (starMask_lt _ _)) hmasks
  apply Nat.eq_of_testBit_eq
  intro k
  have hk := congrArg (fun a : ℕ => a.testBit k) hnum
  simp only [Nat.testBit_xor] at hk ⊢
  revert hk
  cases m.val.testBit k <;> cases n.val.testBit k <;>
    cases (starMask (starElement i) n.val).testBit k <;>
    cases (starMask (starElement j) m.val).testBit k <;> decide

private theorem kernel_conjugate_shift (r : Fin 2) (j : Fin 4) (m k : Fin 2048) :
    nativeMask k.val * (nativeMask m.val * correctedGenerator r j) * (nativeMask k.val)⁻¹ =
      nativeMask (m.val ^^^ (k.val ^^^ starMask (starElement (correctedIndex r j)) k.val)) *
        correctedGenerator r j := by
  rw [inv_eq_of_mul_eq_one_left (nativeMask_square k.val)]
  calc
    _ = ((nativeMask k.val * nativeMask m.val) *
        nativeMask (starMask (starElement (correctedIndex r j)) k.val)) * correctedGenerator r j := by
      simp only [mul_assoc,correctedGenerator,correctedLift_mask_mul]
    _ = ((nativeMask m.val * nativeMask k.val) *
        nativeMask (starMask (starElement (correctedIndex r j)) k.val)) * correctedGenerator r j := by
      rw [(nativeMask_commute k.val m.val).eq]
    _ = _ := by simp only [nativeMask_xor,mul_assoc]

private theorem fixed_mem_eight (r : Fin 2) (m : Fin 2048)
    (hm : fixedTest (r.castLE (by decide)) m) : nativeMask m.val ∈ localEight r := by
  apply (show centralKernel r ≤ localEight r from le_sup_right)
  refine ⟨e m,?_,(nativeMask_eq_maskEquiv m).symm⟩
  apply (mask_mem_pairRow_centralizer_iff (liftClosure r) _ (liftClosure_projection r) _).mpr
  simpa only [native_cast_unprimed] using hm

/-- An arbitrary elementary lift of the whole literal row has a centralizer
conjugate to the constructed eight by one of two explicitly bounded kernel
elements. No choice of lifts, ambient centralizer equality, or normalizer
conclusion is assumed. -/
theorem local_centralizer_conjugacy (A : Subgroup L) [IsElementaryAbelian 2 A]
    (r : Fin 2) (hrow : A.map π = pairRowImage (r.castLE (by decide))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = twist r) ∧
      (centralizer (A : Set L)).map (MulAut.conj (nativeMask k.val)).toMonoidHom = localEight r := by
  have hex (j : Fin 4) : ∃ a ∈ A, π a = starElement (correctedIndex r j) := by
    have h := pairRowGenerator_mem (r.castLE (by decide)) j
    rw [← hrow] at h
    obtain ⟨a,ha,he⟩ := h
    refine ⟨a,ha,he.trans ?_⟩
    fin_cases r <;> fin_cases j <;> rfl
  choose a ha hp using hex
  have hf (j : Fin 4) := (correctedLift_fibre (correctedIndex r j) (a j)).mp (hp j)
  choose m hm huniq using hf
  have hs (j : Fin 4) : maskImage (rows r j) (m j).val = (m j).val := by
    rw [← action_eq]
    apply shifted_square
    rw [← hm j]
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (a j) (ha j)
  have hc (i j : Fin 4) : maskImage (rows r i) (m j).val ^^^ (m j).val =
      maskImage (rows r j) (m i).val ^^^ (m i).val := by
    rw [← action_eq,← action_eq]
    apply shifted_commute _ _ _ _ (correctedGenerator_commute r i j)
    rw [← hm i,← hm j]
    exact setLike_mul_comm (ha i) (ha j)
  obtain ⟨k,hk,hfixed⟩ := correction r m hs hc
  let g := nativeMask k.val
  let B : Subgroup L := closure (Set.range (fun j => g * a j * g⁻¹))
  have hB : B ≤ localEight r := by
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change nativeMask k.val * a j * (nativeMask k.val)⁻¹ ∈ localEight r
    rw [hm j]
    change nativeMask k.val * (nativeMask (m j).val * correctedGenerator r j) *
      (nativeMask k.val)⁻¹ ∈ localEight r
    rw [kernel_conjugate_shift]
    have hmem := fixed_mem_eight r _ (hfixed j)
    change nativeMask ((m j).val ^^^ (k.val ^^^ starMask (starElement (correctedIndex r j)) k.val)) ∈ localEight r at hmem
    exact (localEight r).mul_mem hmem (correctedGenerator_mem_localEight r j)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hB
  have hBp : B.map π = pairRowImage (r.castLE (by decide)) := by
    change (closure (Set.range (fun j => g * a j * g⁻¹))).map π = _
    rw [MonoidHom.map_closure,← Set.range_comp]
    congr 2
    funext j
    change π (g * a j * g⁻¹) = pairRowGenerator (r.castLE (by decide)) j
    rw [map_mul,map_mul,map_inv,show π g = 1 from nativeMask_projection _,one_mul,inv_one,mul_one,hp j]
    fin_cases r <;> fin_cases j <;> rfl
  have hCB : centralizer (B : Set L) = localEight r := by
    have hle : localEight r ≤ centralizer (B : Set L) :=
      (localEight r).le_centralizer.trans (centralizer_le hB)
    apply (eq_of_le_of_card_ge hle ?_).symm
    rw [selected_local_centralizer_card B r hBp,localEight_card]
  have hBA : B ≤ A.map (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (ha j)
  refine ⟨k,hk,eq_of_le_of_card_ge ?_ ?_⟩
  · rw [map_centralizer_equiv]
    exact (centralizer_le hBA).trans hCB.le
  · rw [card_map_of_injective (MulAut.conj g).injective,
      selected_local_centralizer_card A r hrow,localEight_card]

/-- The selected source-row centralizer calculation for an arbitrary ambient
elementary subgroup, retaining the original seed and quotient projection. -/
theorem ambient_centralizer_conjugacy (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    ∃ k : Fin 2048, (k = 0 ∨ k = twist r) ∧
      (centralizer (X : Set Model)).map
        (MulAut.conj ((nativeMask k.val : L) : Model)).toMonoidHom = nativeEight r := by
  let : IsElementaryAbelian 2 (X.subgroupOf L) := IsElementaryAbelian.subgroupOf hXL
  obtain ⟨k,hk,he⟩ := local_centralizer_conjugacy (X.subgroupOf L) r hrow
  refine ⟨k,hk,?_⟩
  rw [seed_ambient_centralizer_map X hXL hs,Subgroup.map_map]
  have hc : (MulAut.conj ((nativeMask k.val : L) : Model)).toMonoidHom.comp (L).subtype =
      (L).subtype.comp (MulAut.conj (nativeMask k.val)).toMonoidHom := by
    ext x
    rfl
  rw [hc,← Subgroup.map_map,he]
  rfl


private theorem primed_image_generators :
    closure (Set.range (fun j : Fin 3 => starElement (correctedIndex 1 j.succ))) = pairRowImage 3 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : starElement (correctedIndex 1 j.succ) = pairRowGenerator 3 j.succ := by
      fin_cases j <;> rfl
    change starElement (correctedIndex 1 j.succ) ∈ pairRowImage 3
    rw [he]
    exact pairRowGenerator_mem _ _
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · exact one_mem _
    · exact subset_closure (Set.mem_range_self 0)
    · exact subset_closure (Set.mem_range_self 1)
    · exact subset_closure (Set.mem_range_self 2)

private theorem primed_kernel_equation (B : Subgroup L) (hBp : B.map π = pairRowImage 3) :
    ((centralizer (B : Set L)).subgroupOf E).map (E).subtype = centralKernel 1 := by
  unfold centralKernel
  congr 1
  ext x
  obtain ⟨m,rfl⟩ := (e).surjective x
  change (e m : L) ∈ centralizer (B : Set L) ↔ (e m : L) ∈ centralizer (liftClosure 1 : Set L)
  rw [mask_mem_pairRow_centralizer_iff _ _ hBp,
    mask_mem_pairRow_centralizer_iff _ _ (liftClosure_projection 1)]
  rfl

private theorem primed_local_centralizer_of_le (B : Subgroup L)
    (hB : B ≤ localEight 1) (hBp : B.map π = pairRowImage 3) :
    centralizer (B : Set L) = localEight 1 := by
  have hle : localEight 1 ≤ centralizer (B : Set L) :=
    (localEight 1).le_centralizer.trans (centralizer_le hB)
  apply le_antisymm ?_ hle
  intro g hg
  have hp : π g ∈ pairRowImage 1 := by
    rw [← primed_d_quotient_centralizer]
    intro p hp
    rw [← hBp] at hp
    obtain ⟨a,ha,rfl⟩ := hp
    exact (map_mul π a g).symm.trans ((congrArg π (hg a ha)).trans (map_mul π g a))
  change π g ∈ pairRowImage ((1 : Fin 2).castLE (by decide)) at hp
  rw [← liftClosure_projection 1] at hp
  obtain ⟨a,ha,he⟩ := hp
  have ha8 : a ∈ localEight 1 := (show liftClosure 1 ≤ localEight 1 from le_sup_left) ha
  have hk : g * a⁻¹ ∈ E := by
    rw [← starProjection_ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
  have hc : g * a⁻¹ ∈ centralizer (B : Set L) :=
    (centralizer _).mul_mem hg ((centralizer _).inv_mem (hle ha8))
  have hm : g * a⁻¹ ∈ centralKernel 1 := by
    rw [← primed_kernel_equation B hBp]
    exact ⟨⟨g * a⁻¹,hk⟩,hc,rfl⟩
  have hh := (localEight 1).mul_mem ((show centralKernel 1 ≤ localEight 1 from le_sup_right) hm) ha8
  simpa only [inv_mul_cancel_right] using hh

/-- The full centralizer for an arbitrary elementary lift of the omitted-
generator (d') row is one of two literal kernel conjugates of the native eight. -/
theorem primed_local_centralizer_conjugacy (A : Subgroup L) [IsElementaryAbelian 2 A]
    (hrow : A.map π = pairRowImage 3) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧
      (centralizer (A : Set L)).map (MulAut.conj (nativeMask k.val)).toMonoidHom = localEight 1 := by
  have hex (j : Fin 3) : ∃ a ∈ A, π a = starElement (correctedIndex 1 j.succ) := by
    have h := pairRowGenerator_mem 3 j.succ
    rw [← hrow] at h
    obtain ⟨a,ha,he⟩ := h
    refine ⟨a,ha,he.trans ?_⟩
    fin_cases j <;> rfl
  choose a ha hp using hex
  have hf (j : Fin 3) := (correctedLift_fibre (correctedIndex 1 j.succ) (a j)).mp (hp j)
  choose m hm huniq using hf
  have hs (j : Fin 3) : maskImage (rows 1 j.succ) (m j).val = (m j).val := by
    rw [← action_eq]
    apply shifted_square
    rw [← hm j]
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (a j) (ha j)
  have hc (i j : Fin 3) : maskImage (rows 1 i.succ) (m j).val ^^^ (m j).val =
      maskImage (rows 1 j.succ) (m i).val ^^^ (m i).val := by
    rw [← action_eq,← action_eq]
    apply shifted_commute _ _ _ _ (correctedGenerator_commute 1 i.succ j.succ)
    rw [← hm i,← hm j]
    exact setLike_mul_comm (ha i) (ha j)
  obtain ⟨k,hk,hfixed⟩ := primed_correction m hs hc
  let g := nativeMask k.val
  let B : Subgroup L := closure (Set.range (fun j => g * a j * g⁻¹))
  have hB : B ≤ localEight 1 := by
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    change nativeMask k.val * a j * (nativeMask k.val)⁻¹ ∈ localEight 1
    rw [hm j]
    change nativeMask k.val * (nativeMask (m j).val * correctedGenerator 1 j.succ) *
      (nativeMask k.val)⁻¹ ∈ localEight 1
    rw [kernel_conjugate_shift]
    have hmem := fixed_mem_eight 1 _ (hfixed j)
    change nativeMask ((m j).val ^^^ (k.val ^^^ starMask (starElement (correctedIndex 1 j.succ)) k.val)) ∈ localEight 1 at hmem
    exact (localEight 1).mul_mem hmem (correctedGenerator_mem_localEight 1 j.succ)
  have hBp : B.map π = pairRowImage 3 := by
    change (closure (Set.range (fun j => g * a j * g⁻¹))).map π = _
    rw [MonoidHom.map_closure,← Set.range_comp,← primed_image_generators]
    congr 2
    funext j
    change π (g * a j * g⁻¹) = starElement (correctedIndex 1 j.succ)
    rw [map_mul,map_mul,map_inv,show π g = 1 from nativeMask_projection _,one_mul,inv_one,mul_one,hp j]
  have hCB := primed_local_centralizer_of_le B hB hBp
  have hBA : B ≤ A.map (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (ha j)
  have hupper : (centralizer (A : Set L)).map (MulAut.conj g).toMonoidHom ≤ localEight 1 := by
    rw [map_centralizer_equiv]
    exact (centralizer_le hBA).trans hCB.le
  have hAlow : A.map (MulAut.conj g).toMonoidHom ≤ localEight 1 :=
    (Subgroup.map_mono A.le_centralizer).trans hupper
  refine ⟨k,hk,le_antisymm hupper ?_⟩
  rw [map_centralizer_equiv]
  exact (localEight 1).le_centralizer.trans (centralizer_le hAlow)

/-- The arbitrary primed-row centralizer, with the original ambient seed and
the full literal quotient image retained. -/
theorem primed_ambient_centralizer_conjugacy (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (hrow : (X.subgroupOf L).map π = pairRowImage 3) :
    ∃ k : Fin 2048, (k = 0 ∨ k = 16) ∧
      (centralizer (X : Set Model)).map
        (MulAut.conj ((nativeMask k.val : L) : Model)).toMonoidHom = nativeEight 1 := by
  let : IsElementaryAbelian 2 (X.subgroupOf L) := IsElementaryAbelian.subgroupOf hXL
  obtain ⟨k,hk,he⟩ := primed_local_centralizer_conjugacy (X.subgroupOf L) hrow
  refine ⟨k,hk,?_⟩
  rw [seed_ambient_centralizer_map X hXL hs,Subgroup.map_map]
  have hc : (MulAut.conj ((nativeMask k.val : L) : Model)).toMonoidHom.comp (L).subtype =
      (L).subtype.comp (MulAut.conj (nativeMask k.val)).toMonoidHom := by
    ext x
    rfl
  rw [hc,← Subgroup.map_map,he]
  rfl

end Janko4.LocalStructure.ElementaryEightGeometry.Sections
