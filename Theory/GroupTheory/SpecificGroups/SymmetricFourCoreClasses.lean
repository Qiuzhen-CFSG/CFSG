module
public import Theory.GroupTheory.SpecificGroups.SymmetricFourCentralNormal
public import Theory.GroupTheory.PCoreProduct

/-!
# Eight marked conjugacy orbits in the two-core of E4 × S4

The two-core is the product of the central four-group and the normal Klein
four in S4. Two independent central involutions and one noncentral core
involution give eight conjugacy representatives: four singleton orbits and
four triples. Two explicit membership patterns consequently contain five
and nine elements. The count transports through any injective realization,
so callers retain their original ambient conjugacy predicate. The marked
plane short class and its root translate meet in the pair t,tz once the
root has nontrivial central coordinate; that source marking stays explicit.

Only the four-element coordinates and the known Klein-four conjugacy action
are used. This is the endpoint calculation behind Aschbacher--Smith F.5.3(8),
printed p.300.
-/

@[expose] public section
namespace SymmetricFourCoreClasses
open Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
abbrev C2 := Multiplicative (ZMod 2)
abbrev C4 := C2 × C2
abbrev Model := C4 × Equiv.Perm (Fin 4)
private instance : Fintype C4 := inferInstance
private instance : DecidableEq C4 := inferInstance
private instance : Fintype core := inferInstance
private instance : DecidableEq core := inferInstance
def Core : Subgroup Model := (⊤ : Subgroup C4).prod core

theorem core_eq : Core = pCore 2 Model := by
  rw [pCore_prod,←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
  have hp : IsPGroup 2 C4 := IsPGroup.of_card (n := 2) (by norm_num [Nat.card_eq_fintype_card])
  rw [show pCore 2 C4 = ⊤ from top_unique (le_sSup ⟨inferInstance,hp.of_equiv (Subgroup.topEquiv).symm⟩)]
  rfl

private theorem center_pair_cases : ∀ (a b v : C4), a≠1 → b≠1 → a≠b →
    v=1 ∨ v=a ∨ v=b ∨ v=a*b := by decide +kernel

private theorem center_coordinates (x : Model) (hx : x∈center Model) : x.2=1 :=
  (SymmetricFourCentralNormal.center_eq.le hx).2

private theorem core_coordinates_conjugate (x y : Model) (hx : x∈Core) (hy : y∈Core)
    (he : x.1=y.1) (hx1 : x.2≠1) (hy1 : y.2≠1) : IsConj x y := by
  obtain ⟨g,hg⟩ := core_conjugate x.2 hx.2 hx1 y.2 hy.2 hy1
  apply isConj_iff.mpr
  refine ⟨(1,g),?_⟩
  exact Prod.ext (by simpa using he) hg

private theorem shift_cases (a b d v : C4) (ha : a≠1) (hb : b≠1) (hab : a≠b) :
    v=d ∨ v=a*d ∨ v=b*d ∨ v=a*b*d := by
  exact (by decide : ∀ (a b d v : C4), a≠1 → b≠1 → a≠b →
    v=d ∨ v=a*d ∨ v=b*d ∨ v=a*b*d) a b d v ha hb hab

private theorem core_rows (a b d x : Model)
    (ha : a∈center Model) (hb : b∈center Model)
    (ha1 : a≠1) (hb1 : b≠1) (hab : a≠b)
    (hd : d∈Core) (hdZ : d∉center Model) (hx : x∈Core) :
    x=1 ∨ x=a ∨ x=b ∨ x=a*b ∨
    IsConj d x ∨ IsConj (a*d) x ∨ IsConj (b*d) x ∨ IsConj (a*b*d) x := by
  have ha2 := center_coordinates a ha
  have hb2 := center_coordinates b hb
  have hac : a.1≠1 := fun he => ha1 (Prod.ext he ha2)
  have hbc : b.1≠1 := fun he => hb1 (Prod.ext he hb2)
  have habc : a.1≠b.1 := fun he => hab (Prod.ext he (ha2.trans hb2.symm))
  have hd2 : d.2≠1 := by
    intro he
    apply hdZ
    rw [SymmetricFourCentralNormal.center_eq]
    exact ⟨mem_top _,he⟩
  have haC : a∈Core := ⟨mem_top _,ha2 ▸ one_mem _⟩
  have hbC : b∈Core := ⟨mem_top _,hb2 ▸ one_mem _⟩
  by_cases hx2 : x.2=1
  · rcases center_pair_cases a.1 b.1 x.1 hac hbc habc with he | he | he | he
    · exact Or.inl (Prod.ext he hx2)
    · exact Or.inr (Or.inl (Prod.ext he (hx2.trans ha2.symm)))
    · exact Or.inr (Or.inr (Or.inl (Prod.ext he (hx2.trans hb2.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext he (by simp [ha2,hb2,hx2])))))
  · right; right; right; right
    rcases shift_cases a.1 b.1 d.1 x.1 hac hbc habc with he | he | he | he
    · exact Or.inl (core_coordinates_conjugate d x hd hx he.symm hd2 hx2)
    · exact Or.inr (Or.inl (core_coordinates_conjugate (a*d) x (Core.mul_mem haC hd) hx he.symm
        (by simpa [ha2] using hd2) hx2))
    · exact Or.inr (Or.inr (Or.inl (core_coordinates_conjugate (b*d) x (Core.mul_mem hbC hd) hx he.symm
        (by simpa [hb2] using hd2) hx2)))
    · exact Or.inr (Or.inr (Or.inr (core_coordinates_conjugate (a*b*d) x
        (Core.mul_mem (Core.mul_mem haC hbC) hd) hx he.symm (by simpa [ha2,hb2] using hd2) hx2)))


private def pattern (plane : Bool) (a b d : C4) (x : Model) : Prop :=
  if x.2=1 then if plane then False else x.1=b ∨ x.1=a*b
  else if plane then x.1=d ∨ x.1=a*d ∨ x.1=a*b*d else x.1=a*b*d
private instance (plane : Bool) (a b d : C4) (x : Model) : Decidable (pattern plane a b d x) := by
  unfold pattern
  infer_instance

private theorem pattern_conj (plane : Bool) (a b d : C4) (x y : Model)
    (h : IsConj x y) : pattern plane a b d x ↔ pattern plane a b d y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  have hfirst : (g*x*g⁻¹).1=x.1 := by simp
  have hsecond : (g*x*g⁻¹).2=1 ↔ x.2=1 := by simp
  simp only [pattern,hfirst,hsecond]

private theorem pattern_rows_test : ∀ (plane : Bool) (a b d : C4) (v : core),
    a≠1 → b≠1 → a≠b → v.val≠1 →
    ¬ pattern plane a b d 1 ∧ ¬ pattern plane a b d (a,1) ∧
    (pattern plane a b d (b,1) ↔ plane=false) ∧
    (pattern plane a b d (a*b,1) ↔ plane=false) ∧
    (pattern plane a b d (d,v.val) ↔ plane=true) ∧
    (pattern plane a b d (a*d,v.val) ↔ plane=true) ∧
    ¬ pattern plane a b d (b*d,v.val) ∧
    pattern plane a b d (a*b*d,v.val) := by decide +kernel

private theorem pattern_card_test : ∀ (plane : Bool) (a b d : C4),
    a≠1 → b≠1 → a≠b →
    (Finset.univ.filter (fun x : C4 × core => pattern plane a b d (x.1,x.2.val))).card =
      if plane then 9 else 5 := by decide +kernel

private def coreEquiv : Core ≃ C4 × core where
  toFun x := (x.val.1,⟨x.val.2,x.property.2⟩)
  invFun x := ⟨(x.1,x.2.val),⟨mem_top _,x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A conjugacy-invariant predicate on the endpoint two-core is counted by
its eight marked orbits: four central singletons and four triples. -/
theorem predicate_card (plane : Bool) (P : Model → Prop)
    (hP : ∀ x y, IsConj x y → (P x ↔ P y)) (a b d : Model)
    (ha : a∈center Model) (hb : b∈center Model)
    (ha1 : a≠1) (hb1 : b≠1) (hab : a≠b)
    (hd : d∈Core) (hdZ : d∉center Model)
    (h1 : ¬P 1) (hPa : ¬P a) (hPb : P b ↔ plane=false)
    (hPab : P (a*b) ↔ plane=false) (hPd : P d ↔ plane=true)
    (hPad : P (a*d) ↔ plane=true) (hPbd : ¬P (b*d)) (hPabd : P (a*b*d)) :
    Nat.card {x : Core // P x.val} = if plane then 9 else 5 := by
  classical
  have ha2 := center_coordinates a ha
  have hb2 := center_coordinates b hb
  have hac : a.1≠1 := fun he => ha1 (Prod.ext he ha2)
  have hbc : b.1≠1 := fun he => hb1 (Prod.ext he hb2)
  have habc : a.1≠b.1 := fun he => hab (Prod.ext he (ha2.trans hb2.symm))
  have hd2 : d.2≠1 := by
    intro he
    apply hdZ
    rw [SymmetricFourCentralNormal.center_eq]
    exact ⟨mem_top _,he⟩
  have hr := pattern_rows_test plane a.1 b.1 d.1 ⟨d.2,hd.2⟩ hac hbc habc hd2
  have har : (a.1,1)=a := Prod.ext rfl ha2.symm
  have hbr : (b.1,1)=b := Prod.ext rfl hb2.symm
  have habr : (a.1*b.1,1)=a*b := Prod.ext rfl (by simp [ha2,hb2])
  have hadr : (a.1*d.1,d.2)=a*d := Prod.ext rfl (by simp [ha2])
  have hbdr : (b.1*d.1,d.2)=b*d := Prod.ext rfl (by simp [hb2])
  have habdr : (a.1*b.1*d.1,d.2)=a*b*d := Prod.ext rfl (by simp [ha2,hb2])
  rw [har,hbr,habr,hadr,hbdr,habdr] at hr
  have he (x : Core) : P x.val ↔ pattern plane a.1 b.1 d.1 x.val := by
    rcases core_rows a b d x.val ha hb ha1 hb1 hab hd hdZ x.property with
      hx | hx | hx | hx | hx | hx | hx | hx
    · rw [hx]
      exact iff_of_false h1 hr.1
    · rw [hx]
      exact iff_of_false hPa hr.2.1
    · rw [hx]
      exact hPb.trans hr.2.2.1.symm
    · rw [hx]
      exact hPab.trans hr.2.2.2.1.symm
    · exact (hP d x.val hx).symm.trans (hPd.trans
        (hr.2.2.2.2.1.symm.trans (pattern_conj plane a.1 b.1 d.1 d x.val hx)))
    · exact (hP (a*d) x.val hx).symm.trans (hPad.trans
        (hr.2.2.2.2.2.1.symm.trans (pattern_conj plane a.1 b.1 d.1 (a*d) x.val hx)))
    · exact iff_of_false (fun hh => hPbd ((hP (b*d) x.val hx).mpr hh))
        (fun hh => hr.2.2.2.2.2.2.1 ((pattern_conj plane a.1 b.1 d.1 (b*d) x.val hx).mpr hh))
    · exact iff_of_true ((hP (a*b*d) x.val hx).mp hPabd)
        ((pattern_conj plane a.1 b.1 d.1 (a*b*d) x.val hx).mp hr.2.2.2.2.2.2.2)
  let e : {x : Core // P x.val} ≃
      {x : C4 × core // pattern plane a.1 b.1 d.1 (x.1,x.2.val)} := {
    toFun x := ⟨coreEquiv x.val,(he x.val).mp x.property⟩
    invFun x := ⟨coreEquiv.symm x.val,(he _).mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact pattern_card_test plane a.1 b.1 d.1 hac hbc habc



/-- Two distinct nonidentity central involutions exhaust the four-group center. -/
theorem center_cases (a b x : Model) (ha : a∈center Model) (hb : b∈center Model)
    (ha1 : a≠1) (hb1 : b≠1) (hab : a≠b) (hx : x∈center Model) :
    x=1 ∨ x=a ∨ x=b ∨ x=a*b := by
  have ha2 := center_coordinates a ha
  have hb2 := center_coordinates b hb
  have hx2 := center_coordinates x hx
  have hac : a.1≠1 := fun he => ha1 (Prod.ext he ha2)
  have hbc : b.1≠1 := fun he => hb1 (Prod.ext he hb2)
  have habc : a.1≠b.1 := fun he => hab (Prod.ext he (ha2.trans hb2.symm))
  rcases center_pair_cases a.1 b.1 x.1 hac hbc habc with he | he | he | he
  · exact Or.inl (Prod.ext he hx2)
  · exact Or.inr (Or.inl (Prod.ext he (hx2.trans ha2.symm)))
  · exact Or.inr (Or.inr (Or.inl (Prod.ext he (hx2.trans hb2.symm))))
  · exact Or.inr (Or.inr (Or.inr (Prod.ext he (by simp [hx2,ha2,hb2]))))

/-- The endpoint two-core is self-centralizing in E4×S4. -/
theorem centralizer_core : centralizer (Core : Set Model)=Core := by
  ext x
  constructor
  · intro hx
    refine ⟨mem_top _,?_⟩
    rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.centralizer_core]
    intro y hy
    exact congrArg Prod.snd (mem_centralizer_iff.mp hx (1,y) ⟨mem_top _,hy⟩)
  · intro hx y hy
    apply Prod.ext
    · exact mul_comm _ _
    · exact congrArg Subtype.val
        ((inferInstance : IsElementaryAbelian 2 core).is_comm.comm
          (⟨y.2,hy.2⟩ : core) ⟨x.2,hx.2⟩)



/-- Injective realization preserves the eight-orbit count. -/
theorem predicate_card_map {G : Type*} [Group G] (j : Model →* G)
    (hj : Function.Injective j) (plane : Bool) (P : G → Prop)
    (hP : ∀ x y, IsConj x y → (P x ↔ P y)) (a b d : Model)
    (ha : a∈center Model) (hb : b∈center Model)
    (ha1 : a≠1) (hb1 : b≠1) (hab : a≠b)
    (hd : d∈Core) (hdZ : d∉center Model)
    (h1 : ¬P 1) (hPa : ¬P (j a)) (hPb : P (j b) ↔ plane=false)
    (hPab : P (j (a*b)) ↔ plane=false) (hPd : P (j d) ↔ plane=true)
    (hPad : P (j (a*d)) ↔ plane=true) (hPbd : ¬P (j (b*d))) (hPabd : P (j (a*b*d))) :
    Nat.card {x : Core.map j // P x.val} = if plane then 9 else 5 := by
  let e := Core.equivMapOfInjective j hj
  let d : {x : Core // P (j x.val)} ≃ {x : Core.map j // P x.val} := {
    toFun x := ⟨e x.val,x.property⟩
    invFun x := ⟨e.symm x.val,by
      have he := congrArg Subtype.val (e.apply_symm_apply x.val)
      change j (e.symm x.val).val = x.val.val at he
      rw [he]
      exact x.property⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x.val)
    right_inv x := Subtype.ext (e.apply_symm_apply x.val) }
  rw [←Nat.card_congr d]
  exact predicate_card plane (P ∘ j) (fun x y h => hP _ _ (j.map_isConj h)) a b _
    ha hb ha1 hb1 hab hd hdZ (by simpa only [Function.comp_apply,map_one] using h1)
    hPa hPb hPab hPd hPad hPbd hPabd


private def shortPattern (b d : C4) (x : Model) : Prop :=
  if x.2=1 then x.1≠1 else x.1=b*d
private instance (b d : C4) (x : Model) : Decidable (shortPattern b d x) := by
  unfold shortPattern
  infer_instance

private theorem short_pattern_conj (b d : C4) (x y : Model)
    (h : IsConj x y) : shortPattern b d x ↔ shortPattern b d y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  have hfirst : (g*x*g⁻¹).1=x.1 := by simp
  have hsecond : (g*x*g⁻¹).2=1 ↔ x.2=1 := by simp
  simp only [shortPattern,hfirst,hsecond]

private theorem short_pattern_rows_test : ∀ (a b d : C4) (v : core),
    a≠1 → b≠1 → a≠b → v.val≠1 →
    ¬ shortPattern b d 1 ∧ shortPattern b d (a,1) ∧
    shortPattern b d (b,1) ∧ shortPattern b d (a*b,1) ∧
    ¬ shortPattern b d (d,v.val) ∧ ¬ shortPattern b d (a*d,v.val) ∧
    shortPattern b d (b*d,v.val) ∧ ¬ shortPattern b d (a*b*d,v.val) := by
  intro a b d v ha hb hab hv
  have hab1 : a*b≠1 := (by decide : ∀ a b : C4, a≠b → a*b≠1) a b hab
  simp [shortPattern,hv,ha,hb,hab,hab1]


private theorem short_pattern_pair_test : ∀ (a b d u : C4) (v w : core),
    a≠1 → b≠1 → a≠b → d≠1 → v.val≠1 →
    (shortPattern b d (u,w.val) ∧ shortPattern b d ((d,v.val)*(u,w.val)) ↔
      (u,w.val)=(b,1) ∨ (u,w.val)=(b*d,v.val)) := by
  unfold shortPattern
  simp only [Prod.ext_iff,Prod.fst_mul,Prod.snd_mul]
  decide +kernel

/-- The plane short class and its root translate meet in the pair t,tz.
The nontrivial central coordinate is the literal long-root marking. -/
theorem predicate_plane_pair (P : Model → Prop)
    (hP : ∀ x y, IsConj x y → (P x ↔ P y)) (a b d x : Model)
    (ha : a∈center Model) (hb : b∈center Model)
    (ha1 : a≠1) (hb1 : b≠1) (hab : a≠b)
    (hd : d∈Core) (hdZ : d∉center Model) (hd1 : d.1≠1) (hx : x∈Core)
    (h1 : ¬P 1) (hPa : P a) (hPb : P b) (hPab : P (a*b))
    (hPd : ¬P d) (hPad : ¬P (a*d)) (hPbd : P (b*d)) (hPabd : ¬P (a*b*d)) :
    (P x ∧ P (d*x)) ↔ x=b ∨ x=b*d := by
  have ha2 := center_coordinates a ha
  have hb2 := center_coordinates b hb
  have hac : a.1≠1 := fun he => ha1 (Prod.ext he ha2)
  have hbc : b.1≠1 := fun he => hb1 (Prod.ext he hb2)
  have habc : a.1≠b.1 := fun he => hab (Prod.ext he (ha2.trans hb2.symm))
  have hd2 : d.2≠1 := by
    intro he
    apply hdZ
    rw [SymmetricFourCentralNormal.center_eq]
    exact ⟨mem_top _,he⟩
  have hr := short_pattern_rows_test a.1 b.1 d.1 ⟨d.2,hd.2⟩ hac hbc habc hd2
  have har : (a.1,1)=a := Prod.ext rfl ha2.symm
  have hbr : (b.1,1)=b := Prod.ext rfl hb2.symm
  have habr : (a.1*b.1,1)=a*b := Prod.ext rfl (by simp [ha2,hb2])
  have hadr : (a.1*d.1,d.2)=a*d := Prod.ext rfl (by simp [ha2])
  have hbdr : (b.1*d.1,d.2)=b*d := Prod.ext rfl (by simp [hb2])
  have habdr : (a.1*b.1*d.1,d.2)=a*b*d := Prod.ext rfl (by simp [ha2,hb2])
  rw [har,hbr,habr,hadr,hbdr,habdr] at hr
  have he (u : Model) (hu : u∈Core) : P u ↔ shortPattern b.1 d.1 u := by
    rcases core_rows a b d u ha hb ha1 hb1 hab hd hdZ hu with
      hu | hu | hu | hu | hu | hu | hu | hu
    · rw [hu]; exact iff_of_false h1 hr.1
    · rw [hu]; exact iff_of_true hPa hr.2.1
    · rw [hu]; exact iff_of_true hPb hr.2.2.1
    · rw [hu]; exact iff_of_true hPab hr.2.2.2.1
    · exact iff_of_false (fun hh => hPd ((hP d u hu).mpr hh))
        (fun hh => hr.2.2.2.2.1 ((short_pattern_conj b.1 d.1 d u hu).mpr hh))
    · exact iff_of_false (fun hh => hPad ((hP (a*d) u hu).mpr hh))
        (fun hh => hr.2.2.2.2.2.1 ((short_pattern_conj b.1 d.1 (a*d) u hu).mpr hh))
    · exact iff_of_true ((hP (b*d) u hu).mp hPbd)
        ((short_pattern_conj b.1 d.1 (b*d) u hu).mp hr.2.2.2.2.2.2.1)
    · exact iff_of_false (fun hh => hPabd ((hP (a*b*d) u hu).mpr hh))
        (fun hh => hr.2.2.2.2.2.2.2 ((short_pattern_conj b.1 d.1 (a*b*d) u hu).mpr hh))
  rw [he x hx,he (d*x) (Core.mul_mem hd hx)]
  have hh := short_pattern_pair_test a.1 b.1 d.1 x.1 ⟨d.2,hd.2⟩ ⟨x.2,hx.2⟩
    hac hbc habc hd1 hd2
  simpa only [Prod.eta,hbr,hbdr] using hh

end SymmetricFourCoreClasses
