module
public import Theory.Combinatorics.TranslationPlane.Coordinates

/-!
# Completing an affine incidence equivalence

An incidence equivalence off a marked line extends to both full projective
fibers. Affine traces distinguish lines, and parallelism recovers incidence
at infinity. Counting affine points identifies the two orders, so images
of affine lines already give a bijection of all lines. The extension
preserves the original affine map and the marked line literally.

This elementary completion argument is used in the one-field recognition
route for DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224. It holds
also for planes of order two.
-/

@[expose] public noncomputable section
namespace Configuration.TranslationPlane
variable {P L : Type*} [Membership P L] [Finite P] [Finite L] [ProjectivePlane P L]

/-- Every non-infinity line has two distinct affine points, even at order two. -/
theorem exists_two_affine_points (l m : L) (hm : m ≠ l) :
    ∃ p q : P, p ∈ m ∧ p ∉ l ∧ q ∈ m ∧ q ∉ l ∧ p ≠ q := by
  have hc : 1 < Nat.card {p : P // p ∈ m ∧ p ∉ l} := by
    rw [card_line_off_axis l m (HasPoints.mkPoint hm)
      (HasPoints.mkPoint_ax hm).2 (HasPoints.mkPoint_ax hm).1 hm]
    exact ProjectivePlane.one_lt_order P L
  let : Nontrivial {p : P // p ∈ m ∧ p ∉ l} := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨p,q,hpq⟩ := exists_pair_ne {p : P // p ∈ m ∧ p ∉ l}
  exact ⟨p,q,p.property.1,p.property.2,q.property.1,q.property.2,
    fun he => hpq (Subtype.ext he)⟩

/-- Affine incidence already distinguishes all projective lines. -/
theorem line_eq_of_affine (l : L) {m n : L}
    (h : ∀ p : P, p ∉ l → (p ∈ m ↔ p ∈ n)) : m = n := by
  by_cases hm : m = l
  · subst m
    by_contra hn
    obtain ⟨p,_,hp,hpl,_,_,_⟩ := exists_two_affine_points l n (Ne.symm hn)
    exact hpl ((h p hpl).mpr hp)
  · obtain ⟨p,q,hpm,hpl,hqm,hql,hpq⟩ := exists_two_affine_points l m hm
    exact (Nondegenerate.eq_or_eq hpm hqm ((h p hpl).mp hpm)
      ((h q hql).mp hqm)).resolve_left hpq

omit [Finite P] [Finite L] in
/-- Parallelism is exactly incidence at a common point of the deleted line. -/
theorem infinity_incident_iff (l : L) {m n : L} {p : P}
    (hm : m ≠ l) (_hn : n ≠ l) (hpl : p ∈ l) (hpm : p ∈ m) :
    p ∈ n ↔ m = n ∨ ¬ ∃ q : P, q ∉ l ∧ q ∈ m ∧ q ∈ n := by
  constructor
  · intro hpn
    by_cases hmn : m = n
    · exact Or.inl hmn
    · refine Or.inr ?_
      rintro ⟨q,hql,hqm,hqn⟩
      have hqp := (Nondegenerate.eq_or_eq hqm hpm hqn hpn).resolve_right hmn
      exact hql (hqp ▸ hpl)
  · rintro (rfl | hno)
    · exact hpm
    · by_cases hmn : m = n
      · exact hmn ▸ hpm
      let q : P := HasPoints.mkPoint hmn
      have hqm : q ∈ m := (HasPoints.mkPoint_ax hmn).1
      have hqn : q ∈ n := (HasPoints.mkPoint_ax hmn).2
      have hql : q ∈ l := by
        by_contra hq
        exact hno ⟨q,hq,hqm,hqn⟩
      have hqp := (Nondegenerate.eq_or_eq hqm hpm hql hpl).resolve_right hm
      exact hqp ▸ hqn

private theorem point_ext (p q : P) (h : ∀ m : L, p ∈ m ↔ q ∈ m) : p = q := by
  have hc : 1 < Nat.card {m : L // p ∈ m} :=
    lt_trans (by decide) (ProjectivePlane.two_lt_lineCount L p)
  let : Nontrivial {m : L // p ∈ m} := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨m,n,hmn⟩ := exists_pair_ne {m : L // p ∈ m}
  exact (Nondegenerate.eq_or_eq m.property ((h m).mp m.property)
    n.property ((h n).mp n.property)).resolve_right (fun he => hmn (Subtype.ext he))

variable {P' L' : Type*} [Membership P' L'] [Finite P'] [Finite L']
  [ProjectivePlane P' L']
variable (l : L) (l' : L')
  (e : {p : P // p ∉ l} ≃ {p : P' // p ∉ l'})
  (f : L ≃ L') (hf : f l = l')
  (hi : ∀ (p : {p : P // p ∉ l}) (m : L), (e p).val ∈ f m ↔ p.val ∈ m)

include hi in
omit [Finite P] [Finite L] [ProjectivePlane P L] [Finite P'] [Finite L'] [ProjectivePlane P' L'] in
private theorem affine_meet_iff (m n : L) :
    (∃ q : P', q ∉ l' ∧ q ∈ f m ∧ q ∈ f n) ↔
      ∃ q : P, q ∉ l ∧ q ∈ m ∧ q ∈ n := by
  constructor
  · rintro ⟨q,hql,hqm,hqn⟩
    let p := e.symm ⟨q,hql⟩
    have he : e p = ⟨q,hql⟩ := e.apply_symm_apply _
    exact ⟨p,p.property,(hi p m).mp (by simpa only [he] using hqm),
      (hi p n).mp (by simpa only [he] using hqn)⟩
  · rintro ⟨p,hpl,hpm,hpn⟩
    exact ⟨e ⟨p,hpl⟩,(e ⟨p,hpl⟩).property,(hi ⟨p,hpl⟩ m).mpr hpm,
      (hi ⟨p,hpl⟩ n).mpr hpn⟩

include hf hi in
omit [Finite P] [Finite L] [Finite P'] [Finite L'] in
/-- An affine incidence equivalence determines every point at infinity. -/
theorem exists_infinity_image (o : {p : P // p ∉ l}) (p : P) (hp : p ∈ l) :
    ∃ p' : P', p' ∈ l' ∧ ∀ m : L, p' ∈ f m ↔ p ∈ m := by
  have hop : o.val ≠ p := fun he => o.property (he ▸ hp)
  let m : L := HasLines.mkLine hop
  have hom : o.val ∈ m := (HasLines.mkLine_ax hop).1
  have hpm : p ∈ m := (HasLines.mkLine_ax hop).2
  have hm : m ≠ l := fun he => o.property ((congrArg (o.val ∈ ·) he).mp hom)
  have hfm : f m ≠ l' := fun he => hm (f.injective (he.trans hf.symm))
  let p' : P' := HasPoints.mkPoint hfm
  have hpfm : p' ∈ f m := (HasPoints.mkPoint_ax hfm).1
  have hpl' : p' ∈ l' := (HasPoints.mkPoint_ax hfm).2
  refine ⟨p',hpl',?_⟩
  intro n
  by_cases hn : n = l
  · subst n
    simp only [hf, hpl', hp]
  · have hfn : f n ≠ l' := fun he => hn (f.injective (he.trans hf.symm))
    rw [infinity_incident_iff l' hfm hfn hpl' hpfm,
      infinity_incident_iff l hm hn hp hpm, f.injective.eq_iff,
      affine_meet_iff l l' e f hi]

include hf hi in
/-- Extend an affine incidence identification to the complete projective plane.
The affine chart and the marked infinity line are preserved literally. -/
theorem exists_projective_extension (o : {p : P // p ∉ l}) :
    ∃ ep : P ≃ P', (∀ p m, ep p ∈ f m ↔ p ∈ m) ∧
      ∀ p : {p : P // p ∉ l}, ep p.val = (e p).val := by
  classical
  have hex (p : P) : ∃ p' : P', ∀ m : L, p' ∈ f m ↔ p ∈ m := by
    by_cases hp : p ∈ l
    · obtain ⟨p',_,h⟩ := exists_infinity_image l l' e f hf hi o p hp
      exact ⟨p',h⟩
    · exact ⟨e ⟨p,hp⟩,hi ⟨p,hp⟩⟩
  let ep : P → P' := fun p => (hex p).choose
  have hep (p : P) (m : L) : ep p ∈ f m ↔ p ∈ m := (hex p).choose_spec m
  have hinj : Function.Injective ep := by
    intro p q hpq
    apply point_ext (L := L) p q
    intro m
    rw [←hep p m, ←hep q m, hpq]
  have honto : Function.Surjective ep := by
    intro p'
    have hrev : ∀ (p : {p : P' // p ∉ l'}) (m : L'),
        (e.symm p).val ∈ f.symm m ↔ p.val ∈ m := by
      intro p m
      simpa only [e.apply_symm_apply, f.apply_symm_apply] using
        (hi (e.symm p) (f.symm m)).symm
    have hf' : f.symm l' = l := by rw [←hf,f.symm_apply_apply]
    have hp : ∃ p : P, ∀ m : L', p ∈ f.symm m ↔ p' ∈ m := by
      by_cases hp' : p' ∈ l'
      · obtain ⟨p,_,hh⟩ := exists_infinity_image l' l e.symm f.symm hf' hrev (e o) p' hp'
        exact ⟨p,hh⟩
      · exact ⟨e.symm ⟨p',hp'⟩,hrev ⟨p',hp'⟩⟩
    obtain ⟨p,hp⟩ := hp
    refine ⟨p,point_ext (L := L') (ep p) p' ?_⟩
    intro m
    simpa only [f.apply_symm_apply] using (hep p (f.symm m)).trans (hp m)
  refine ⟨Equiv.ofBijective ep ⟨hinj,honto⟩,hep,?_⟩
  intro p
  apply point_ext (L := L')
  intro m
  obtain ⟨n,rfl⟩ := f.surjective m
  exact (hep p n).trans (hi p n).symm

/-- Images of affine lines suffice to construct the whole line equivalence. -/
theorem exists_line_extension
    (hl : ∀ m : L, m ≠ l → ∃ m' : L', m' ≠ l' ∧
      ∀ p : {p : P // p ∉ l}, (e p).val ∈ m' ↔ p.val ∈ m) :
    ∃ f : L ≃ L', f l = l' ∧
      ∀ (p : {p : P // p ∉ l}) (m : L), (e p).val ∈ f m ↔ p.val ∈ m := by
  classical
  have hex (m : L) : ∃ m' : L',
      ∀ p : {p : P // p ∉ l}, (e p).val ∈ m' ↔ p.val ∈ m := by
    by_cases hm : m = l
    · subst m
      exact ⟨l',fun p => iff_of_false (e p).property p.property⟩
    · obtain ⟨m',_,hh⟩ := hl m hm
      exact ⟨m',hh⟩
  let f : L → L' := fun m => (hex m).choose
  have hf (p : {p : P // p ∉ l}) (m : L) :
      (e p).val ∈ f m ↔ p.val ∈ m := (hex m).choose_spec p
  have hinj : Function.Injective f := by
    intro m n hmn
    apply line_eq_of_affine l
    intro p hp
    rw [←hf ⟨p,hp⟩ m, ←hf ⟨p,hp⟩ n, hmn]
  have horder : ProjectivePlane.order P L = ProjectivePlane.order P' L' := by
    have hc := Nat.card_congr e
    rw [card_affinePoints, card_affinePoints] at hc
    nlinarith
  have hcard : Nat.card L = Nat.card L' := by
    let : Fintype L := Fintype.ofFinite L
    let : Fintype L' := Fintype.ofFinite L'
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ProjectivePlane.card_lines P L, ProjectivePlane.card_lines P' L', horder]
  refine ⟨Equiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩),?_,hf⟩
  apply line_eq_of_affine l'
  intro p hp
  obtain ⟨q,hq⟩ := e.surjective ⟨p,hp⟩
  have hh := hf q l
  rw [hq] at hh
  exact hh.trans (iff_of_false q.property hp)

/-- An affine chart comparison preserving affine lines extends to full incidence. -/
theorem exists_incidence_extension
    (hl : ∀ m : L, m ≠ l → ∃ m' : L', m' ≠ l' ∧
      ∀ p : {p : P // p ∉ l}, (e p).val ∈ m' ↔ p.val ∈ m)
    (o : {p : P // p ∉ l}) :
    ∃ (ep : P ≃ P') (el : L ≃ L'), el l = l' ∧
      (∀ p m, ep p ∈ el m ↔ p ∈ m) ∧
      ∀ p : {p : P // p ∉ l}, ep p.val = (e p).val := by
  obtain ⟨el,hel,hi⟩ := exists_line_extension l l' e hl
  obtain ⟨ep,hep,ha⟩ := exists_projective_extension l l' e el hel hi o
  exact ⟨ep,el,hel,hep,ha⟩
end Configuration.TranslationPlane
