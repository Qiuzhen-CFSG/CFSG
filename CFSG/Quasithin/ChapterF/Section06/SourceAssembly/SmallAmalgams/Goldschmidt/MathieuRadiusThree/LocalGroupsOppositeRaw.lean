module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeQuotient
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeLift
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeFrame
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionCoreNormalization

/-!
# Literal source generators for the opposite endpoint

A cubic branch actor cycles three depth-three source labels. An order-four
lift fixes the first label and exchanges the two independent adjacent
central labels. The exact branch-action kernel supplies the two remaining
core-membership relations. The core together with these two actors generates
the opposite source group, giving the complete extension-recognition input.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the last
paragraph of (6.12), printed p.406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem cubic_and_reflection : ∀ (p q : Equiv.Perm (Fin 3)) (i : Fin 3),
    p ≠ 1 → p i = i → q ^ 3 = 1 → q ≠ 1 →
      p (q i) = (q ^ 2) i ∧ p ((q ^ 2) i) = q i ∧
        (p * q) ^ 2 = 1 ∧ p ^ 2 = 1 := by
  have h₃ : ∀ (p q : Equiv.Perm (Fin 3)) (i : Fin 3),
      p ≠ 1 → p i = i → q ^ 3 = 1 → q ≠ 1 → (p * q) ^ 2 = 1 := by decide +kernel
  have h₄ : ∀ (p : Equiv.Perm (Fin 3)) (i : Fin 3),
      p ≠ 1 → p i = i → p ^ 2 = 1 := by decide +kernel
  intro p q i hp hi hq hqne
  have hpq := h₃ p q i hp hi hq hqne
  have hp2 := h₄ p i hp hi
  have hpi : p⁻¹=p := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp2)
  have hqi : q⁻¹=q^2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ',hq])
  have hpqi : (p*q)⁻¹=p*q :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpq)
  have hrel : p*q=q^2*p := by rw [← hpqi,mul_inv_rev,hpi,hqi]
  have h₁ : p (q i)=(q^2) i := by
    have hh := Equiv.congr_fun hrel i
    simpa only [Equiv.Perm.mul_apply,hi] using hh
  have h₂ : p ((q^2) i)=q i := by
    have hh := Equiv.congr_fun hp2 (q i)
    simpa only [pow_two,Equiv.Perm.mul_apply,Equiv.Perm.one_apply,h₁] using hh
  exact ⟨h₁,h₂,hpq,hp2⟩

/-- Goldschmidt's geometric source generators satisfy exactly the raw
core-by-S₃ recognition contract inside the literal opposite group. -/
theorem LocalRelations.oppositeGroup_raw_generators
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side)
    (hcards : ∀ a, (RankTwo.graph F).Adj v a → Nat.card (d.labelBall a 4) = 192) :
    ∃ x y z a b T C : oppositeGroup d v,
      CoreExtensionRawRelations x y z a b T C ∧
      closure ({x,y,z,T,C} : Set (oppositeGroup d v)) = ⊤ := by
  classical
  let t := h.action.toCubicTreeAction
  let H := oppositeGroup d v
  let Q := (d.labelBall v 3).subgroupOf H
  have hHQ := radiusThree_le_oppositeGroup d t hr (by have := h.five_le; omega) v
  obtain ⟨f⟩ := t.exists_branchFrame v
  let a₀ := (f.e 0).val
  have hva : (RankTwo.graph F).Adj v a₀ := (f.e 0).property
  have ha : a₀.type = d.side := by
    have hn := hva.1
    cases h0 : v.type <;> cases h1 : a₀.type <;> cases h2 : d.side <;> simp_all
  obtain ⟨tg, htarm, htsq, ⟨b₀, hvb, htb⟩, w₀, hwside, hdw, hnw, htx⟩ :=
    r.exists_oppositeGenerator_lift_with_fixedLabel hr ha hva
  obtain ⟨cg, hcH, hc3, hcmove⟩ := r.exists_oppositeGroup_cubic hr v hv hcards
  let T : H := ⟨tg, oppositeGenerator_le d hva htarm⟩
  let C : H := ⟨cg, hcH⟩
  have hCv : cg • v = v := oppositeGroup_le_stabilizer d v hcH
  have hCnv (n : ℕ) : cg ^ n • v = v :=
    oppositeGroup_le_stabilizer d v (H.pow_mem hcH n)
  let u : Fin 3 → RankTwo.Vertex F := ![a₀,cg • a₀,cg ^ 2 • a₀]
  let w : Fin 3 → RankTwo.Vertex F := ![w₀,cg • w₀,cg ^ 2 • w₀]
  have hUadj : ∀ i, (RankTwo.graph F).Adj v (u i) := by
    have hh (n : ℕ) : (RankTwo.graph F).Adj v (cg ^ n • a₀) := by
      have he := (translationGraphIso F (cg ^ n)).toHom.map_adj hva
      change (RankTwo.graph F).Adj (cg ^ n • v) (cg ^ n • a₀) at he
      simpa only [hCnv] using he
    intro i
    fin_cases i
    · exact hva
    · change (RankTwo.graph F).Adj v (cg • a₀)
      simpa only [pow_one] using hh 1
    · exact hh 2
  have haC : a₀ ≠ cg • a₀ := (hcmove a₀ hva).symm
  have haC2 : a₀ ≠ cg ^ 2 • a₀ := by
    intro he
    have hh := congrArg (cg • ·) he
    rw [← mul_smul, ← pow_succ', hc3, one_smul] at hh
    exact hcmove a₀ hva hh
  have hCC2 : cg • a₀ ≠ cg ^ 2 • a₀ := by
    rw [pow_two, mul_smul]
    exact fun he => haC ((MulAction.toPerm cg).injective he)
  have hUdist : ∀ i j, i ≠ j → u i ≠ u j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | exact haC | exact haC2 | exact haC.symm |
        exact hCC2 | exact haC2.symm | exact hCC2.symm
  have hwtypes : ∀ i, (w i).type = d.side := by
    intro i
    fin_cases i <;> exact hwside
  have hwdist : ∀ i, (RankTwo.graph F).dist v (w i) = 3 := by
    have hh (n : ℕ) : (RankTwo.graph F).dist v (cg ^ n • w₀) = 3 := by
      have he := RankTwo.dist_smul F (cg ^ n) v w₀
      rw [hCnv] at he
      exact he.trans hdw
    intro i
    fin_cases i
    · exact hdw
    · change (RankTwo.graph F).dist v (cg • w₀) = 3
      simpa only [pow_one] using hh 1
    · exact hh 2
  have hwnear : ∀ i, (RankTwo.graph F).dist (u i) (w i) = 2 := by
    intro i
    fin_cases i
    · exact hnw
    · exact (RankTwo.dist_smul F cg a₀ w₀).trans hnw
    · exact (RankTwo.dist_smul F (cg ^ 2) a₀ w₀).trans hnw
  obtain ⟨hrelG, hcoreG⟩ := r.radiusThree_arms_generators hr hv u w hUadj hUdist
    hwtypes hwdist hwnear
  have hwQ (i : Fin 3) : d.label (w i) ∈ d.labelBall v 3 :=
    d.label_mem_labelBall (hwtypes i) (le_of_eq (hwdist i))
  have hutypes (i : Fin 3) : (u i).type = d.side := by
    fin_cases i <;> exact ha
  have huQ (i : Fin 3) : d.label (u i) ∈ d.labelBall v 3 :=
    d.label_mem_labelBall (hutypes i) ((dist_eq_one_iff_adj.mpr (hUadj i)).le.trans (by decide))
  let x : H := ⟨d.label (w 0), hHQ (hwQ 0)⟩
  let y : H := ⟨d.label (w 1), hHQ (hwQ 1)⟩
  let z : H := ⟨d.label (w 2), hHQ (hwQ 2)⟩
  let a : H := ⟨d.label (u 2), hHQ (huQ 2)⟩
  let b : H := ⟨d.label (u 1), hHQ (huQ 1)⟩
  have hrel : ThreeInvolutionFourCommutators.Relations x y z a b := {
    x_sq := Subtype.ext hrelG.x_sq
    y_sq := Subtype.ext hrelG.y_sq
    z_sq := Subtype.ext hrelG.z_sq
    a_order := (Subgroup.orderOf_coe a).symm.trans hrelG.a_order
    b_order := (Subgroup.orderOf_coe b).symm.trans hrelG.b_order
    a_ne_b := fun he => hrelG.a_ne_b (congrArg Subtype.val he)
    xy := Subtype.ext hrelG.xy
    xz := Subtype.ext hrelG.xz
    yz := Subtype.ext hrelG.yz
    bx := Subtype.ext hrelG.bx.eq
    by_ := Subtype.ext hrelG.by_.eq
    bz := Subtype.ext hrelG.bz.eq }
  have hcore : closure ({x,y,z} : Set H) = Q := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    change closure ({d.label (w 0),d.label (w 1),d.label (w 2)} : Set G) = Q.map H.subtype
    rw [hcoreG, Subgroup.map_subgroupOf_eq_of_le hHQ]
  obtain ⟨hHcard, hkerG⟩ := r.oppositeGroup_card_and_action_kernel hr v hv hcards f
  let : Finite H := Nat.finite_of_card_ne_zero (by rw [hHcard]; decide)
  let ψ := f.branchAction.comp (Subgroup.inclusion (oppositeGroup_le_stabilizer d v))
  have hker : ψ.ker = Q := hkerG
  have heval (g : H) (i : Fin 3) : (f.e (ψ g i)).val = g.val • (f.e i).val :=
    f.branchAction_eval (Subgroup.inclusion (oppositeGroup_le_stabilizer d v) g) i
  have hψT : ψ T ≠ 1 := by
    intro he
    obtain ⟨i, hi⟩ := f.e.surjective ⟨b₀, hvb⟩
    have hi' : (f.e i).val = b₀ := congrArg Subtype.val hi
    have hh := heval T i
    rw [he, Equiv.Perm.one_apply, hi'] at hh
    exact htb hh.symm
  have hψC : ψ C ≠ 1 := by
    intro he
    have hh := heval C 0
    rw [he, Equiv.Perm.one_apply] at hh
    exact hcmove a₀ hva hh.symm
  have hψTf : ψ T 0 = 0 := by
    apply f.e.injective
    apply Subtype.ext
    rw [heval]
    exact d.labelBall_le_stabilizer a₀ 4 (by omega)
      (by have := h.five_le; omega) htarm.1
  have hC3 : C ^ 3 = 1 := Subtype.ext hc3
  have hψC3 : (ψ C) ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
  obtain ⟨hT1, hT2, hTC, hTsquare⟩ := cubic_and_reflection (ψ T) (ψ C) 0
    hψT hψTf hψC3 hψC
  have hTorder : orderOf (ψ T) = 2 := orderOf_eq_prime hTsquare hψT
  have hu1 : (f.e (ψ C 0)).val = u 1 := heval C 0
  have hu2 : (f.e ((ψ C ^ 2) 0)).val = u 2 := by
    rw [← map_pow]
    exact heval (C ^ 2) 0
  have hTact1 : tg • u 1 = u 2 := by rw [← hu1, ← heval T, hT1, hu2]
  have hTact2 : tg • u 2 = u 1 := by rw [← hu2, ← heval T, hT2, hu1]
  have hTsq : T ^ 2 = a * b := by
    apply Subtype.ext
    change tg ^ 2 = d.label (u 2) * d.label (u 1)
    rw [htsq]
    have hp := d.neighbor_product v (u 2) (u 1) (u 0) (hUadj 2) (hUadj 1) (hUadj 0)
      (hUdist 2 1 (by decide)) (hUdist 2 0 (by decide)) (hUdist 1 0 (by decide)) (hutypes 2)
    have hh : d.label (u 2) * d.label (u 1) = d.label (u 0) := by
      simpa only [d.label_inv (hutypes 0)] using mul_eq_one_iff_eq_inv.mp hp
    exact hh.symm
  have hraw : CoreExtensionRawRelations x y z a b T C := {
    toRelations := hrel
    T_sq := hTsq
    C_cube := hC3
    Tx := by
      apply Subtype.ext
      change tg * d.label w₀ * tg⁻¹ = d.label w₀
      rw [htx.eq, mul_inv_cancel_right]
    Cx := by
      apply Subtype.ext
      exact (d.conjugate cg w₀ hwside).symm
    Cy := by
      apply Subtype.ext
      change cg * d.label (cg • w₀) * cg⁻¹ = d.label (cg ^ 2 • w₀)
      rw [← d.conjugate cg (cg • w₀) hwside, ← mul_smul, ← pow_two]
    Cz := by
      apply Subtype.ext
      change cg * d.label (cg ^ 2 • w₀) * cg⁻¹ = d.label w₀
      rw [← d.conjugate cg (cg ^ 2 • w₀) hwside, ← mul_smul, ← pow_succ', hc3, one_smul]
    Ta := by
      apply Subtype.ext
      change tg * d.label (u 2) * tg⁻¹ = d.label (u 1)
      rw [← d.conjugate tg (u 2) (hutypes 2), hTact2]
    Tb := by
      apply Subtype.ext
      change tg * d.label (u 1) * tg⁻¹ = d.label (u 2)
      rw [← d.conjugate tg (u 1) (hutypes 1), hTact1]
    Ty_mem := by
      rw [hcore]
      exact (radiusThree_normal_oppositeGroup d t hr (by have := h.five_le; omega) v).conj_mem
        y (hwQ 1) T
    TC_sq_mem := by
      rw [hcore, ← hker]
      change ψ ((T*C)^2) = 1
      rw [map_pow, map_mul, hTC] }
  refine ⟨x,y,z,a,b,T,C,hraw,?_⟩
  let J := closure ({x,y,z,T,C} : Set H)
  have hQJ : ψ.ker ≤ J := by
    rw [hker, ← hcore]
    apply Subgroup.closure_mono
    intro g hg
    rcases hg with rfl | rfl | rfl <;> simp
  have hTmem : T ∈ J := subset_closure (by simp)
  have hCmem : C ∈ J := subset_closure (by simp)
  have htwo : 2 ∣ Nat.card (J.map ψ) := by
    simpa only [hTorder] using
      (J.map ψ).orderOf_dvd_natCard (mem_map.mpr ⟨T,hTmem,rfl⟩)
  have hthree : 3 ∣ Nat.card (J.map ψ) := by
    have ho : orderOf (ψ C) = 3 := orderOf_eq_prime hψC3 hψC
    simpa only [ho] using
      (J.map ψ).orderOf_dvd_natCard (mem_map.mpr ⟨C,hCmem,rfl⟩)
  have hfull : J.map ψ = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [card_top, Nat.card_perm, Nat.card_fin]
    exact Nat.le_of_dvd Nat.card_pos ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwo hthree)
  change J = ⊤
  rw [← Subgroup.comap_map_eq_self hQJ, hfull, Subgroup.comap_top]

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
