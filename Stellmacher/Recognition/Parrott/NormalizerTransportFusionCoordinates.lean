module

public import Stellmacher.Recognition.Parrott.NormalizerTransportRootAlgebra
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionOrbitBound

/-!
# Elementary fusion coordinates for the supplied Parrott transport

The intersection of the class of y with wF consists of the eight words
wuv, wt, wut, wvt and their z-twists. Conjugation by x cycles the four
base words and conjugation by a supplies the twists. The actions of b
and c distinguish the base words. Thus the eight words saturate the
previously proved upper bound for this intersection.

Since y is conjugate to yaz, transport puts (yaz)ˢ in this list.
The supplied s preserves ⟨z,t,v⟩, whose generators commute with w;
but a is outside that subgroup because [a,w] = z ≠ 1.
This excludes four of the eight possibilities and proves aˢ ∈ u⟨v,z⟩.
No square-root exhaustion or normalizer-seed assertion is used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, first paragraph, with the involution fusion from p.681.
-/

set_option linter.unusedSimpArgs false

open Subgroup Tits
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]
private theorem inv_of_sq {g : G} (h : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
private theorem act_comm {g j : G} (h : Commute g j) :
    (MulAut.conj g⁻¹) j = j := by
  simp only [MulAut.conj_apply, inv_inv, h.inv_left.eq, mul_assoc,
    inv_mul_cancel, mul_one]
private theorem act_rel {g j q : G} (h : parrottCommutator g j = q)
    (hq : q ^ 2 = 1) : (MulAut.conj g⁻¹) j = j * q := by
  have hh := (parrottCommutator_eq_iff _ _ _).mp h
  change g⁻¹ * j * g⁻¹⁻¹ = j * q
  rw [inv_inv]
  calc
    _ = g⁻¹ * (g * j) * q⁻¹ := by rw [hh]; group
    _ = _ := by rw [inv_of_sq hq]; group

private def base (f : ParrottSylowGeneratorData n) (i : Fin 4) : G :=
  match i.val with
  | 0 => f.w * f.u * n.v
  | 1 => f.w * n.t
  | 2 => f.w * f.u * n.t
  | _ => f.w * n.v * n.t
private def word (f : ParrottSylowGeneratorData n) (i : Fin 4 × Bool) : G :=
  base f i.1 * z ^ i.2.toNat

private theorem base_actions (f : ParrottSylowGeneratorData n) (i : Fin 4) :
    (MulAut.conj f.x⁻¹) (base f i) = base f (i + 1) ∧
    (MulAut.conj f.a⁻¹) (base f i) = base f i * z ∧
    (MulAut.conj f.b⁻¹) (base f i) = base f i * z ^ (if i = 0 ∨ i = 2 then 1 else 0) ∧
    (MulAut.conj f.c⁻¹) (base f i) = base f i * z ^ (if i = 0 ∨ i = 3 then 1 else 0) := by
  have Xw := act_rel f.eq01_xw f.u_sq
  have Xu := act_rel f.eq01_xu f.v_sq
  have Xv := act_rel f.eq01_xv f.t_sq
  have Xt := act_comm ((parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)
  have Aw := act_rel f.eq02_aw f.z_sq
  have Au := act_comm f.comm_au
  have Av := act_comm f.comm_av
  have At := act_comm f.comm_at
  have Bw := act_comm ((parrottCommutator_eq_one_iff _ _).mp f.eq02_bw)
  have Bu := act_rel f.eq02_bu f.z_sq
  have Bv := act_comm (show Commute f.b n.v from by rw [← f.eq03_b]; exact Commute.self_pow _ _)
  have Bt := act_comm f.comm_bt
  have Cw := act_comm ((parrottCommutator_eq_one_iff _ _).mp f.eq09_cw)
  have Cu := act_comm ((parrottCommutator_eq_one_iff _ _).mp f.eq09_cu)
  have Cv := act_rel f.eq10_cv f.z_sq
  have Ct := act_comm ((parrottCommutator_eq_one_iff _ _).mp f.eq10_ct)
  have uu : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  have vv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have tt : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  generalize hX : MulAut.conj f.x⁻¹ = X at *
  generalize hA : MulAut.conj f.a⁻¹ = A at *
  generalize hB : MulAut.conj f.b⁻¹ = B at *
  generalize hC : MulAut.conj f.c⁻¹ = C at *
  fin_cases i <;> simp +decide only [Fin.ext_iff, ite_true, ite_false, pow_zero, pow_one, mul_one]
  all_goals first
    | change X (f.w * f.u * n.v) = f.w * n.t ∧
        A (f.w * f.u * n.v) = (f.w * f.u * n.v) * z ∧
        B (f.w * f.u * n.v) = (f.w * f.u * n.v) * z ∧
        C (f.w * f.u * n.v) = (f.w * f.u * n.v) * z
    | change X (f.w * n.t) = f.w * f.u * n.t ∧
        A (f.w * n.t) = (f.w * n.t) * z ∧
        B (f.w * n.t) = f.w * n.t ∧
        C (f.w * n.t) = f.w * n.t
    | change X (f.w * f.u * n.t) = f.w * n.v * n.t ∧
        A (f.w * f.u * n.t) = (f.w * f.u * n.t) * z ∧
        B (f.w * f.u * n.t) = (f.w * f.u * n.t) * z ∧
        C (f.w * f.u * n.t) = f.w * f.u * n.t
    | change X (f.w * n.v * n.t) = f.w * f.u * n.v ∧
        A (f.w * n.v * n.t) = (f.w * n.v * n.t) * z ∧
        B (f.w * n.v * n.t) = f.w * n.v * n.t ∧
        C (f.w * n.v * n.t) = (f.w * n.v * n.t) * z
  all_goals simp only [map_mul, Xw, Xu, Xv, Xt, Aw, Au, Av, At, Bw, Bu, Bv, Bt, Cw, Cu, Cv, Ct,
    mul_assoc, tail f.comm_vu.eq, tail f.comm_tv.eq,
    tail f.comm_zu.eq, tail f.comm_zv.eq, tail f.comm_zt.eq,
    f.comm_zu.eq, f.comm_zv.eq, f.comm_zt.eq,
    tail uu, tail vv, tail tt, uu, vv, tt, one_mul, mul_one, and_self]

private theorem word_twist (f : ParrottSylowGeneratorData n) (φ : MulAut G)
    (hφz : φ z = z) (i : Fin 4 × Bool) (r : ℕ)
    (hi : φ (base f i.1) = base f i.1 * z ^ r) :
    φ (word f i) = word f i * z ^ r := by
  simp only [word, map_mul, map_pow, hφz, hi, mul_assoc, ← pow_add]
  rw [Nat.add_comm]

private theorem word_injective (f : ParrottSylowGeneratorData n) (hz : z ≠ 1) :
    Function.Injective (word f) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ he
  -- The b- and c-actions detect the u- and v-coordinates, respectively.
  have hb := congrArg (MulAut.conj f.b⁻¹) he
  have hc := congrArg (MulAut.conj f.c⁻¹) he
  rw [word_twist f _ (act_comm f.comm_zb.symm) _ _ (base_actions f i).2.2.1,
    word_twist f _ (act_comm f.comm_zb.symm) _ _ (base_actions f i').2.2.1,
    he, mul_left_cancel_iff] at hb
  rw [word_twist f _ (act_comm f.comm_zc.symm) _ _ (base_actions f i).2.2.2,
    word_twist f _ (act_comm f.comm_zc.symm) _ _ (base_actions f i').2.2.2,
    he, mul_left_cancel_iff] at hc
  have hii : i = i' := by
    fin_cases i <;> fin_cases i' <;> simp +decide only [Fin.ext_iff, pow_one, pow_zero, ite_true, ite_false, or_true, true_or, false_or] at hb hc ⊢ <;>
      first | exact False.elim (hz hb) | exact False.elim (hz hb.symm) |
        exact False.elim (hz hc) | exact False.elim (hz hc.symm)
  subst i'
  have hj : j = j' := by
    have hh : z ^ j.toNat = z ^ j'.toNat := by
      simpa only [word, mul_left_cancel_iff] using he
    cases j <;> cases j' <;> simp_all
  exact Prod.ext rfl hj
private theorem words_in_class (f : ParrottCentralizerGeneratorData n) :
    Set.range (word f.toParrottSylowGeneratorData) ⊆
      {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} := by
  let d := f.toParrottSylowGeneratorData
  have step (i : Fin 4) : IsConj (base d i) (base d (i + 1)) :=
    isConj_iff.mpr ⟨f.x⁻¹, by
      simpa only [MulAut.conj_apply, inv_inv] using (base_actions d i).1⟩
  have twist (i : Fin 4) : IsConj (base d i) (base d i * z) :=
    isConj_iff.mpr ⟨f.a⁻¹, by
      simpa only [MulAut.conj_apply, inv_inv] using (base_actions d i).2.1⟩
  have h0 : IsConj f.y (base d 0) :=
    f.y_isConj_wuvz.trans (twist 0).symm
  have h1 : IsConj f.y (base d 1) := h0.trans (step 0)
  have h2 : IsConj f.y (base d 2) := h1.trans (step 1)
  have h3 : IsConj f.y (base d 3) := h2.trans (step 2)
  have hall (i : Fin 4) : IsConj f.y (base d i) := by
    fin_cases i <;> assumption
  have hu : f.u ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hv : n.v ∈ e.F := n.v_mem_inf.2
  have ht : n.t ∈ e.F := n.t_mem_inf.2
  have hz : z ∈ e.F := e.z_mem_inf.2
  rintro g ⟨⟨i, j⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have hb : f.w⁻¹ * base d i ∈ e.F := by
      fin_cases i
      · change f.w⁻¹ * (f.w * f.u * n.v) ∈ e.F
        simpa only [inv_mul_cancel_left, mul_assoc] using e.F.mul_mem hu hv
      · change f.w⁻¹ * (f.w * n.t) ∈ e.F
        simpa only [inv_mul_cancel_left] using ht
      · change f.w⁻¹ * (f.w * f.u * n.t) ∈ e.F
        simpa only [inv_mul_cancel_left, mul_assoc] using e.F.mul_mem hu ht
      · change f.w⁻¹ * (f.w * n.v * n.t) ∈ e.F
        simpa only [inv_mul_cancel_left, mul_assoc] using e.F.mul_mem hv ht
    simpa only [word, mul_assoc] using e.F.mul_mem hb (e.F.pow_mem hz j.toNat)
  · cases j
    · simpa only [word, Bool.toNat_false, pow_zero, mul_one] using hall i
    · simpa only [word, Bool.toNat_true, pow_one] using (hall i).trans (twist i)

private theorem class_eq_words [Finite G] (f : ParrottCentralizerGeneratorData n)
    (h : ParrottCentralizerHypotheses z) :
    {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} =
      Set.range (word f.toParrottSylowGeneratorData) := by
  have hz : z ≠ 1 := by
    intro hz
    have hh := h.involution
    rw [hz, orderOf_one] at hh
    omega
  have hc : (Set.range (word f.toParrottSylowGeneratorData)).ncard = 8 := by
    rw [Set.ncard_range_of_injective (word_injective _ hz)]
    simp only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  exact (Set.eq_of_subset_of_ncard_le (words_in_class f)
    (hc ▸ f.w_coset_y_class_ncard_le_eight h)).symm
private theorem transport_twice {f : ParrottCentralizerGeneratorData n}
    (k : ParrottNormalizerTransportData f) (g : G) :
    (MulAut.conj k.s⁻¹) ((MulAut.conj k.s⁻¹) g) = g := by
  simp only [MulAut.conj_apply, inv_inv, inv_of_sq k.sq]
  have hss : k.s * k.s = 1 := by simpa only [pow_two] using k.sq
  simp only [← mul_assoc, hss, one_mul]
  rw [mul_assoc, hss, mul_one]

private theorem a_image_not_small {f : ParrottCentralizerGeneratorData n}
    (k : ParrottNormalizerTransportData f) (h : ParrottCentralizerHypotheses z) :
    (MulAut.conj k.s⁻¹) f.a ∉ closure ({z, n.t, n.v} : Set G) := by
  let L := closure ({z, n.t, n.v} : Set G)
  let S := MulAut.conj k.s⁻¹
  have hz : z ∈ L := subset_closure (by simp)
  have ht : n.t ∈ L := subset_closure (by simp)
  have hv : n.v ∈ L := subset_closure (by simp)
  -- The three transport equations preserve the small elementary subgroup.
  have hS : L ≤ L.comap S.toMonoidHom := by
    apply (closure_le _).mpr
    intro g hg
    change S g ∈ L
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · simpa only [S, MulAut.conj_apply, inv_inv, k.z_conj] using ht
    · simpa only [S, MulAut.conj_apply, inv_inv, k.t_conj] using hz
    · simpa only [S, MulAut.conj_apply, inv_inv, k.v_conj] using L.mul_mem (L.mul_mem hv ht) hz
  have hL : L ≤ centralizer ({f.w} : Set G) := by
    apply (closure_le _).mpr
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact f.comm_zw.eq
    · exact f.comm_tw.eq
    · exact f.comm_vw.eq
  intro ha
  have haa : f.a ∈ L := by
    have hh : S (S f.a) ∈ L := hS ha
    simpa only [S, transport_twice] using hh
  have hc : Commute f.a f.w := mem_centralizer_singleton_iff.mp (hL haa)
  have hz1 : z = 1 := f.eq02_aw.symm.trans ((parrottCommutator_eq_one_iff _ _).mpr hc)
  have hz2 := h.involution
  rw [hz1, orderOf_one] at hz2
  omega

/-- Elementary fusion restricts the image of a under the supplied transport,
without any square-root exhaustion or normalizer-seed hypothesis. -/
public theorem ParrottNormalizerTransportData.a_conj_fusion_coordinates [Finite G]
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f)
    (h : ParrottCentralizerHypotheses z) :
    k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z ∨
    k.s⁻¹ * f.a * k.s = f.u * n.v ∨ k.s⁻¹ * f.a * k.s = f.u * n.v * z := by
  let S := MulAut.conj k.s⁻¹
  have hy : S f.y = f.w * f.u * n.v * z := by
    simpa only [S, MulAut.conj_apply, inv_inv] using k.y_conj
  have hz : S z = n.t := by
    simpa only [S, MulAut.conj_apply, inv_inv] using k.z_conj
  have haF : f.a ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hSaF : S f.a ∈ e.F := by
    simpa only [S, MulAut.conj_apply, inv_inv] using
      (mem_normalizer_iff''.mp k.mem_normalizer f.a).mp haF
  have huF : f.u ∈ e.F := f.elementary_basis ▸ subset_closure (by simp)
  have hgF : f.w⁻¹ * S (f.y * f.a * z) ∈ e.F := by
    rw [map_mul, map_mul, hy, hz]
    simpa only [mul_assoc, inv_mul_cancel_left] using
      e.F.mul_mem (e.F.mul_mem (e.F.mul_mem (e.F.mul_mem huF n.v_mem_inf.2)
        e.z_mem_inf.2) hSaF) n.t_mem_inf.2
  have hyaz : IsConj f.y (f.y * f.a * z) :=
    isConj_iff.mpr ⟨(f.c * f.u)⁻¹, by
      simpa only [inv_inv] using f.toParrottSylowGeneratorData.y_conj_cu⟩
  have hgC : IsConj f.y (S (f.y * f.a * z)) :=
    hyaz.trans (isConj_iff.mpr ⟨k.s⁻¹, rfl⟩)
  have hg : S (f.y * f.a * z) ∈ Set.range (word f.toParrottSylowGeneratorData) :=
    (class_eq_words f h) ▸ (show S (f.y * f.a * z) ∈
      {g : G | f.w⁻¹ * g ∈ e.F ∧ IsConj f.y g} from ⟨hgF, hgC⟩)
  obtain ⟨⟨i, j⟩, hij⟩ := hg
  have he : f.w * f.u * n.v * z * S f.a * n.t = word f.toParrottSylowGeneratorData (i, j) := by
    simpa only [map_mul, hy, hz] using hij.symm
  have hsolve : S f.a = (f.u * n.v * z)⁻¹ *
      (f.w⁻¹ * word f.toParrottSylowGeneratorData (i, j)) * n.t⁻¹ := by
    rw [← he]
    group
  have hnot : S f.a ∉ closure ({z, n.t, n.v} : Set G) := a_image_not_small k h
  have hzt : n.t * z ∈ closure ({z, n.t, n.v} : Set G) :=
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hvz : n.v * z ∈ closure ({z, n.t, n.v} : Set G) :=
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have ht : n.t ∈ closure ({z, n.t, n.v} : Set G) := subset_closure (by simp)
  have hv : n.v ∈ closure ({z, n.t, n.v} : Set G) := subset_closure (by simp)
  have zz : z * z = 1 := by simpa only [pow_two] using f.z_sq
  have tt : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  have vv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have uu : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  have hSa : S f.a = k.s⁻¹ * f.a * k.s := by simp only [S, MulAut.conj_apply, inv_inv]
  rw [← hSa]
  -- The wuv and wut cases put aˢ in the small subgroup; the other cases survive.
  fin_cases i <;> cases j
  all_goals dsimp only [word, base] at hsolve
  all_goals
    simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_one,
      mul_inv_rev, inv_of_sq f.z_sq, inv_of_sq f.v_sq, inv_of_sq f.u_sq,
      inv_of_sq f.t_sq, mul_assoc, inv_mul_cancel_left,
      tail f.comm_zu.eq, tail f.comm_zv.eq, tail f.comm_zt.eq,
      tail f.comm_vu.eq, tail f.comm_tv.eq, tail f.comm_tu.eq,
      f.comm_zt.eq, f.comm_zv.eq, f.comm_zu.eq,
      tail zz, tail tt, tail vv, tail uu, zz, tt, vv, uu, one_mul, mul_one] at hsolve
  all_goals first
    | exact Or.inl hsolve
    | exact Or.inr (Or.inl hsolve)
    | exact Or.inr (Or.inr (Or.inl hsolve))
    | exact Or.inr (Or.inr (Or.inr (by simpa only [mul_assoc] using hsolve)))
    | exact False.elim (hnot (hsolve.symm ▸ hzt))
    | exact False.elim (hnot (hsolve.symm ▸ hvz))
    | exact False.elim (hnot (hsolve.symm ▸ ht))
    | exact False.elim (hnot (hsolve.symm ▸ hv))

end Stellmacher.Recognition
