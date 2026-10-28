module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Geometry.Shears

/-!
# Irreducibility of the end-radical parameters

A transvection in the four-dimensional Levi block sends a parameter vector
`a` to `a + a i • e j`. An invariant additive subgroup containing a nonzero
vector therefore contains a coordinate vector, and then every coordinate
vector. This proves minimal normality in the actual parabolic. The shear
addition law also shows that its two-core is elementary abelian.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, Proposition 4.7,
step 1, manuscript p.25. Normality is used only inside the marked parabolic.
-/

public section

open Matrix
open Representation Representation.BinaryOffender
open SL5TenDimensional.Classification.Separated
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Geometry

private def levi (e : Fin 2) (i j : Fin 4) : G :=
  if e = 0 then rootElement i.succ j.succ else rootElement j.castSucc i.castSucc

private lemma root_mem_parabolic (e : Fin 2) (i j : Fin 5)
    (hblock : (i.val ≤ (node e).val ∧ j.val ≤ (node e).val) ∨
      ((node e).val < i.val ∧ (node e).val < j.val)) :
    rootElement i j ∈ parabolic e := by
  by_cases hij : i ≠ j
  · rw [mem_parabolic_iff]
    intro r s hr hs
    have hrs : r ≠ s := by intro h; subst s; omega
    have hpair : ¬ (i = r ∧ j = s) := by
      rintro ⟨rfl, rfl⟩
      rcases hblock with h | h <;> omega
    simp [rootElement, hij, Matrix.SpecialLinearGroup.transvection,
      Matrix.transvection, hrs, hpair]
  · simp only [rootElement, dif_neg hij]
    exact (parabolic e).one_mem

private lemma levi_mem_parabolic (e : Fin 2) (i j : Fin 4) : levi e i j ∈ parabolic e := by
  fin_cases e
  · apply root_mem_parabolic
    right
    simp [node]
  · apply root_mem_parabolic
    left
    change j.val ≤ 3 ∧ i.val ≤ 3
    constructor <;> omega

private lemma root_inv (i j : Fin 5) : (rootElement i j)⁻¹ = rootElement i j := by
  by_cases hij : i ≠ j
  · simp only [rootElement, dif_pos hij, Matrix.SpecialLinearGroup.transvection_inv]
    rfl
  · simp only [rootElement, dif_neg hij, inv_one]

private lemma levi_inv (e : Fin 2) (i j : Fin 4) : (levi e i j)⁻¹ = levi e i j := by
  unfold levi
  split_ifs <;> exact root_inv _ _

private lemma binary_self_add (x : F) : x + x = 0 := by
  exact (by decide : ∀ x : F, x + x = 0) x


private lemma sandwich_entry (M : Matrix (Fin 5) (Fin 5) F) (i j r s : Fin 5) :
    (Matrix.transvection i j (1 : F) * M * Matrix.transvection i j (1 : F)) r s =
      (M r s + if r = i then M j s else 0) +
        if s = j then M r i + if r = i then M j i else 0 else 0 := by
  by_cases hr : r = i <;> by_cases hs : s = j <;> subst_vars <;>
    simp [Matrix.mul_transvection_apply_of_ne, Matrix.transvection_mul_apply_of_ne, *]

@[simp] private lemma shear00 (a : Vec) : shearMatrix 0 a 0 0 = 1 := rfl
@[simp] private lemma shear0s (a : Vec) (j : Fin 4) :
    shearMatrix 0 a 0 j.succ = a j := by fin_cases j <;> rfl
@[simp] private lemma shears0 (a : Vec) (i : Fin 4) :
    shearMatrix 0 a i.succ 0 = 0 := by fin_cases i <;> rfl
@[simp] private lemma shearss (a : Vec) (i j : Fin 4) :
    shearMatrix 0 a i.succ j.succ = (1 : Matrix (Fin 4) (Fin 4) F) i j := by
  fin_cases i <;> fin_cases j <;> rfl
@[simp] private lemma shear44 (a : Vec) : shearMatrix 1 a 4 4 = 1 := rfl
@[simp] private lemma shearc4 (a : Vec) (i : Fin 4) :
    shearMatrix 1 a i.castSucc 4 = a i := by fin_cases i <;> rfl
@[simp] private lemma shear4c (a : Vec) (j : Fin 4) :
    shearMatrix 1 a 4 j.castSucc = 0 := by fin_cases j <;> rfl
@[simp] private lemma shearcc (a : Vec) (i j : Fin 4) :
    shearMatrix 1 a i.castSucc j.castSucc = (1 : Matrix (Fin 4) (Fin 4) F) i j := by
  fin_cases i <;> fin_cases j <;> rfl

private lemma conjugate_zero (i j : Fin 4) (hij : i ≠ j) (a : Vec) :
    (levi 0 i j).val * shearMatrix 0 a * (levi 0 i j).val =
      shearMatrix 0 (a + a i • Pi.single j 1) := by
  have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective 4 h)
  have ht : (levi 0 i j).val = Matrix.transvection i.succ j.succ 1 := by
    change (rootElement i.succ j.succ).val = _
    rw [rootElement, dif_pos hs]
    rfl
  have hi0 : (0 : Fin 5) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hj0 : (0 : Fin 5) ≠ j.succ := (Fin.succ_ne_zero j).symm
  have hji : j ≠ i := hij.symm
  rw [ht]
  ext r s
  rw [sandwich_entry]
  refine Fin.cases ?_ (fun r => ?_) r
  · refine Fin.cases ?_ (fun s => ?_) s
    · simp_all
    · by_cases hs : s = j
      · subst s; simp_all
      · have hjs := Ne.symm hs
        simp_all
  · refine Fin.cases ?_ (fun s => ?_) s
    · simp_all
    · by_cases hr : r = i <;> by_cases hs : s = j <;>
        simp_all [Matrix.one_apply]
      exact Ne.symm hs

private lemma conjugate_one (i j : Fin 4) (hij : i ≠ j) (a : Vec) :
    (levi 1 i j).val * shearMatrix 1 a * (levi 1 i j).val =
      shearMatrix 1 (a + a i • Pi.single j 1) := by
  have hs : j.castSucc ≠ i.castSucc := fun h => hij (Fin.castSucc_injective 4 h).symm
  have ht : (levi 1 i j).val = Matrix.transvection j.castSucc i.castSucc 1 := by
    change (rootElement j.castSucc i.castSucc).val = _
    rw [rootElement, dif_pos hs]
    rfl
  have hi4 : i.castSucc ≠ (4 : Fin 5) := ne_of_lt (Fin.castSucc_lt_last i)
  have hj4 : j.castSucc ≠ (4 : Fin 5) := ne_of_lt (Fin.castSucc_lt_last j)
  have h4i := hi4.symm
  have h4j := hj4.symm
  have hji := hij.symm
  rw [ht]
  ext r s
  rw [sandwich_entry]
  refine Fin.lastCases ?_ (fun r => ?_) r
  · refine Fin.lastCases ?_ (fun s => ?_) s
    · simp_all
    · simp_all
  · refine Fin.lastCases ?_ (fun s => ?_) s
    · by_cases hr : r = j
      · subst r; simp_all
      · have hjr := Ne.symm hr
        simp_all
    · by_cases hr : r = j <;> by_cases hs : s = i <;>
        simp_all [Matrix.one_apply]
      exact Ne.symm hs

private lemma levi_conjugate_shear (e : Fin 2) (i j : Fin 4) (hij : i ≠ j) (a : Vec) :
    levi e i j * shear e a * (levi e i j)⁻¹ =
      shear e (a + a i • Pi.single j 1) := by
  rw [levi_inv]
  apply Subtype.ext
  change (levi e i j).val * shearMatrix e a * (levi e i j).val =
    shearMatrix e (a + a i • Pi.single j 1)
  fin_cases e
  · exact conjugate_zero i j hij a
  · exact conjugate_one i j hij a

lemma elementary_radical (e : Fin 2) : IsElementaryTwo (radical e) := by
  have square (g : radical e) : g ^ 2 = 1 := by
    obtain ⟨a, ha⟩ := (show g.val ∈ (shearHom e).range from
      (range_shearHom e).symm ▸ g.property)
    apply Subtype.ext
    change g.val ^ 2 = 1
    rw [← ha, ← map_pow]
    have hp : a ^ 2 = 1 := by
      rw [pow_two]
      change a.toAdd + a.toAdd = 0
      ext i
      exact binary_self_add _
    rw [hp, map_one]
  refine ⟨?_, { is_comm := ?_, exponent_dvd_p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr square }⟩
  · intro h
    have hc := card_radical e
    rw [h, Subgroup.card_bot] at hc
    contradiction
  · constructor
    intro a b
    have hi (g : radical e) : g⁻¹ = g :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using square g)
    calc
      a * b = (a * b)⁻¹ := (hi _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [hi, hi]

lemma radical_minimal (e : Fin 2) (K : Subgroup (parabolic e))
    (hN : K.Normal) (hK : K ≤ radical e) : K = ⊥ ∨ K = radical e := by
  classical
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  right
  have hex : ∃ g ∈ K, g ≠ 1 := by
    by_contra! hz
    exact hbot ((Subgroup.eq_bot_iff_forall _).mpr hz)
  obtain ⟨g, hg, hgne⟩ := hex
  obtain ⟨a, ha⟩ := (show g ∈ (shearHom e).range from (range_shearHom e).symm ▸ hK hg)
  let H : AddSubgroup Vec :=
    { carrier := {a | shearHom e (Multiplicative.ofAdd a) ∈ K}
      zero_mem' := by change shearHom e 1 ∈ K; rw [map_one]; exact K.one_mem
      add_mem' := by
        intro a b ha hb
        change shearHom e (Multiplicative.ofAdd a * Multiplicative.ofAdd b) ∈ K
        rw [map_mul]
        exact K.mul_mem ha hb
      neg_mem' := by
        intro a ha
        change shearHom e (Multiplicative.ofAdd a)⁻¹ ∈ K
        rw [map_inv]
        exact K.inv_mem ha }
  have hconj (v : Vec) (hv : v ∈ H) (i j : Fin 4) (hij : i ≠ j) :
      v + v i • Pi.single j 1 ∈ H := by
    have hh := hN.conj_mem (shearHom e (Multiplicative.ofAdd v)) hv
      ⟨levi e i j, levi_mem_parabolic e i j⟩
    have he : (⟨levi e i j, levi_mem_parabolic e i j⟩ : parabolic e) *
        shearHom e (Multiplicative.ofAdd v) *
        (⟨levi e i j, levi_mem_parabolic e i j⟩ : parabolic e)⁻¹ =
        shearHom e (Multiplicative.ofAdd (v + v i • Pi.single j 1)) :=
      Subtype.ext (levi_conjugate_shear e i j hij v)
    rw [he] at hh
    exact hh
  have extract (v : Vec) (hv : v ∈ H) (i j : Fin 4) (hij : i ≠ j) (hi : v i = 1) :
      Pi.single j 1 ∈ H := by
    have hh := H.sub_mem (hconj v hv i j hij) hv
    simpa only [hi, one_smul, add_sub_cancel_left] using hh
  have hav : a.toAdd ∈ H := by
    change shearHom e a ∈ K
    rwa [ha]
  have ha0 : a.toAdd ≠ 0 := by
    intro h
    have ha1 : a = 1 := Multiplicative.toAdd.injective h
    exact hgne (by rw [← ha, ha1, map_one])
  obtain ⟨i, hi⟩ : ∃ i, a.toAdd i ≠ 0 := by
    by_contra! hz
    exact ha0 (funext hz)
  have hi1 : a.toAdd i = 1 := (by decide : ∀ x : F, x ≠ 0 → x = 1) _ hi
  obtain ⟨j, hij⟩ : ∃ j : Fin 4, i ≠ j := exists_ne i |>.imp (fun _ h => h.symm)
  have hj := extract a.toAdd hav i j hij hi1
  have hall (k : Fin 4) : Pi.single k 1 ∈ H := by
    by_cases hk : j = k
    · simpa only [hk] using hj
    · exact extract (Pi.single j 1) hj j k hk (by simp)
  apply le_antisymm hK
  intro x hx
  obtain ⟨v, rfl⟩ := (show x ∈ (shearHom e).range from (range_shearHom e).symm ▸ hx)
  have hs (k : Fin 4) : Pi.single k (v.toAdd k) ∈ H := by
    by_cases hk : v.toAdd k = 0
    · simpa only [hk, Pi.single_zero] using H.zero_mem
    · have hk1 : v.toAdd k = 1 := (by decide : ∀ x : F, x ≠ 0 → x = 1) _ hk
      simpa only [hk1] using hall k
  have hv : v.toAdd ∈ H := by
    rw [← Finset.univ_sum_single v.toAdd]
    exact H.sum_mem fun k _ => hs k
  exact hv

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Geometry
