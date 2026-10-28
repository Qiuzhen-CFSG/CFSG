module
public import Theory.SpecificGroups.SL2.PairSylowTorus

/-!
# Simultaneous diagonal coordinates for odd binary Borel subgroups

The diagonal projection is injective on every odd subgroup of a binary
SL₂ Borel, since its kernel is a two-group. Such a subgroup is abelian.
A nonidentity element has distinct diagonal entries; one upper unipotent
conjugator diagonalizes it. Commutativity then diagonalizes every element
at once. Sylow conjugacy gives the intrinsic version, and projection to
each factor gives a common marking for a subgroup of the pair normalizer.

These are the common torus coordinates used in Aschbacher--Smith, 10.2.3,
printed p.745. They apply to the actual odd subgroup without a Hall or
full-torus hypothesis.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

omit [Finite F] [CharP F 2] in
private theorem triangular_diagonalize {g : SL(2,F)} (hg : g ∈ rankOneBorel F)
    (hne : g.val 0 0 ≠ g.val 1 1) :
    ∃ t : F, (u t * g * (u t)⁻¹).val 0 1 = 0 := by
  refine ⟨g.val 0 1 / (g.val 0 0 - g.val 1 1),?_⟩
  have h10 := (mem_rankOneBorel_iff g).mp hg
  simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two, transvection_coe, h10]
  field_simp
  ring

private theorem odd_borel_projection_injective (C : Subgroup SL(2,F))
    (hC : C ≤ rankOneBorel F) (ho : Odd (Nat.card C)) :
    Function.Injective (borelDiagonalProjection.comp (inclusion hC)) := by
  obtain ⟨n,hn⟩ := (upperUnipotentSylow F 2).isPGroup'.exists_card_eq
  have hdis : Disjoint (upperUnipotent F) C := disjoint_of_coprime_natCard (by
    change Nat.Coprime (Nat.card (upperUnipotentSylow F 2)) (Nat.card C)
    rw [hn]
    exact (Nat.coprime_two_left.mpr ho).pow_left n)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  exact disjoint_def.mp hdis
    ((borelDiagonalProjection_eq_one_iff (inclusion hC x)).mp hx) x.property

omit [Finite F] [CharP F 2] in
private theorem diagonal_of_offdiagonal_zero {g : SL(2,F)}
    (h10 : g.val 1 0 = 0) (h01 : g.val 0 1 = 0) :
    ∃ z : Fˣ, g = diag2 (z : F) z.ne_zero := by
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [det_fin_two,h10,mul_zero,sub_zero] using g.property
  have h11 := eq_inv_of_mul_eq_one_right hd
  refine ⟨Units.mk0 (g.val 0 0) (left_ne_zero_of_mul_eq_one hd),?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2_coe',h10,h01,h11]

/-- One unipotent conjugator puts every element of an odd Borel subgroup in
its diagonal torus. The diagonal character is retained as a homomorphism. -/
theorem odd_borel_diagonal_coordinates (C : Subgroup SL(2,F))
    (hC : C ≤ rankOneBorel F) (ho : Odd (Nat.card C)) :
    ∃ (a : SL(2,F)) (d : C →* Fˣ), a ∈ upperUnipotent F ∧
      ∀ x : C, a * x * a⁻¹ = diag2 (d x : F) (Units.ne_zero _) := by
  let f := borelDiagonalProjection.comp (inclusion hC)
  have hf : Function.Injective f := odd_borel_projection_injective C hC ho
  have hcomm (x y : C) : (x : SL(2,F)) * y = (y : SL(2,F)) * x := by
    exact congrArg Subtype.val (hf (show f (x*y) = f (y*x) by simp only [map_mul,mul_comm]))
  by_cases hbot : C = ⊥
  · refine ⟨1,1,(upperUnipotent F).one_mem,?_⟩
    intro x
    have hx : (x : SL(2,F)) = 1 := mem_bot.mp (hbot ▸ x.property)
    rw [hx,inv_one,one_mul]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe']
  obtain ⟨x,hx,hx1⟩ := C.bot_or_exists_ne_one.resolve_left hbot
  have hxN := hC hx
  have hx10 := (mem_rankOneBorel_iff x).mp hxN
  have hx00 : x.val 0 0 ≠ 1 := by
    intro he
    apply hx1
    have hu : x ∈ upperUnipotent F := by
      have h11 : x.val 1 1 = 1 := by
        simpa only [det_fin_two,he,hx10,one_mul,mul_zero,sub_zero] using x.property
      refine (mem_upperUnipotent F x).mpr ⟨x.val 0 1,?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [transvection_coe,he,h11,hx10]
    exact congrArg Subtype.val (hf (show f ⟨x,hx⟩ = f 1 by
      rw [map_one]
      exact (borelDiagonalProjection_eq_one_iff (inclusion hC ⟨x,hx⟩)).mpr hu))
  have hneq : x.val 0 0 ≠ x.val 1 1 := by
    intro he
    apply hx00
    apply (frobenius_inj F 2)
    have hd : x.val 0 0 * x.val 1 1 = 1 := by
      simpa only [det_fin_two,hx10,mul_zero,sub_zero] using x.property
    simpa [frobenius_def,pow_two,←he] using hd
  obtain ⟨t,ht⟩ := triangular_diagonalize hxN hneq
  let a := u t
  have haU : a ∈ upperUnipotent F := (mem_upperUnipotent F _).mpr ⟨t,rfl⟩
  have haN := (upperUnipotent F).le_normalizer haU
  have hconj (y : C) : a * y * a⁻¹ ∈ rankOneBorel F :=
    (rankOneBorel F).mul_mem ((rankOneBorel F).mul_mem haN (hC y.property))
      ((rankOneBorel F).inv_mem haN)
  let j : C →* rankOneBorel F :=
    ((MulAut.conj a).toMonoidHom.comp C.subtype).codRestrict _ hconj
  have hdiag (y : C) : ∃ z : Fˣ, a*y*a⁻¹ = diag2 (z : F) z.ne_zero := by
      have hc : (a*x*a⁻¹) * (a*y*a⁻¹) = (a*y*a⁻¹) * (a*x*a⁻¹) := by
        simpa only [map_mul,MulAut.conj_apply] using congrArg (MulAut.conj a) (hcomm ⟨x,hx⟩ y)
      have h00 : (a*x*a⁻¹).val 0 0 = x.val 0 0 := by
        simp [a,adjugate_fin_two,mul_apply,Fin.sum_univ_two,transvection_coe,hx10]
      have h11 : (a*x*a⁻¹).val 1 1 = x.val 1 1 := by
        simp [a,adjugate_fin_two,mul_apply,Fin.sum_univ_two,transvection_coe,hx10]
      have entry_mul (g h : SL(2,F)) : (g*h).val 0 1 =
          g.val 0 0*h.val 0 1 + g.val 0 1*h.val 1 1 := by
        simp [mul_apply,Fin.sum_univ_two]
      have he := (entry_mul (a*x*a⁻¹) (a*y*a⁻¹)).symm.trans
        ((congrArg (fun g : SL(2,F) => g.val 0 1) hc).trans
          (entry_mul (a*y*a⁻¹) (a*x*a⁻¹)))
      rw [h00,h11,ht,zero_mul,mul_zero,add_zero,zero_add] at he
      have hz : (a*y*a⁻¹).val 0 1 = 0 := by
        apply (mul_eq_zero.mp (show (x.val 0 0-x.val 1 1)*(a*y*a⁻¹).val 0 1=0 by
          linear_combination he)).resolve_left (sub_ne_zero.mpr hneq)
      exact diagonal_of_offdiagonal_zero ((mem_rankOneBorel_iff _).mp (hconj y)) hz
  have hd : Function.Injective (borelDiagonalHom (F := F)) := by
    intro z w he
    have hh := congrArg (fun x : rankOneBorel F => x.val.val 0 0) he
    apply Units.ext
    simpa [borelDiagonalHom,diag2_coe'] using hh
  let E := MonoidHom.ofInjective hd
  let k : C →* (borelDiagonalHom (F := F)).range := j.codRestrict _ (by
    intro y
    obtain ⟨z,hz⟩ := hdiag y
    exact ⟨z,Subtype.ext hz.symm⟩)
  refine ⟨a,E.symm.toMonoidHom.comp k,haU,?_⟩
  intro y
  have he := congrArg (fun x : (borelDiagonalHom (F := F)).range => x.val.val)
    (E.apply_symm_apply (k y))
  exact he.symm

/-- A single inner marking makes the specified Sylow standard and an arbitrary
odd subgroup of its normalizer diagonal. -/
theorem sylow_odd_subgroup_diagonal_coordinates (S : Sylow 2 SL(2,F))
    (C : Subgroup SL(2,F)) (hC : C ≤ normalizer (S : Set SL(2,F)))
    (ho : Odd (Nat.card C)) :
    ∃ (a : SL(2,F)) (d : C →* Fˣ),
      (S : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F ∧
      ∀ x : C, a * x * a⁻¹ = diag2 (d x : F) (Units.ne_zero _) := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  have hS : (S : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F := by
    change ((a • S : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  let Ca := C.map (MulAut.conj a).toMonoidHom
  have hCa : Ca ≤ rankOneBorel F := by
    have hh := (map_mono (f := (MulAut.conj a).toMonoidHom) hC).trans (le_normalizer_map _)
    rwa [hS] at hh
  have hoCa : Odd (Nat.card Ca) := by
    rwa [card_map_of_injective (MulAut.conj a).injective]
  obtain ⟨b,d,hb,hd⟩ := odd_borel_diagonal_coordinates Ca hCa hoCa
  refine ⟨b*a,d.comp ((MulAut.conj a).toMonoidHom.subgroupMap C),?_,?_⟩
  · have hbN : b ∈ normalizer (upperUnipotent F : Set SL(2,F)) :=
      (upperUnipotent F).le_normalizer hb
    have hmul : (MulAut.conj (b*a)).toMonoidHom =
        (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
      ext x
      simp only [MulAut.conj_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
      group
    rw [hmul,←Subgroup.map_map,hS]
    exact mem_normalizer_iff_map_conj_eq.mp hbN
  · intro x
    have hh := hd ((MulAut.conj a).toMonoidHom.subgroupMap C x)
    change b*(a*(x : SL(2,F))*a⁻¹)*b⁻¹ = _ at hh
    simpa only [_root_.mul_inv_rev,mul_assoc,MonoidHom.comp_apply] using hh

/-- The two conjugators are chosen once for the whole odd subgroup. -/
theorem pair_sylow_odd_subgroup_diagonal_coordinates
    (S : Sylow 2 (SL(2,F) × SL(2,F)))
    (C : Subgroup (SL(2,F) × SL(2,F)))
    (hC : C ≤ normalizer (S : Set (SL(2,F) × SL(2,F))))
    (ho : Odd (Nat.card C)) :
    ∃ (a b : SL(2,F)) (d : C →* Fˣ × Fˣ),
      (S : Subgroup (SL(2,F) × SL(2,F))).map
        ((MulAut.conj a).prodCongr (MulAut.conj b)).toMonoidHom =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      ∀ x : C, ((MulAut.conj a).prodCongr (MulAut.conj b)) x =
        (diag2 ((d x).1 : F) (Units.ne_zero _),
          diag2 ((d x).2 : F) (Units.ne_zero _)) := by
  let f := MonoidHom.fst SL(2,F) SL(2,F)
  let g := MonoidHom.snd SL(2,F) SL(2,F)
  let S1 := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := g) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup 2 ((S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F))) := by
    obtain ⟨m,hm⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := S2.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := m+n)
    rw [Nat.card_congr (prodEquiv (S1 : Subgroup SL(2,F)) (S2 : Subgroup SL(2,F))).toEquiv,
      Nat.card_prod,hm,hn,pow_add]
  have he : (S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F)) = (S : Subgroup (SL(2,F) × SL(2,F))) :=
    S.is_maximal' hp (by
      intro x hx
      exact ⟨mem_map_of_mem f hx,mem_map_of_mem g hx⟩)
  obtain ⟨a,d1,h1,hd1⟩ := sylow_odd_subgroup_diagonal_coordinates S1 (C.map f)
    ((map_mono hC).trans (le_normalizer_map f)) (ho.of_dvd_nat (C.card_map_dvd f))
  obtain ⟨b,d2,h2,hd2⟩ := sylow_odd_subgroup_diagonal_coordinates S2 (C.map g)
    ((map_mono hC).trans (le_normalizer_map g)) (ho.of_dvd_nat (C.card_map_dvd g))
  refine ⟨a,b,(d1.comp (f.subgroupMap C)).prod (d2.comp (g.subgroupMap C)),?_,?_⟩
  · rw [←he]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨h1 ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hy.1,
        h2 ▸ mem_map_of_mem (MulAut.conj b).toMonoidHom hy.2⟩
    · intro hx
      have hx1 : x.1 ∈ (S1 : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom := h1.symm ▸ hx.1
      have hx2 : x.2 ∈ (S2 : Subgroup SL(2,F)).map (MulAut.conj b).toMonoidHom := h2.symm ▸ hx.2
      obtain ⟨y1,hy1,hxy1⟩ := hx1
      obtain ⟨y2,hy2,hxy2⟩ := hx2
      exact ⟨(y1,y2),⟨hy1,hy2⟩,Prod.ext hxy1 hxy2⟩
  · intro x
    exact Prod.ext (hd1 (f.subgroupMap C x)) (hd2 (g.subgroupMap C x))

end Matrix.SpecialLinearGroup
