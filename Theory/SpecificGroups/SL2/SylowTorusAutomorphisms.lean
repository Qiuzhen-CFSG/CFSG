module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
/-!
# Automorphisms preserving a binary Sylow and its split torus

An automorphism of SL₂ over a finite field of characteristic two is inner
followed by a field automorphism. Preservation of the upper root group puts
the inner factor in its Borel. If the full split torus is also preserved,
a nonidentity torus element forces the off-diagonal entry to vanish.
For a product of two such groups, preservation of the first factor forces
preservation of its centralizer, the second factor. Thus the same marking
realizes the automorphism by two diagonal inner factors and two field factors.
Restriction to the full torus determines those field factors uniquely, and
hence assembles them into a homomorphism for any group of such actors.

Source: the automorphism decomposition in Aschbacher--Smith 10.2.3, printed
p.745. The field factors are retained; their elimination uses the original
module and centralizing-omega-center hypotheses.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
open BenderSuzuki.ZD.Linear
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem sl2_semilinear_coverage (a : MulAut SL(2,F)) :
    ∃ (g : SL(2,F)) (σ : F ≃+* F), a = MulAut.conj g * sl2FieldAut σ := by
  obtain ⟨g,b,he,hU,hw⟩ := exists_root_weyl_normalization a
  obtain ⟨σ,hσ⟩ := eq_sl2FieldAut_of_rootParameter_mul b hU hw (rootParameter_mul b hU hw)
  exact ⟨g,σ,hσ ▸ he⟩

omit [Finite F] [CharP F 2] in
theorem sl2FieldAut_diagonal (σ : F ≃+* F) (z : Fˣ) :
    sl2FieldAut σ (diag2 (z:F) z.ne_zero) =
      diag2 (σ (z:F)) ((map_ne_zero σ).2 z.ne_zero) := by
  apply Subtype.ext
  ext i j
  change σ ((diag2 (z:F) z.ne_zero).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [diag2_coe']

omit [Finite F] [CharP F 2] in
theorem sl2FieldAut_map_upper (σ : F ≃+* F) :
    (upperUnipotent F).map (sl2FieldAut σ).toMonoidHom = upperUnipotent F := by
  have he (τ : F ≃+* F) (t : F) :
      sl2FieldAut τ (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t) =
        transvection zero_ne_one (τ t) := by
    apply Subtype.ext
    ext i j
    change τ ((transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t).val i j) = _
    fin_cases i <;> fin_cases j <;> simp [transvection_coe]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
    rw [MulEquiv.coe_toMonoidHom,he]
    exact (mem_upperUnipotent F _).mpr ⟨σ t,rfl⟩
  · intro x hx
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
    refine ⟨transvection zero_ne_one (σ.symm t), (mem_upperUnipotent F _).mpr ⟨_,rfl⟩,?_⟩
    rw [MulEquiv.coe_toMonoidHom,he,σ.apply_symm_apply]

theorem borel_torus_preserver_diagonal (hF : 2 < Nat.card F) (g : SL(2,F))
    (hg : g ∈ rankOneBorel F)
    (hD : ∀ z : Fˣ, ∃ w : Fˣ,
      g * diag2 (z:F) z.ne_zero * g⁻¹ = diag2 (w:F) w.ne_zero) :
    ∃ a : Fˣ, g = diag2 (a:F) a.ne_zero := by
  have h10 := (mem_rankOneBorel_iff g).mp hg
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [det_fin_two,h10,mul_zero,sub_zero] using g.property
  have h00 : g.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨z,hz⟩ := exists_ne (1:Fˣ)
  obtain ⟨w,hw⟩ := hD z
  have he := mul_inv_eq_iff_eq_mul.mp hw
  have he0 := congrArg (fun x : SL(2,F) => x.val 0 0) he
  have hzw : (z:F) = (w:F) := by
    apply mul_left_cancel₀ h00
    simpa [mul_apply,Fin.sum_univ_two,diag2_coe',mul_comm] using he0
  have he1 := congrArg (fun x : SL(2,F) => x.val 0 1) he
  have he1' : g.val 0 1 * ((z:F)⁻¹-(z:F)) = 0 := by
    have hh : g.val 0 1 * (z:F)⁻¹ = (z:F) * g.val 0 1 := by
      simpa [mul_apply,Fin.sum_univ_two,diag2_coe',←hzw] using he1
    linear_combination hh
  have hz' : (z:F)⁻¹-(z:F) ≠ 0 := by
    intro hh
    have hs : (z:F)^2 = 1 := by
      calc
        (z:F)^2 = (z:F) * (z:F)⁻¹ := by rw [pow_two,sub_eq_zero.mp hh]
        _ = 1 := mul_inv_cancel₀ z.ne_zero
    have hz1 : (z:F) = 1 := by
      rcases sq_eq_one_iff.mp hs with h | h
      · exact h
      · simpa only [CharTwo.neg_eq] using h
    exact hz (Units.ext hz1)
  have h01 := (mul_eq_zero.mp he1').resolve_right hz'
  refine ⟨Units.mk0 (g.val 0 0) h00,?_⟩
  have h11 := eq_inv_of_mul_eq_one_right hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2_coe',h10,h01,h11]

theorem sylow_torus_preserving_semilinear (hF : 2 < Nat.card F) (α : MulAut SL(2,F))
    (hU : (upperUnipotent F).map α.toMonoidHom = upperUnipotent F)
    (hD : ∀ z : Fˣ, ∃ w : Fˣ, α (diag2 (z:F) z.ne_zero) = diag2 (w:F) w.ne_zero) :
    ∃ (a : Fˣ) (σ : F ≃+* F),
      α = MulAut.conj (diag2 (a:F) a.ne_zero) * sl2FieldAut σ := by
  obtain ⟨g,σ,rfl⟩ := sl2_semilinear_coverage α
  have hg : g ∈ rankOneBorel F := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (upperUnipotent F).map
      ((MulAut.conj g).toMonoidHom.comp (sl2FieldAut σ).toMonoidHom) = _ at hU
    rwa [←Subgroup.map_map,sl2FieldAut_map_upper] at hU
  obtain ⟨a,ha⟩ := borel_torus_preserver_diagonal hF g hg (fun z => by
    obtain ⟨w,hw⟩ := hD (Units.map σ.symm.toMonoidHom z)
    refine ⟨w,?_⟩
    change g * sl2FieldAut σ _ * g⁻¹ = _ at hw
    rw [sl2FieldAut_diagonal] at hw
    change g * diag2 (σ (σ.symm (z:F))) _ * g⁻¹ = _ at hw
    simpa only [σ.apply_symm_apply] using hw)
  exact ⟨a,σ,by rw [ha]⟩

private theorem exists_second_factor (e : MulAut (SL(2,F) × SL(2,F)))
    (a : MulAut SL(2,F)) (ha : ∀ x, e (x,1) = (a x,1)) :
    ∃ b : MulAut SL(2,F), ∀ x, e x = (a x.1,b x.2) := by
  have hz (y : SL(2,F)) : (e (1,y)).1 = 1 := by
    apply (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F)).le
    apply Subgroup.mem_center_iff.mpr
    intro x
    obtain ⟨z,rfl⟩ := a.surjective x
    have hc : (z,1) * (1,y) = (1,y) * (z,1) := by simp
    have he := congrArg e hc
    rw [map_mul,map_mul,ha] at he
    exact congrArg Prod.fst he
  let f := (MonoidHom.snd SL(2,F) SL(2,F)).comp
    (e.toMonoidHom.comp (MonoidHom.inr SL(2,F) SL(2,F)))
  have hf : Function.Injective f := by
    intro x y hxy
    have he : e (1,x) = e (1,y) := Prod.ext ((hz x).trans (hz y).symm) hxy
    exact congrArg Prod.snd (e.injective he)
  let b := MulEquiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  refine ⟨b,fun x => ?_⟩
  have he : x = (x.1,1) * (1,x.2) := by simp
  rw [he,map_mul,ha]
  exact Prod.ext (by simp [hz]) (by simp [b,f])

theorem pair_sylow_torus_preserving_semilinear (hF : 2 < Nat.card F)
    (e : MulAut (SL(2,F) × SL(2,F)))
    (a : MulAut SL(2,F)) (ha : ∀ x, e (x,1) = (a x,1))
    (hU : ((upperUnipotent F).prod (upperUnipotent F)).map e.toMonoidHom =
      (upperUnipotent F).prod (upperUnipotent F))
    (hD : ∀ z : Fˣ × Fˣ, ∃ w : Fˣ × Fˣ,
      e (diag2 (z.1:F) z.1.ne_zero,diag2 (z.2:F) z.2.ne_zero) =
        (diag2 (w.1:F) w.1.ne_zero,diag2 (w.2:F) w.2.ne_zero)) :
    ∃ (d : Fˣ × Fˣ) (σ τ : F ≃+* F),
      e = (MulAut.conj (diag2 (d.1:F) d.1.ne_zero) * sl2FieldAut σ).prodCongr
        (MulAut.conj (diag2 (d.2:F) d.2.ne_zero) * sl2FieldAut τ) := by
  obtain ⟨b,hb⟩ := exists_second_factor e a ha
  have hu (j : MulAut SL(2,F))
      (hj : ∀ x ∈ upperUnipotent F, j x ∈ upperUnipotent F) :
      (upperUnipotent F).map j.toMonoidHom = upperUnipotent F := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      exact hj x hx
    · rw [card_map_of_injective j.injective]
  have haU : (upperUnipotent F).map a.toMonoidHom = upperUnipotent F :=
    hu a (fun x hx => by
      have hh := hU ▸ mem_map_of_mem e.toMonoidHom
        (show (x,1) ∈ (upperUnipotent F).prod (upperUnipotent F) from
          ⟨hx,(upperUnipotent F).one_mem⟩)
      change e (x,1) ∈ _ at hh
      rw [ha] at hh
      exact hh.1)
  have hbU : (upperUnipotent F).map b.toMonoidHom = upperUnipotent F :=
    hu b (fun x hx => by
      have hh := hU ▸ mem_map_of_mem e.toMonoidHom
        (show (1,x) ∈ (upperUnipotent F).prod (upperUnipotent F) from
          ⟨(upperUnipotent F).one_mem,hx⟩)
      change e (1,x) ∈ _ at hh
      rw [hb] at hh
      exact hh.2)
  obtain ⟨d1,σ,hd1⟩ := sylow_torus_preserving_semilinear hF a haU (fun z => by
    obtain ⟨w,hw⟩ := hD (z,1)
    rw [hb] at hw
    exact ⟨w.1,congrArg Prod.fst hw⟩)
  obtain ⟨d2,τ,hd2⟩ := sylow_torus_preserving_semilinear hF b hbU (fun z => by
    obtain ⟨w,hw⟩ := hD (1,z)
    rw [hb] at hw
    exact ⟨w.2,congrArg Prod.snd hw⟩)
  refine ⟨(d1,d2),σ,τ,?_⟩
  rw [←hd1,←hd2]
  exact MulEquiv.ext hb
end Matrix.SpecialLinearGroup

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open BenderSuzuki.ZD.Linear
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "diag" => fun z : Fˣ => diag2 (z:F) (Units.ne_zero z)

theorem diagonal_field_apply_diagonal (d z : Fˣ) (σ : F ≃+* F) :
    (MulAut.conj (diag d) * sl2FieldAut σ) (diag z) =
      diag (Units.map σ.toMonoidHom z) := by
  change diag d * sl2FieldAut σ (diag z) * (diag d)⁻¹ = _
  rw [sl2FieldAut_diagonal]
  let f : Fˣ →* SL(2,F) := (rankOneBorel F).subtype.comp borelDiagonalHom
  change f d * f (Units.map σ.toMonoidHom z) * (f d)⁻¹ = f (Units.map σ.toMonoidHom z)
  rw [←map_inv,←map_mul,←map_mul]
  congr 1
  simp only [mul_comm d, mul_inv_cancel_right]

private theorem pair_field_unique
    (f : SL(2,F) × SL(2,F) → SL(2,F) × SL(2,F))
    (a b : (F ≃+* F) × (F ≃+* F))
    (ha : ∀ z : Fˣ × Fˣ, f (diag z.1,diag z.2) =
      (diag (Units.map a.1.toMonoidHom z.1),diag (Units.map a.2.toMonoidHom z.2)))
    (hb : ∀ z : Fˣ × Fˣ, f (diag z.1,diag z.2) =
      (diag (Units.map b.1.toMonoidHom z.1),diag (Units.map b.2.toMonoidHom z.2))) : a = b := by
  have he (z : Fˣ × Fˣ) := (ha z).symm.trans (hb z)
  apply Prod.ext
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · have hh := congrArg (fun p : SL(2,F) × SL(2,F) => p.1.val 0 0)
        (he (Units.mk0 x hx,1))
      simpa [diag2_coe'] using hh
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · have hh := congrArg (fun p : SL(2,F) × SL(2,F) => p.2.val 0 0)
        (he (1,Units.mk0 x hx))
      simpa [diag2_coe'] using hh

variable {A : Type*} [Group A]

theorem exists_pair_torus_field_action (ρ : A →* MulAut (SL(2,F) × SL(2,F)))
    (h : ∀ b : A, ∃ s : (F ≃+* F) × (F ≃+* F),
      ∀ z : Fˣ × Fˣ, ρ b (diag z.1,diag z.2) =
        (diag (Units.map s.1.toMonoidHom z.1),diag (Units.map s.2.toMonoidHom z.2))) :
    ∃ φ : A →* ((F ≃+* F) × (F ≃+* F)),
      ∀ (b : A) (z : Fˣ × Fˣ), ρ b (diag z.1,diag z.2) =
        (diag (Units.map (φ b).1.toMonoidHom z.1),diag (Units.map (φ b).2.toMonoidHom z.2)) := by
  let φ : A →* ((F ≃+* F) × (F ≃+* F)) := {
    toFun b := (h b).choose
    map_one' := pair_field_unique (ρ 1) (h 1).choose 1 (h 1).choose_spec (by
      intro z
      rw [map_one]
      rfl)
    map_mul' b c := pair_field_unique (ρ (b*c)) (h (b*c)).choose
      ((h b).choose * (h c).choose) (h (b*c)).choose_spec (by
        intro z
        rw [map_mul]
        change ρ b (ρ c (diag z.1,diag z.2)) = _
        rw [(h c).choose_spec z, (h b).choose_spec
          (Units.map (h c).choose.1.toMonoidHom z.1,
           Units.map (h c).choose.2.toMonoidHom z.2)]
        rfl) }
  exact ⟨φ,fun b => (h b).choose_spec⟩

theorem exists_pair_diagonal_field_hom (ρ : A →* MulAut (SL(2,F) × SL(2,F)))
    (h : ∀ b : A, ∃ (d : Fˣ × Fˣ) (σ τ : F ≃+* F),
      ρ b = (MulAut.conj (diag d.1) * sl2FieldAut σ).prodCongr
        (MulAut.conj (diag d.2) * sl2FieldAut τ)) :
    ∃ φ : A →* ((F ≃+* F) × (F ≃+* F)),
      (∀ (b : A) (z : Fˣ × Fˣ), ρ b (diag z.1,diag z.2) =
        (diag (Units.map (φ b).1.toMonoidHom z.1),diag (Units.map (φ b).2.toMonoidHom z.2))) ∧
      ∀ b : A, ∃ d : Fˣ × Fˣ,
        ρ b = (MulAut.conj (diag d.1) * sl2FieldAut (φ b).1).prodCongr
          (MulAut.conj (diag d.2) * sl2FieldAut (φ b).2) := by
  have hd (b : A) (d : Fˣ × Fˣ) (σ τ : F ≃+* F)
      (he : ρ b = (MulAut.conj (diag d.1) * sl2FieldAut σ).prodCongr
        (MulAut.conj (diag d.2) * sl2FieldAut τ)) :
      ∀ z : Fˣ × Fˣ, ρ b (diag z.1,diag z.2) =
        (diag (Units.map σ.toMonoidHom z.1),diag (Units.map τ.toMonoidHom z.2)) := by
    intro z
    rw [he]
    exact Prod.ext (diagonal_field_apply_diagonal d.1 z.1 σ)
      (diagonal_field_apply_diagonal d.2 z.2 τ)
  obtain ⟨φ,hφ⟩ := exists_pair_torus_field_action ρ (fun b => by
    obtain ⟨d,σ,τ,he⟩ := h b
    exact ⟨(σ,τ),hd b d σ τ he⟩)
  refine ⟨φ,hφ,fun b => ?_⟩
  obtain ⟨d,σ,τ,he⟩ := h b
  have hs : φ b = (σ,τ) := pair_field_unique (ρ b) (φ b) (σ,τ) (hφ b) (hd b d σ τ he)
  exact ⟨d,by rw [hs]; exact he⟩
end Matrix.SpecialLinearGroup
