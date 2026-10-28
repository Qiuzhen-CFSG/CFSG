module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import Mathlib.LinearAlgebra.Transvection.Basic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.OddField
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.PrimeResidual
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Odd-prime displacement on the natural SL₃ automizer

A determinant-one odd-order operator cannot have displacement rank one:
the rank-one normal form and determinant make it a transvection, of order
two in characteristic two. Restricting scalars gives the inner bound 2n.

For the full automizer, semilinearity separates the field actors, treated
by descent, from the linear kernel. Its determinant is a homomorphism to
the field units. Nontrivial prime-order determinant forces p to divide
q−1, so source 11.0.4 excludes it when p>3. If n is odd, three does not
divide q−1 either. The Source endpoint completes FixedCodimensions and
applies the residual consumer in that row. The even-degree cubic case
retains its separate source obligation.

All actions use the literal faithful natural quotient and projection of
V; no scalar or diagonal exclusion is assumed for arbitrary normalizers.
Source: Aschbacher--Smith, I.2.3, 11.0.4 and 11.2.2, pp.413,760,767--768.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem specialLinear_odd_rank {d : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin d) F) (hg : g ≠ 1) (ho : Odd (orderOf g)) :
    2 ≤ Module.finrank F ((specialLinearNatural d g - LinearMap.id).range) := by
  classical
  by_contra hn
  have hr : Module.finrank F ((Matrix.SpecialLinearGroup.toLin' g).toLinearMap -
      LinearMap.id).range ≤ 1 := by
    change Module.finrank F ((specialLinearNatural d g - LinearMap.id).range) ≤ 1
    omega
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr
  have hd : LinearMap.det (Matrix.SpecialLinearGroup.toLin' g).toLinearMap = 1 := by
    change LinearMap.det (Matrix.toLin' g.val) = 1
    rw [LinearMap.det_toLin']
    exact g.property
  rw [he, LinearMap.transvection.det] at hd
  have hfv : f v = 0 := by linear_combination hd
  have hg2 : g ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_pow,map_one]
    apply LinearEquiv.ext
    intro w
    have he' (x : Fin d → F) : Matrix.SpecialLinearGroup.toLin' g x = x + f x • v :=
      LinearMap.congr_fun he x
    change Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' g w) = w
    rw [he',he']
    simp only [map_add,map_smul,hfv,smul_zero,add_zero]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have hord := orderOf_dvd_of_pow_eq_one hg2
  have heq := Nat.eq_one_of_dvd_coprimes ho.coprime_two_right (dvd_refl _) hord
  exact hg (orderOf_eq_one_iff.mp heq)

/-- A nonidentity odd-order determinant-one actor moves at least two field
dimensions. Rank one would make it a characteristic-two transvection. -/
theorem specialLinear_odd_lower {d : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin d) F) (hg : g ≠ 1) (ho : Odd (orderOf g)) :
    2 * Module.finrank (ZMod 2) F ≤
      fixedCodim (restrictScalars (k := ZMod 2) (specialLinearNatural d)) (zpowers g) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  let δ := specialLinearNatural d g - LinearMap.id
  change 2 * Module.finrank (ZMod 2) F ≤ Module.finrank (ZMod 2) (δ.restrictScalars (ZMod 2)).range
  rw [LinearMap.range_restrictScalars,
    ((δ.range.restrictScalarsEquiv (ZMod 2)).restrictScalars (ZMod 2)).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F δ.range]
  simpa only [Nat.mul_comm] using
    Nat.mul_le_mul_left (Module.finrank (ZMod 2) F) (specialLinear_odd_rank g hg ho)


open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Inner odd-prime actors in the actual SL₃ automizer satisfy the source
bound on the original module, through its specified coordinate projection. -/
theorem sl3_inner_odd_prime_lower
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      a ∈ inducedAutomizer V L →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha haL
  let c := Coordinates.sl3 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let ρ3 : Representation (ZMod 2) (Automizer V) (Fin 3 → S.field.Carrier) := ρ
  let e3 : inducedAutomizer V L ≃* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier :=
    layerEquiv D S c
  have hres3 (x : inducedAutomizer V L) (v : Fin 3 → S.field.Carrier) :
      ρ3 (x : Automizer V) v = specialLinearNatural 3 (e3 x) v := hres x v
  let g := e3 ⟨a,haL⟩
  have hg : orderOf g = p := by
    rw [e3.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ha
  have hg1 : g ≠ 1 := by intro h; simp only [h,orderOf_one] at hg; exact hp.ne_one hg.symm
  have hgo : Odd (orderOf g) := hg.symm ▸ ho
  have hd := specialLinear_odd_lower g hg1 hgo
  have hfix : fixedSpace ρ3 (zpowers a) =
      fixedSpace (restrictScalars (k := ZMod 2) (specialLinearNatural 3)) (zpowers g) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff,mem_fixedSpace_zpowers_iff]
    exact (congrArg (· = v) (hres3 ⟨a,haL⟩ v)).to_iff
  have hcod : fixedCodim ρ3 (zpowers a) =
      fixedCodim (restrictScalars (k := ZMod 2) (specialLinearNatural 3)) (zpowers g) := by
    unfold fixedCodim
    rw [hfix]
  rw [← hcod, Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hd
  exact hd.trans (fixedCodim_le_of_equivariant_surjection
    (automizerRepresentation V) ρ3 (projectionLinear D S c)
    (projectionLinear_surjective D S c) he (zpowers a))

/-- Every prime greater than three satisfies the full SL₃ source bound.
A field actor is handled by descent. A linear actor with nontrivial determinant
would have a source prime dividing q−1, so 11.0.4 places it in the actual layer. -/
private theorem sl3_odd_prime_lower_of_source_range
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → (3 < p ∨ ¬ p ∣ 2 ^ S.field.degree - 1) →
      ∀ a : Automizer V, orderOf a = p →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho hcase a ha
  let c := Coordinates.sl3 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let ρ3 : Representation (ZMod 2) (Automizer V) (Fin 3 → S.field.Carrier) := ρ
  let e3 : inducedAutomizer V L ≃* Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier :=
    layerEquiv D S c
  have hres3 (x : inducedAutomizer V L) (v : Fin 3 → S.field.Carrier) :
      ρ3 (x : Automizer V) v = specialLinearNatural 3 (e3 x) v := hres x v
  let := layer_normal D S
  let hsemi := SL3OddNaturalNormalizer.normalizer_semilinear
    (inducedAutomizer V L) e3 ρ3 hres3
  let φ := SL3OddNaturalNormalizer.fieldAction ρ3 hsemi
  by_cases hφ : φ a = 1
  · have haK : a ∈ φ.ker := hφ
    let τ : Representation S.field.Carrier φ.ker (Fin 3 → S.field.Carrier) := {
      toFun g := {
        toFun := ρ3 (g : Automizer V)
        map_add' := (ρ3 (g : Automizer V)).map_add
        map_smul' := by
          intro r v
          exact (SL3OddNaturalNormalizer.fieldAction_eq_one_iff ρ3 hsemi g).mp g.property r v }
      map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ρ3.map_one v
      map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (ρ3.map_mul g h) v }
    let μ : φ.ker →* Matrix.GeneralLinearGroup (Fin 3) S.field.Carrier :=
      Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp τ.asGroupHom
    let δ := Matrix.GeneralLinearGroup.det.comp μ
    let x : φ.ker := ⟨a,haK⟩
    have hμ (b : φ.ker) (v : Fin 3 → S.field.Carrier) : (μ b).val.mulVec v = ρ3 (b : Automizer V) v := by
      change (Matrix.GeneralLinearGroup.toLin (μ b) : Module.End S.field.Carrier (Fin 3 → S.field.Carrier)) v = _
      have heμ : Matrix.GeneralLinearGroup.toLin (μ b) = τ.asGroupHom b :=
        Matrix.GeneralLinearGroup.toLin.apply_symm_apply _
      rw [heμ]
      rfl
    have haL : a ∈ inducedAutomizer V L := by
      by_cases hd : δ x = 1
      · have hd' : (μ x).val.det = 1 := congrArg Units.val hd
        let g : Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier := ⟨(μ x).val,hd'⟩
        have hae : a = e3.symm g := by
          apply (show Function.Injective ρ3 from hρ)
          apply LinearMap.ext
          intro v
          rw [hres3, e3.apply_symm_apply]
          exact (hμ x v).symm
        rw [hae]
        exact (e3.symm g).property
      · have hδp : δ x ^ p = 1 := by
          rw [← map_pow]
          have hxp : x ^ p = 1 := Subtype.ext (ha ▸ pow_orderOf_eq_one a)
          rw [hxp,map_one]
        let : Fact p.Prime := ⟨hp⟩
        have hδo : orderOf (δ x) = p := orderOf_eq_prime hδp hd
        have hdiv : p ∣ 2 ^ S.field.degree - 1 := by
          have hh := orderOf_dvd_natCard (δ x)
          rwa [hδo,Nat.card_units,S.field.card_eq] at hh
        rcases hcase with hp3 | hnot
        · exact automizer_orderPrime_mem_layer D S hp (Or.inr ⟨⟨m⟩,hp3,hdiv⟩) ha
        · exact (hnot hdiv).elim
    exact sl3_inner_odd_prime_lower D S m p hp ho a ha haL
  · have hd := odd_field_lower ρ3 hp ho a ha (φ a) hφ
      (SL3OddNaturalNormalizer.fieldAction_smul ρ3 hsemi a)
    have hdim : Module.finrank S.field.Carrier (Fin 3 → S.field.Carrier) = 3 := by
      simp only [Module.finrank_pi,Fintype.card_fin]
    rw [hdim, Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hd
    have hsmall : 2 * S.field.degree ≤ fixedCodim ρ3 (zpowers a) := by omega
    exact hsmall.trans (fixedCodim_le_of_equivariant_surjection
      (automizerRepresentation V) ρ3 (projectionLinear D S c)
      (projectionLinear_surjective D S c) he (zpowers a))

/-- The source bound for every prime above three, on the literal full SL₃ automizer. -/
theorem sl3_odd_prime_lower_of_gt_three
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → 3 < p → ∀ a : Automizer V, orderOf a = p →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp hp3 a ha
  exact sl3_odd_prime_lower_of_source_range D S m p hp
    (hp.odd_of_ne_two (by omega)) (Or.inl hp3) a ha

/-- For odd coefficient degree all odd-prime actors satisfy the source bound;
three does not divide q−1, so the determinant obstruction is absent. -/
theorem sl3_odd_prime_lower_of_odd_degree
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hn : Odd S.field.degree) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha
  apply sl3_odd_prime_lower_of_source_range D S m p hp ho _ a ha
  by_cases hp3 : p = 3
  · right
    have hm : 2 ^ S.field.degree % 3 = 2 := by
      obtain ⟨k,hk⟩ := hn
      have he : S.field.degree = 2 * k + 1 := by omega
      rw [he,pow_add,pow_mul]
      norm_num [Nat.mul_mod,Nat.pow_mod]
    intro hd
    rw [hp3] at hd
    have hd' := Nat.dvd_iff_mod_eq_zero.mp hd
    have hh : 0 < 2 ^ S.field.degree := pow_pos (by decide) _
    have hsub : 2 ^ S.field.degree - 1 + 1 = 2 ^ S.field.degree := Nat.sub_add_cancel hh
    have hs := congrArg (fun k : ℕ => k % 3) hsub
    rw [Nat.add_mod,hd',hm] at hs
    norm_num at hs
  · left
    have htwo := hp.two_le
    obtain ⟨k,hk⟩ := ho
    omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
