module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanFlag
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Common field powers on the original Hall torsion

Simultaneous alignment puts the original inner Sylow in the standard
unipotent group and the literal Hall p-torsion in the diagonal torus.
The same original Sylow element acts semilinearly and preserves the
intrinsic complete flag. Removing its coefficient twist gives an
invertible triangular matrix, hence every diagonal entry is nonzero.
The diagonal entries of the intertwining identity therefore give one
common coefficient automorphism on the torsion. Over the finite binary
field this is a Frobenius power, and odd-primary quotient injectivity
lifts it to the same conjugation in the ambient group.

The Sp4 matrices keep their original Fin 2 + Fin 2 indices. Only the
triangular determinant argument uses the flag order e0,e1,f1,f0.
There is no coordinate, field-action or whole-Hall abelianness premise
in either source application. CartanExclusion applies these results to
the Hall prime constructed from the actual paired component.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Matrix Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Remove the coefficient twist from the original additive operator. -/
private def untwistedOperator (e : (ι → F) ≃+ (ι → F)) (σ : F ≃+* F)
    (he : ∀ a v, e (a • v) = σ a • e v) : (ι → F) →ₗ[F] (ι → F) where
  toFun v := e (fun i => σ.symm (v i))
  map_add' v w := by
    simp only [Pi.add_apply,map_add]
    exact map_add e _ _
  map_smul' a v := by
    change e (fun i => σ.symm (a * v i)) = a • e (fun i => σ.symm (v i))
    simp only [map_mul]
    change e (σ.symm a • (fun i => σ.symm (v i))) = _
    rw [he,σ.apply_symm_apply]

private theorem exists_semilinear_matrix (e : (ι → F) ≃+ (ι → F)) (σ : F ≃+* F)
    (he : ∀ a v, e (a • v) = σ a • e v) :
    ∃ g : Matrix ι ι F, g.det ≠ 0 ∧
      (∀ v, e v = g.mulVec (fun i => σ (v i))) ∧
      ∀ i j, g i j = e (Pi.single j 1) i := by
  let f := untwistedOperator e σ he
  have hi : Function.Injective f := by
    intro v w hvw
    have h := e.injective hvw
    funext i
    exact σ.symm.injective (congrFun h i)
  have hu : IsUnit (LinearMap.toMatrix' f) := LinearMap.isUnit_toMatrix'_iff.mpr
    ((LinearMap.isUnit_iff_ker_eq_bot f).mpr (LinearMap.ker_eq_bot.mpr hi))
  refine ⟨LinearMap.toMatrix' f,(Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero,?_,?_⟩
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    change e v = e (fun i => σ.symm (σ (v i)))
    simp only [σ.symm_apply_apply]
  · intro i j
    rw [LinearMap.toMatrix'_apply]
    change e (fun k => σ.symm ((Pi.single j (1 : F) : ι → F) k)) i = e (Pi.single j 1) i
    apply congrArg (fun v : ι → F => e v i)
    funext k
    by_cases h : j = k
    · subst k; simp
    · simp [h]

/-- A compatible additive intertwiner gives the literal matrix identity
for its unique coefficient twist. -/
private theorem semilinear_matrix_intertwines
    (e : (ι → F) ≃+ (ι → F)) (σ : F ≃+* F) (g : Matrix ι ι F)
    (he : ∀ v, e v = g.mulVec (fun i => σ (v i)))
    (a b : Matrix ι ι F) (hab : ∀ v, e (a.mulVec v) = b.mulVec (e v)) :
    g * a.map σ = b * g := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have hh := hab (Pi.single j 1)
  rw [he,he] at hh
  have hm (v : ι → F) : (fun i => σ (a.mulVec v i)) =
      (a.map σ).mulVec (fun i => σ (v i)) := by
    funext i
    exact σ.toRingHom.map_mulVec a v i
  have hs : (fun i => σ ((Pi.single j (1 : F) : ι → F) i)) = Pi.single j 1 := by
    funext i
    by_cases h : j = i
    · subst i; simp
    · simp [h]
  rw [hm,hs] at hh
  simpa only [mulVec_mulVec] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
open Matrix
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {F : Type*} [Field F]

private theorem diagonal_nonzero_of_triangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (g : Matrix ι ι F) (h : g.IsUpperTriangular) (hd : g.det ≠ 0) :
    ∀ i, g i i ≠ 0 := by
  rw [det_of_isUpperTriangular h,Finset.prod_ne_zero_iff] at hd
  exact fun i => hd i (Finset.mem_univ i)

private theorem sl3_diagonal_nonzero
    (e : (Fin 3 → F) ≃+ (Fin 3 → F)) (g : Matrix (Fin 3) (Fin 3) F)
    (hd : g.det ≠ 0) (he : ∀ i j, g i j = e (Pi.single j 1) i)
    (hp : ∀ v ∈ SL3.Model.point, e v ∈ SL3.Model.point)
    (hl : ∀ v ∈ SL3.Model.plane, e v ∈ SL3.Model.plane) :
    ∀ i, g i i ≠ 0 := by
  have hp0 := hp (Pi.single 0 1) (by simp [SL3.Model.mem_point])
  have hl1 := hl (Pi.single 1 1) (by simp [SL3.Model.mem_plane])
  have h10 : g 1 0 = 0 := (he 1 0).trans hp0.1
  have h20 : g 2 0 = 0 := (he 2 0).trans hp0.2
  have h21 : g 2 1 = 0 := (he 2 1).trans hl1
  apply diagonal_nonzero_of_triangular g _ hd
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The symplectic flag orders the coordinates as e₀,e₁,f₁,f₀.
Only the determinant argument uses this order; the matrices retain their
original Fin 2 + Fin 2 indices throughout. -/
private theorem sp4_diagonal_nonzero [Finite F] [CharP F 2]
    (e : ((Fin 2 ⊕ Fin 2) → F) ≃+ ((Fin 2 ⊕ Fin 2) → F))
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hd : g.det ≠ 0) (he : ∀ i j, g i j = e (Pi.single j 1) i)
    (hf : ∀ i : Fin 4, ∀ v ∈ Sp4.ModelFlag.stage i, e v ∈ Sp4.ModelFlag.stage i) :
    ∀ i, g i i ≠ 0 := by
  let key : Fin 2 ⊕ Fin 2 → ℕ := Sum.elim (fun i => i.val) (fun i => 3-i.val)
  have hinj : Function.Injective key := by
    intro i j h
    rcases i with i|i <;> rcases j with j|j <;>
      fin_cases i <;> fin_cases j <;> simp_all [key]
  have hp0 := hf 1 (Pi.single (.inl 0) 1) (by
    change Pi.single (.inl 0) 1 ∈ Theory.SpecificGroups.SymplecticFour.point F
    rw [Theory.SpecificGroups.SymplecticFour.mem_point_iff]
    simp)
  have hp := (Theory.SpecificGroups.SymplecticFour.mem_point_iff _).mp hp0
  have hl1 := hf 2 (Pi.single (.inl 1) 1) (by
    change ∀ i : Fin 2, (Pi.single (Sum.inl (1 : Fin 2)) (1 : F) : (Fin 2 ⊕ Fin 2) → F) (Sum.inr i) = 0
    simp)
  have hh1 := hf 3 (Pi.single (.inr 1) 1)
    ((Sp4.ModelFlag.mem_hyperplane (F := F) _).mpr (by simp))
  have hhh := (Sp4.ModelFlag.mem_hyperplane (F := F) _).mp hh1
  have h10 : g (.inl 1) (.inl 0) = 0 := (he _ _).trans hp.1
  have h20 : g (.inr 1) (.inl 0) = 0 := (he _ _).trans (hp.2 1)
  have h30 : g (.inr 0) (.inl 0) = 0 := (he _ _).trans (hp.2 0)
  have h21 : g (.inr 1) (.inl 1) = 0 := (he _ _).trans (hl1 1)
  have h31 : g (.inr 0) (.inl 1) = 0 := (he _ _).trans (hl1 0)
  have h32 : g (.inr 0) (.inr 1) = 0 := (he _ _).trans hhh
  let : LinearOrder (Fin 2 ⊕ Fin 2) := LinearOrder.lift' key hinj
  apply diagonal_nonzero_of_triangular g _ hd
  intro i j hij
  change key j < key i at hij
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> simp_all [key]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
open Matrix Subgroup Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

omit [Finite G] in
private theorem diagonal_field_action
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (A L : Subgroup G) (p : ℕ) (hL : primeTorsion A p ≤ L)
    (t : G) (htA : t ∈ normalizer (A : Set G)) (htL : t ∈ normalizer (L : Set G))
    (ρ : (L ⧸ pCore 2 L) →* Matrix ι ι F)
    (σ : F ≃+* F) (g : Matrix ι ι F) (hg : ∀ i, g i i ≠ 0)
    (hdiag : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d : ι → F, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d)
    (hint : ∀ x : L, (x : G) ∈ primeTorsion A p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) * g) :
    ∀ x : L, (x : G) ∈ primeTorsion A p →
      ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) =
        (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ := by
  intro x hx
  let y : L := ⟨t*x*t⁻¹,hL ((primeTorsion_normalizer A p htA x).mp hx)⟩
  obtain ⟨d,hd⟩ := hdiag x hx
  obtain ⟨e,he⟩ := hdiag y ((primeTorsion_normalizer A p htA x).mp hx)
  have he' : ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) =
      diagonal e := he
  have hi := hint x hx
  rw [hd,he',diagonal_map (map_zero σ)] at hi ⊢
  congr 1
  funext i
  apply mul_right_cancel₀ (hg i)
  have hii := congrArg (fun z : Matrix ι ι F => z i i) hi
  simp only [mul_diagonal,diagonal_mul] at hii
  exact hii.symm.trans (mul_comm _ _)

/-- The actual SL3 marking gives one common Frobenius power on the literal
odd Hall p-torsion, for the same original Sylow element normalizing it. -/
theorem source_primeTorsion_power_sl3
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (A : Subgroup G) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : primeTorsion A p ≤ cartanNormalizer T L)
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G)) :
    ∃ j : ℕ, ∀ x ∈ primeTorsion A p, (t : G)*x*(t : G)⁻¹ = x ^ (2 ^ j) := by
  obtain ⟨b,hb,hdiag⟩ := source_primeTorsion_alignment_sl3 m A p hp2 hQ
  let c : Coordinates D S.field := .sl3 m
  let e : (Fin 3 → S.field.Carrier) ≃+ (Fin 3 → S.field.Carrier) :=
    (alignedSylowOperator c b t).toAddEquiv
  obtain ⟨σ,hσ⟩ := source_aligned_semilinear_sl3 m b t
  obtain ⟨g,hgdet,hg,hcoeff⟩ := exists_semilinear_matrix e σ hσ
  have hf := source_aligned_flag_sl3 m b hb t
  have hgd := sl3_diagonal_nonzero e g hgdet hcoeff hf.1 hf.2
  let ρ : (L ⧸ pCore 2 L) →* Matrix (Fin 3) (Fin 3) S.field.Carrier :=
    SpecialLinearGroup.coeMonoidHom.comp
      ((MulAut.conj b).toMonoidHom.comp m.groupEquiv.toMonoidHom)
  have hρ : Function.Injective ρ := SpecialLinearGroup.coeMonoidHom_injective.comp
    ((MulAut.conj b).injective.comp m.groupEquiv.injective)
  have hL : primeTorsion A p ≤ L := hQ.trans inf_le_left
  have htL := D.sylow_normalizes_component t.property
  have hd : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d := hdiag
  have hint : ∀ x : L, (x : G) ∈ primeTorsion A p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) * g := by
    intro x _
    apply semilinear_matrix_intertwines e σ g hg
    exact alignedSylowOperator_intertwines c b t x
  obtain ⟨j,hj⟩ := primeTorsion_quotient_field_power A L p hL t htA htL ρ hρ σ hd
    (diagonal_field_action A L p hL t htA htL ρ σ g hgd hd hint)
  exact ⟨j,primeTorsion_power_of_quotient A L p (2 ^ j) hp2 hL t htA hj⟩

/-- The symplectic marking gives the same common field power on all
coordinates of the original Hall p-torsion, with its original index order. -/
theorem source_primeTorsion_power_sp4
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (A : Subgroup G) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : primeTorsion A p ≤ cartanNormalizer T L)
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G)) :
    ∃ j : ℕ, ∀ x ∈ primeTorsion A p, (t : G)*x*(t : G)⁻¹ = x ^ (2 ^ j) := by
  obtain ⟨b,hb,hdiag⟩ := source_primeTorsion_alignment_sp4 m A p hp2 hQ
  let c : Coordinates D S.field := .sp4 m
  let e : ((Fin 2 ⊕ Fin 2) → S.field.Carrier) ≃+ ((Fin 2 ⊕ Fin 2) → S.field.Carrier) :=
    (alignedSylowOperator c b t).toAddEquiv
  obtain ⟨σ,hσ⟩ := source_aligned_semilinear_sp4 m b t
  obtain ⟨g,hgdet,hg,hcoeff⟩ := exists_semilinear_matrix e σ hσ
  have hf := source_aligned_flag_sp4 m b hb t
  have hgd := sp4_diagonal_nonzero e g hgdet hcoeff hf
  let ρ : (L ⧸ pCore 2 L) →*
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) S.field.Carrier :=
    (Matrix.symplecticGroup (Fin 2) S.field.Carrier).subtype.comp
      ((MulAut.conj b).toMonoidHom.comp m.groupEquiv.toMonoidHom)
  have hρ : Function.Injective ρ := Subtype.val_injective.comp
    ((MulAut.conj b).injective.comp m.groupEquiv.injective)
  have hL : primeTorsion A p ≤ L := hQ.trans inf_le_left
  have htL := D.sylow_normalizes_component t.property
  have hd : ∀ x : L, (x : G) ∈ primeTorsion A p →
      ∃ d, ρ (QuotientGroup.mk' (pCore 2 L) x) = diagonal d := by
    intro x hx
    have hh := hdiag (mem_map_of_mem _ hx)
    obtain ⟨d,hd⟩ := hh
    refine ⟨Sum.elim ![(d.1 : S.field.Carrier),(d.2 : S.field.Carrier)]
      ![(↑d.1⁻¹ : S.field.Carrier),(↑d.2⁻¹ : S.field.Carrier)],?_⟩
    exact congrArg Subtype.val hd.symm
  have hint : ∀ x : L, (x : G) ∈ primeTorsion A p →
      g * (ρ (QuotientGroup.mk' (pCore 2 L) x)).map σ =
        ρ (quotientConjugation L t htL (QuotientGroup.mk' (pCore 2 L) x)) * g := by
    intro x _
    apply semilinear_matrix_intertwines e σ g hg
    exact alignedSylowOperator_intertwines c b t x
  obtain ⟨j,hj⟩ := primeTorsion_quotient_field_power A L p hL t htA htL ρ hρ σ hd
    (diagonal_field_action A L p hL t htA htL ρ σ g hgd hd hint)
  exact ⟨j,primeTorsion_power_of_quotient A L p (2 ^ j) hp2 hL t htA hj⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
