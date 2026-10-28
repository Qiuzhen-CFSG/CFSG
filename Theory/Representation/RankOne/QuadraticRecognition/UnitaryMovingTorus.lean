module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallCentralizer
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryTorus

/-!
# The moving unitary torus on the local central quotient

The norm-one torus commutes with the literal fixed-field SL₂ block. If an
individual actor element has fixed codimension below twice the field degree,
the local central quotient has dimension below four times that degree.
The odd-centralizer dichotomy makes a torus element either trivial or
fixed-free on this quotient. Triviality would fix the ambient actor
displacements, so root/block generation and the three-conjugate degree bound
exclude it for elements with nontrivial projective image.

Cubic scalar elements in SU₃ are handled separately. The actor normally
generates the whole group. A central odd element fixing all its displacements
must act trivially on the original vectors, contradicting faithfulness.
Thus the full special torus is covered, including q=8, while the projective
version tests nontriviality after the scalar quotient.

All fixed-free assertions are stated on original representatives modulo the
actual block-fixed denominator, within the fixed-generated local submodule.
They are the moving-torus reduction in DGS85, Groups and Graphs, (5.10)(b),
pp.111–112. The subsequent numerical contradiction remains separate.
CriticalMovingTorus gives the literal Z/(Z∩Z(L)) applications.
-/

public noncomputable section
open Matrix Subgroup Representation.BinaryOffender
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus.EvenCenterAction HermitianForm.EvenInner
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])

/-- The original norm-one torus commutes with the entire fixed-field block,
including the cubic scalar elements of the special cover. -/
theorem su3_normOne_commutes_block (k : normOne J) (g : SL(2,fixedField J)) :
    hermitianTorusSU J hJ k.val * block J hJ g =
      block J hJ g * hermitianTorusSU J hJ k.val := by
  apply Subtype.ext
  apply Units.ext
  change hermitianTorusMatrix J k.val * (block J hJ g).val.val =
    (block J hJ g).val.val * hermitianTorusMatrix J k.val
  rw [block_val]
  rw [hermitianTorusMatrix_eq,k.property,inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_three,mul_comm]

/-- Projectivization preserves the literal block and torus commutation. -/
theorem psu3_normOne_commutes_block (k : normOne J) (g : SL(2,fixedField J)) :
    normOneMap J hJ k * (J.specialToProjective.comp (block J hJ)) g =
      (J.specialToProjective.comp (block J hJ)) g * normOneMap J hJ k := by
  have he := congrArg J.specialToProjective (su3_normOne_commutes_block J hJ k g)
  have ht : J.specialToProjective (hermitianTorusSU J hJ k.val)=normOneMap J hJ k := by
    apply Subtype.ext
    rw [J.specialToProjective_apply_val]
    exact (hermitianTorusPSU_val J hJ k.val).symm
  simpa only [map_mul,MonoidHom.comp_apply,ht] using he

private theorem embedded_odd_dichotomy
    {K D V : Type*} [Field K] [Finite K] [CharP K 2] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (j : SL(2,K) →* D)
    {n : ℕ} (hn : 2≤n) (hK : Nat.card K=2^n)
    (A : Subgroup D) (hAr : A≤j.range) (hq : IsQuadratic ρ A)
    (t : D) (ht : t∈A) (ht1 : t≠1)
    (hd : let W := fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤)<4*n)
    (k : D) (hc : ∀ g, k*j g=j g*k) {m : ℕ} (hm : Odd m) (hkp : k^m=1) :
    (∀ a∈A, ∀ v, ρ k (ρ a v-v)=ρ a v-v) ∨
    (∀ v∈(fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)).toSubmodule,
      ρ k v-v∈fixedSpace (ρ.comp j) ⊤ → v∈fixedSpace (ρ.comp j) ⊤) := by
  have hlarge : 3<Nat.card K := by
    rw [hK]
    have hh := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hn
    norm_num at hh
    omega
  let : Group.IsPerfect SL(2,K) := SL2SylowFixedRecognition.perfect (by omega)
  let : IsSimpleGroup PSL(2,K) := ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup SL(2,K) := (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL K).isSimpleGroup
  let B := A.comap j
  have hcl : normalClosure (B : Set SL(2,K))=⊤ := by
    apply normalClosure_normal.eq_bot_or_eq_top.resolve_left
    intro hb
    obtain ⟨t₀,ht₀⟩ := hAr ht
    have hh : t₀∈normalClosure (B : Set SL(2,K)) := subset_normalClosure (show j t₀∈A from ht₀.symm ▸ ht)
    rw [hb,mem_bot] at hh
    exact ht1 (ht₀.symm.trans (hh ▸ j.map_one))
  have hqB : IsQuadratic (ρ.comp j) B := fun a ha b hb v => hq (j a) ha (j b) hb v
  have hTc (g : SL(2,K)) (v : V) :
      ρ k ((ρ.comp j) g v)=(ρ.comp j) g (ρ k v) := by
    change ρ k (ρ (j g) v)=ρ (j g) (ρ k v)
    rw [←Module.End.mul_apply,←map_mul,hc,map_mul,Module.End.mul_apply]
  have hTp : (ρ k)^m=1 := by rw [←map_pow,hkp,map_one]
  rcases sl2_fixedGenerated_odd_centralizer_dichotomy (ρ.comp j) B hqB hcl
      (by omega) hK hd (ρ k) hTc hm hTp with ht|hf
  · left
    intro a ha v
    obtain ⟨a₀,rfl⟩ := hAr ha
    exact ht a₀ v
  · exact Or.inr hf

omit [CharP F 2] in
private theorem normOne_power [Finite F] {n : ℕ} (hn : 0<n)
    (hcard : Nat.card F=(2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n))
    (k : normOne J) : Odd (2^n+1) ∧ k^(2^n+1)=1 := by
  refine ⟨(even_two.pow_of_ne_zero (by omega : n≠0)).add_odd odd_one,?_⟩
  rw [←normOne_card J hcard hconj]
  exact pow_card_eq_one'

variable [Finite F] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- In the contrary small-index case of DGS (5.10)(b), every noncentral
norm-one torus element is fixed-free on the actual local central quotient. -/
theorem su3_small_element_torus_fixed_free
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hnt : ∃ g, ρ g≠1)
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hAc : 4≤Nat.card A)
    (hq : IsQuadratic ρ A) (hgen : GeneratedByFixedSpace ρ A)
    (t : J.specialSubgroup) (ht : t∈A) (ht1 : t≠1)
    (hsmall : fixedCodim ρ (zpowers t)<2*n)
    (k : normOne J) (hk : k^3≠1) :
    ∀ v∈(fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))).toSubmodule,
      ρ (hermitianTorusSU J hJ k.val) v-v∈fixedSpace (ρ.comp (block J hJ)) ⊤ →
      v∈fixedSpace (ρ.comp (block J hJ)) ⊤ := by
  have hF : Nat.card (fixedField J)=2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  have hd := (su3_root_fixedGenerated_reduction J hJ (by omega) hcard hconj
    ρ A hA hAc hq t ht ht1).2
  have hd' : let W := fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤)<4*n := by
    dsimp only at hd ⊢
    omega
  obtain ⟨ho,hpow⟩ := normOne_power J (by omega) hcard hconj k
  have hp : (hermitianTorusSU J hJ k.val)^(2^n+1)=1 := by
    exact (map_pow ((hermitianTorusSU J hJ).comp (normOne J).subtype) k _).symm.trans
      (by rw [hpow,map_one])
  rcases embedded_odd_dichotomy ρ (block J hJ) hn hF A
      (hA.trans (su3_central_le_block J hJ)) hq t ht ht1 hd'
      (hermitianTorusSU J hJ k.val) (su3_normOne_commutes_block J hJ k) ho hp with hf|hf
  · have he := su3_fixedGenerated_eq_top_of_torus_centralizes_displacements J hJ hn hcard hconj
      ρ A hA hgen k hk hf
    have heq := (su3_root_fixedGenerated_reduction J hJ (by omega) hcard hconj
      ρ A hA hAc hq t ht ht1).1
    rw [he,top_inf_eq] at heq
    have hl := su3_root_actor_fixedCodim_lower J hJ hn hcard hconj ρ hnt A hA hAc
    unfold fixedCodim at hl hsmall
    rw [heq] at hsmall
    omega
  · exact hf

/-- In the contrary small-index case of DGS (5.10)(b), every nonidentity
projective norm-one torus element is fixed-free on the actual local central quotient. -/
theorem psu3_small_element_torus_fixed_free
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V) (hnt : ∃ g, ρ g≠1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hA : A≤centralImage J hJ) (hAc : 4≤Nat.card A)
    (hq : IsQuadratic ρ A) (hgen : GeneratedByFixedSpace ρ A)
    (t : (ProjectiveSpecialUnitaryMatrixGroup J)) (ht : t∈A) (ht1 : t≠1)
    (hsmall : fixedCodim ρ (zpowers t)<2*n)
    (k : normOne J) (hk : normOneMap J hJ k≠1) :
    ∀ v∈(fixedGeneratedSubrepresentation (ρ.comp (J.specialToProjective.comp (block J hJ))) (A.comap (J.specialToProjective.comp (block J hJ)))).toSubmodule,
      ρ (normOneMap J hJ k) v-v∈fixedSpace (ρ.comp (J.specialToProjective.comp (block J hJ))) ⊤ →
      v∈fixedSpace (ρ.comp (J.specialToProjective.comp (block J hJ))) ⊤ := by
  have hF : Nat.card (fixedField J)=2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  have hd := (psu3_root_fixedGenerated_reduction J hJ (by omega) hcard hconj
    ρ A hA hAc hq t ht ht1).2
  have hd' : let W := fixedGeneratedSubrepresentation (ρ.comp (J.specialToProjective.comp (block J hJ))) (A.comap (J.specialToProjective.comp (block J hJ)))
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤)<4*n := by
    dsimp only at hd ⊢
    omega
  obtain ⟨ho,hpow⟩ := normOne_power J (by omega) hcard hconj k
  have hp : (normOneMap J hJ k)^(2^n+1)=1 := by
    rw [←map_pow,hpow,map_one]
  rcases embedded_odd_dichotomy ρ (J.specialToProjective.comp (block J hJ)) hn hF A
      (hA.trans (psu3_central_le_block J hJ)) hq t ht ht1 hd'
      (normOneMap J hJ k) (psu3_normOne_commutes_block J hJ k) ho hp with hf|hf
  · have he := psu3_fixedGenerated_eq_top_of_torus_centralizes_displacements J hJ hn hcard hconj
      ρ A hA hgen k hk hf
    have heq := (psu3_root_fixedGenerated_reduction J hJ (by omega) hcard hconj
      ρ A hA hAc hq t ht ht1).1
    rw [he,top_inf_eq] at heq
    have hl := psu3_root_actor_fixedCodim_lower J hJ hn hcard hconj ρ hnt A hA hAc
    unfold fixedCodim at hl hsmall
    rw [heq] at hsmall
    omega
  · exact hf

/-- Faithfulness handles the cubic scalar elements as well: the entire
nonidentity special norm-one torus is fixed-free on the same central
quotient in the contrary small-index case. -/
theorem su3_small_element_full_torus_fixed_free
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hf : Function.Injective ρ)
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hAc : 4≤Nat.card A)
    (hq : IsQuadratic ρ A) (hgen : GeneratedByFixedSpace ρ A)
    (t : J.specialSubgroup) (ht : t∈A) (ht1 : t≠1)
    (hsmall : fixedCodim ρ (zpowers t)<2*n)
    (k : normOne J) (hk : hermitianTorusSU J hJ k.val≠1) :
    ∀ v∈(fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))).toSubmodule,
      ρ (hermitianTorusSU J hJ k.val) v-v∈fixedSpace (ρ.comp (block J hJ)) ⊤ →
      v∈fixedSpace (ρ.comp (block J hJ)) ⊤ := by
  by_cases hcub : k^3=1
  · have hF : Nat.card (fixedField J)=2^n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
    have hd := (su3_root_fixedGenerated_reduction J hJ (by omega) hcard hconj
      ρ A hA hAc hq t ht ht1).2
    have hd' : let W := fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))
        Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤)<4*n := by
      dsimp only at hd ⊢
      omega
    obtain ⟨ho,hpow⟩ := normOne_power J (by omega) hcard hconj k
    have hp : (hermitianTorusSU J hJ k.val)^(2^n+1)=1 := by
      exact (map_pow ((hermitianTorusSU J hJ).comp (normOne J).subtype) k _).symm.trans
        (by rw [hpow,map_one])
    rcases embedded_odd_dichotomy ρ (block J hJ) hn hF A
        (hA.trans (su3_central_le_block J hJ)) hq t ht ht1 hd'
        (hermitianTorusSU J hJ k.val) (su3_normOne_commutes_block J hJ k) ho hp with hm|hm
    · have hc : hermitianTorusSU J hJ k.val∈center J.specialSubgroup := by
        apply J.specialToProjective_ker_le_center
        have he : J.specialToProjective (hermitianTorusSU J hJ k.val)=normOneMap J hJ k := by
          apply Subtype.ext
          rw [J.specialToProjective_apply_val]
          exact (hermitianTorusPSU_val J hJ k.val).symm
        exact he.trans ((normOneMap_eq_one_iff J hJ k).mpr hcub)
      have hcl : normalClosure (A : Set J.specialSubgroup)=⊤ := by
        obtain ⟨g,h,he⟩ := su3_root_three_conjugates J hJ hn hcard hconj A hA hAc
        have hn (g : J.specialSubgroup) : A.map (MulAut.conj g).toMonoidHom≤
            normalClosure (A : Set J.specialSubgroup) := by
          rintro _ ⟨a,ha,rfl⟩
          exact normalClosure_normal.conj_mem a (subset_normalClosure ha) g
        apply top_unique
        rw [←he]
        exact sup_le (sup_le subset_normalClosure (hn g)) (hn h)
      have he := odd_central_trivial_of_fixes_displacements ρ A hcl
        (hermitianTorusSU J hJ k.val) hc ho hp hm
      exact (hk (hf (he.trans ρ.map_one.symm))).elim
    · exact hm
  · exact su3_small_element_torus_fixed_free J hJ hn hcard hconj ρ
      ⟨t,fun he => ht1 (hf (he.trans ρ.map_one.symm))⟩ A hA hAc hq hgen t ht ht1 hsmall k hcub

end Representation.RankOne.QuadraticRecognition
