module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondRows
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorSecondProduct
public import Theory.Representation.CyclicSeedTensor.CubicSlices
public import Theory.SpecificGroups.SymmetricThree.PerfectImage
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The ordered product in the second quotient

Both constructed tensor rows give |V₀:U₀| = 64 or 512. For the supplied
conjugator g whose image modulo O₂(I₂) is cubic, the three marked slices
lift to the literal ordered product V_H V_H^g V_H^(g²). The same g, both
factor homomorphisms and quotient coordinates are retained. The original
source definition L₂,₊ = O²([L₂,T ∩ L]) supplies this cube condition:
a two-perfect image in S₃ lies in A₃. The residual application therefore
uses the original g in L₂,₊, with no added cube premise.

The original seed hypotheses allow any escaping element of I₂, including
an element with transposition image. A separate choice theorem constructs
a cubic representative in its left H-coset, preserving its first V_H
translate and the subgroup generated with H. Its original-input application
therefore needs no additional cube hypothesis. This representative is in
I₂; placement in a specified smaller source L₂,₊ is not asserted. In
particular the choice is explicit, rather than identifying an arbitrary
original g with a cubic. The extra-line movement in the maximal quotient,
critical intersections and chief obstruction remain assembly obligations.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Notation 13.2.1 and 13.8.29(4), printed pp.877 and 964. This supplies the ordered-product application,
not the full 13.8.28 contradiction.
-/

public noncomputable section
open Subgroup Representation
open scoped TensorProduct
open QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open scoped MatrixGroups IsMulCommutative
open CyclicSeedTensor
open SourceCompletion TransvectionRecognition.Component.ModelExtension BinaryPermutation
open BinaryLinear.OuterCyclic
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryParabolicExteriorSquare SingularPresentation
open PlaneSpan (pointSpace firstSpace planeSpace)
open BinaryLinear.FlagCoordinates
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {G K U W : Type*} [Group G] [Finite G] [Group K]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- A cubic choice can be made in the original escaping coset. The first
translate and generated overgroup are unchanged; the selected element is
explicit, so this does not assert that an arbitrary escaping element is cubic. -/
theorem source_second_cubic_choice
    (ds : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (A : Subgroup G) (hHeq : H = normalizer (V₁:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
    (cV : BinaryConjugationSection A V V₂
      ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom).comp
        (eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))))
    (hpoint : cV.imageSpace V₃ = Submodule.span (ZMod 2) {first})
    (g : A) (hg : (g:G) ∉ H)
    (ha : e (eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)) first = second) :
    ∃ g' : A, (g':G) ∉ H ∧ g' ^ 3 ∈ pCore 2 A ∧
      H ⊔ zpowers (g':G) = H ⊔ zpowers (g:G) ∧
      (Source.VH H V).conjBy ((g':G)⁻¹) = (Source.VH H V).conjBy ((g:G)⁻¹) ∧
      e (eI (QuotientGroup.mk' (pCore 2 A) g'⁻¹)) first = second := by
  let ι := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let μ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom
  obtain ⟨r,hr0,hr1⟩ := BinaryLinear.exists_linearEquiv_pair
    (first : Fin 2 → ZMod 2) second second (first + second)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr : r ^ 3 = 1 := by
    have h0 : (r ^ 3) first = first := by
      change r (r (r first)) = first
      rw [hr0,hr1,map_add,hr0,hr1]
      ext i
      fin_cases i <;> simp [first,second]
    have h1 : (r ^ 3) second = second := by
      change r (r (r second)) = second
      simp only [map_add,hr0,hr1]
      ext i
      fin_cases i <;> simp [first,second]
    apply LinearEquiv.ext
    intro v
    have hv : v = v 0 • first + v 1 • second := by
      ext i
      fin_cases i <;> simp [first,second]
    change (r ^ 3) v = v
    rw [hv,map_add,map_smul,map_smul,h0,h1]
  let a := e (ι g⁻¹)
  let i := e.symm (a⁻¹ * r)
  have hi : μ i first = first := by
    change e i first = first
    rw [show e i = a⁻¹ * r from e.apply_symm_apply _,LinearEquiv.mul_apply,hr0]
    rw [←ha]
    change a⁻¹ (a first) = first
    simp
  obtain ⟨b,hb,hbH⟩ := source_seed_stabilizer_lift ds H A hHeq hALT ι
    (eI.surjective.comp (QuotientGroup.mk'_surjective _)) μ cV hpoint i hi
  let g' := b⁻¹ * g
  have hg'r : e (ι g'⁻¹) = r := by
    simp only [g',mul_inv_rev,inv_inv,map_mul,hb]
    change a * e i = r
    rw [e.apply_symm_apply]
    simp
  have hg' : (g':G) ∉ H := by
    intro hh
    apply hg
    have hbg := H.mul_mem hbH hh
    simpa [g'] using hbg
  have hcube : g' ^ 3 ∈ pCore 2 A := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply eI.injective
    change ι (g' ^ 3) = ι 1
    apply e.injective
    simp only [map_one,map_pow]
    have heq : e (ι g') = r⁻¹ := by
      have heq' : (e (ι g'))⁻¹ = r := by simpa only [map_inv] using hg'r
      exact inv_eq_iff_eq_inv.mp heq'
    rw [heq,inv_pow,hr,inv_one]
  have hjoin : H ⊔ zpowers (g':G) = H ⊔ zpowers (g:G) := by
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [zpowers_le]
      exact (H ⊔ zpowers (g:G)).mul_mem
        ((le_sup_left : H ≤ H ⊔ zpowers (g:G)) (H.inv_mem hbH))
        ((le_sup_right : zpowers (g:G) ≤ H ⊔ zpowers (g:G)) (mem_zpowers _))
    · apply sup_le le_sup_left
      rw [zpowers_le]
      have hh := (H ⊔ zpowers (g':G)).mul_mem
        ((le_sup_left : H ≤ H ⊔ zpowers (g':G)) hbH)
        ((le_sup_right : zpowers (g':G) ≤ H ⊔ zpowers (g':G)) (mem_zpowers (g':G)))
      simpa [g'] using hh
  have hconj : (Source.VH H V).conjBy ((g':G)⁻¹) =
      (Source.VH H V).conjBy ((g:G)⁻¹) := by
    have hbN : (b:G) ∈ normalizer (Source.VH H V : Set G) :=
      le_normalizer_conjugateSpanBy V H hbH
    have hfix : (Source.VH H V).conjBy (b:G) = Source.VH H V :=
      (mem_normalizer_iff_map_conj_eq).mp hbN
    change (Source.VH H V).conjBy (((b:G)⁻¹ * (g:G))⁻¹) = _
    rw [mul_inv_rev,inv_inv,conjBy_mul,hfix]
  exact ⟨g',hg',hcube,hjoin,hconj,by change e (ι g'⁻¹) first = second; rw [hg'r,hr0]⟩

/-- Both full tensor rows give the exact quotient order and ordered product
for the supplied cubic representative, with no change of conjugator. -/
theorem source_second_product_from_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hQA : H.pCoreIn 2 ≤ A) (hnA : G2 V₂ ≤ normalizer A)
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H) (hgcube : g ^ 3 ∈ pCore 2 A)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    (U0 (Source.UH H V₃) V₂).relIndex (V0 (Source.VH H V) V₂) ∈ ({64,512} : Set ℕ) ∧
      ∀ x ∈ V0 (Source.VH H V) V₂,
        ∃ u ∈ Source.VH H V, ∃ v ∈ Source.VH H V, ∃ w ∈ Source.VH H V,
          x = u * ((g:G)⁻¹ * v * (g:G)) * ((g:G)⁻¹ ^ 2 * w * (g:G) ^ 2) := by
  obtain ⟨hn,he,e,τ,q,hseed,hq,⟨f,hf,hr,hrows⟩,hbound,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_tensor_rows_from_original_seed s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  let := hn
  let := he
  let c := eI (QuotientGroup.mk' (pCore 2 A) g⁻¹)
  let μ := TransitiveSeedCover.planeNatural e.toMonoidHom
  have hcube : c ^ 3 = 1 := by
    have hc : (QuotientGroup.mk' (pCore 2 A)) (g ^ 3) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hgcube
    calc
      c ^ 3 = (eI ((QuotientGroup.mk' (pCore 2 A)) (g ^ 3)))⁻¹ := by
        simp [c,map_inv,inv_pow]
      _ = 1 := by rw [hc,map_one,inv_one]
  have ha' : μ c first = second := ha
  have hb' : μ c second = first + second :=
    second_of_cube_eq_one (e c) (by rw [←map_pow,hcube,map_one]) ha
  have hUV := source_U0_le_VH_of_normal_factors H (Source.UH H V₃) V₂ V₃ V L2
    (T:Subgroup G) hK hG hV hgen s.seed_le
  have hgπ : π (inclusion hAG g)⁻¹ = (1,c) := hπI g⁻¹
  have hmem (u : Module.Dual (ZMod 2) U) : f u ∈ q.imageSpace (Source.VH H V) := by
    rw [←hr]
    exact ⟨u,rfl⟩
  have card_of_dim (n : ℕ)
      (hdimY : Module.finrank (ZMod 2) (Additive (V0 (Source.VH H V) V₂ ⧸
        (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))) = n) :
      (U0 (Source.UH H V₃) V₂).relIndex (V0 (Source.VH H V) V₂) = 2 ^ n := by
    change Nat.card (Additive (V0 (Source.VH H V) V₂ ⧸
      (U0 (Source.UH H V₃) V₂).subgroupOf (V0 (Source.VH H V) V₂))) = _
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hdimY]
  rcases hrows with ⟨E,hE⟩ | ⟨E,hE⟩
  · have hdimY := E.toLinearEquiv.finrank_eq.symm
    rw [Module.finrank_tensorProduct,Subspace.dual_finrank_eq,hdim] at hdimY
    have hc := card_of_dim 6 (by simpa using hdimY)
    refine ⟨by simp [hc],?_⟩
    intro x hx
    exact source_natural_second_tensor_product (Source.UH H V₃) V₂ (Source.VH H V)
      hUV π σ.dual μ τ q E c ha' (fun u => (hE u).symm ▸ hmem u)
      (inclusion hAG g) hgπ x hx
  · have hdimY := E.toLinearEquiv.finrank_eq.symm
    rw [Module.finrank_tensorProduct,Subspace.dual_finrank_eq,hdim,Module.finrank_prod] at hdimY
    have hc := card_of_dim 9 (by simpa using hdimY)
    refine ⟨by simp [hc],?_⟩
    intro x hx
    exact source_extra_line_second_tensor_product (Source.UH H V₃) V₂ (Source.VH H V)
      hUV π σ.dual μ τ q E c ha' hb' (fun u => (hE u).symm ▸ hmem u)
      (inclusion hAG g) hgπ x hx

/-- Original seed data permits a cubic representative in the same escaping
coset and gives the ordered three-factor product, without an added cube
hypothesis. Its first V_H translate and generated overgroup agree with the
original element. The separate same-element theorem applies whenever the
original representative is already cubic modulo the two-core. -/
theorem source_second_three_product_choice_from_original_seed
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hQA : H.pCoreIn 2 ≤ A) (hnA : G2 V₂ ≤ normalizer A)
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    (U0 (Source.UH H V₃) V₂).relIndex (V0 (Source.VH H V) V₂) ∈ ({64,512} : Set ℕ) ∧
      ∃ g' : A, (g':G) ∉ H ∧ g' ^ 3 ∈ pCore 2 A ∧
        H ⊔ zpowers (g':G) = H ⊔ zpowers (g:G) ∧
        (Source.VH H V).conjBy ((g':G)⁻¹) = (Source.VH H V).conjBy ((g:G)⁻¹) ∧
        ∀ x ∈ V0 (Source.VH H V) V₂,
          ∃ u ∈ Source.VH H V, ∃ v ∈ Source.VH H V, ∃ w ∈ Source.VH H V,
            x = u * ((g':G)⁻¹ * v * (g':G)) * ((g':G)⁻¹ ^ 2 * w * (g':G) ^ 2) := by
  obtain ⟨hn,he,e,τ,q,⟨cV,hcV⟩,hq,hrows,hbound,hd,hdis,hspan,hfix,ha,hmin⟩ :=
    source_second_tensor_rows_from_original_seed s hab h hH hcentral hHeq A L2 hK hG hV
      π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
      hgen hdim g hg ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate
  obtain ⟨g',hg',hcube,hjoin,hconj,ha'⟩ := source_second_cubic_choice
    (s.toLocalSetup hab) A hHeq hALT eI e cV hcV g hg ha
  obtain ⟨hindex,hprod⟩ := source_second_product_from_original_seed s hab h hH hcentral hHeq
    A L2 hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT
    hVA hAG hπI hgen hdim g' hg' hcube ρ d π₄ hker honto hnatural hpoint hplane eU
    hcoords hUcard hu (hjoin.symm ▸ hgenerate)
  exact ⟨hindex,g',hg',hcube,hjoin,hconj,hprod⟩

/-- The original two-residual actor has cubic image in the supplied I₂
quotient. No change to the element or quotient homomorphism is made. -/
theorem source_residual_actor_cube
    (A B P : Subgroup G) (hBA : B ≤ A)
    (hB : B = (pResidual 2 P).map P.subtype)
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (g : A) (hg : (g:G) ∈ B) : g ^ 3 ∈ pCore 2 A := by
  have hperfect : IsPPerfect 2 B := by
    rw [hB]
    exact isPPerfect_embedded_pResidual 2 P
  let f := (eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))).comp (inclusion hBA)
  have hc := Equiv.Perm.cube_eq_one_of_isPPerfect hperfect f (⟨g,hg⟩ : B)
  change eI (QuotientGroup.mk' (pCore 2 A) g) ^ 3 = 1 at hc
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pCore 2 A) (g ^ 3) = 1
  apply eI.injective
  simpa only [map_pow,map_one] using hc

/-- The source definition of L₂,₊ as an embedded two-residual discharges the
cube condition in the same-g ordered-product theorem. The literal residual,
its placement in I₂, and the original g ∈ L₂,₊ are retained as source inputs. -/
theorem source_second_product_from_original_residual
    (s : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hab : IsMulCommutative (conjugateSpanBy V G₁))
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃:Set G) ≤ M ⊓ normalizer (V:Set G))
    (hHeq : H = normalizer (V₁:Set G))
    (A L2 : Subgroup G)
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) (Source.UH H V₃) V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hQA : H.pCoreIn 2 ≤ A) (hnA : G2 V₂ ≤ normalizer A)
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (hgen : Source.UH H V₃ = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (P : Subgroup G) (hL2def : L2 = (pResidual 2 P).map P.subtype)
    (hL2A : L2 ≤ A) (hgL2 : (g:G) ∈ L2)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H (Source.UH H V₃) V₁ ρ)
    (π₄ : H →* SL(4,ZMod 2))
    (hker : π₄.ker = (Source.QH H).subgroupOf H)
    (honto : Function.Surjective π₄)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π₄ h).val w)
    (hpoint : d.imageSpace V₂ = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hplane : d.imageSpace V₃ = plane)
    (eU : QuotientSpace (Pi.single 0 1 : Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (hcoords : ∀ u : Source.UH H V₃, (dU.coordinates u).toAdd =
      eU ((line (Pi.single 0 1)).mkQ (d.coordinates u).toAdd))
    (hUcard : Nat.card (Source.UH H V₃) = 32)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    (U0 (Source.UH H V₃) V₂).relIndex (V0 (Source.VH H V) V₂) ∈ ({64,512} : Set ℕ) ∧
      ∀ x ∈ V0 (Source.VH H V) V₂,
        ∃ u ∈ Source.VH H V, ∃ v ∈ Source.VH H V, ∃ w ∈ Source.VH H V,
          x = u * ((g:G)⁻¹ * v * (g:G)) * ((g:G)⁻¹ ^ 2 * w * (g:G) ^ 2) := by
  exact source_second_product_from_original_seed s hab h hH hcentral hHeq A L2 hK hG hV
    π hπ hπker hcore σ κ dU hκker hκ hπK eI hAcore hQA hnA hALT hVA hAG hπI
    hgen hdim g hg (source_residual_actor_cube A L2 P hL2A hL2def eI g hgL2)
    ρ d π₄ hker honto hnatural hpoint hplane eU hcoords hUcard hu hgenerate

end CFSG.Quasithin.Chapter13.Section08.LinearFour
