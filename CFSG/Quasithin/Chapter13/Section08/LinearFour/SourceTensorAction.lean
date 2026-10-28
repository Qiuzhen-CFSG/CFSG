module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorMarking
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.ActionKernel

/-!
# The whole first-tensor action from the original normal factors

Normality of the actual K₂ and G₂ = ⟨K₂,L₂,₊,T⟩ put U₀ inside
⟨V^{K₂}⟩, hence inside the already elementary V_H. This proves the
needed elementary quotient before any tensor decomposition is used.
The natural action on U_H/V₂ has kernel O₂(N_H(V₂)). Since O₂(G₂)
lies in H, it centralizes this section. A normalized commutator preimage
extends that bound to every generating conjugate, giving [O₂(G₂),U₀] ≤ V₂.
The actual conjugation action therefore descends through the marked
G₂/O₂(G₂), with the literal U₀ → U₀/V₂ coordinate map.

The source application obtains normality, generation, the K₂ seed span
and core containment from the existing natural marking, I₂ supplement
and common Sylow subgroup. The resulting whole action shares that
natural point-quotient marking and retains the original I₂ quotient map.

The smaller V/V₂ section and a moved seed line also prove V ≤ U₀.
Together with the existing compatible-embedding construction this gives
tensor coordinates, the specified two-conjugate product and intersection,
and |U₀:V| = 16. The literal V_H intersection application no longer
assumes an action or tensor embedding on U₀/V₂.

The covered-case natural V/V₂ section, compatible exterior and second-tensor
markings, extra-line movement and chief obstruction remain to be proved by
qt-d-138-linear-four-source. These conditional source applications do not
complete 13.8.28. Earlier 13.8.27 retains qt-d-138-six-g2-source, and final
13.8.1 assembly retains qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(2--3), printed p.964, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G]

/-- Normal factors put U₀ in the elementary H-span before the tensor is known. -/
theorem source_U0_le_VH_of_normal_factors
    (H UH V2 V3 V L2 T : Subgroup G)
    (hK : ((K2 H V2).subgroupOf (G2 V2)).Normal)
    (hG : G2 V2 = K2 H V2 ⊔ L2 ⊔ T)
    (hV : L2 ⊔ T ≤ normalizer (V:Set G))
    (hgen : UH = conjugateSpanBy V3 (K2 H V2)) (h3V : V3 ≤ V) :
    U0 UH V2 ≤ Source.VH H V := by
  have hKG := (K2_le_localNormalizer H V2).trans inf_le_right
  have hKn : G2 V2 ≤ normalizer (K2 H V2 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKG).mp hK
  have hL2 : L2 ≤ G2 V2 := by
    rw [hG]
    exact le_sup_right.trans le_sup_left
  have hT : T ≤ G2 V2 := by
    rw [hG]
    exact le_sup_right
  have hn : G2 V2 ≤ normalizer (conjugateSpanBy V (K2 H V2) : Set G) := by
    rw [hG]
    exact sup_le (sup_le (le_normalizer_conjugateSpanBy _ _)
      (normalizes_conjugateSpanBy V (K2 H V2) L2
        (le_sup_left.trans hV) (hL2.trans hKn)))
      (normalizes_conjugateSpanBy V (K2 H V2) T
        (le_sup_right.trans hV) (hT.trans hKn))
  exact (conjugateSpanBy_le (hgen ▸ conjugateSpanBy_mono h3V le_rfl) hn).trans
    (conjugateSpanBy_mono le_rfl ((K2_le_localNormalizer H V2).trans inf_le_left))

/-- The natural point-quotient kernel centralizes the whole G₂-span modulo V₂. -/
theorem source_U0_core_commutator
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (H UH V2 : Subgroup G) (κ : ↥(H ⊓ G2 V2) →* K)
    (σ : Representation (ZMod 2) K W)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2
      (σ.comp κ))
    (hκ : κ.ker = pCore 2 ↥(H ⊓ G2 V2)) (hcore : Q2 V2 ≤ H) :
    ⁅Q2 V2,U0 UH V2⁆ ≤ V2 := by
  have hQN : G2 V2 ≤ normalizer (Q2 V2 : Set G) := by
    exact (G2 V2).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (G2 V2)))
  have hQP : Q2 V2 ≤ H ⊓ G2 V2 := le_inf hcore (Q2_le_G2 V2)
  have hQc : Q2 V2 ≤ (H ⊓ G2 V2).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (G2 V2)) hQP
      (inf_le_right.trans hQN)
  have hc : ⁅Q2 V2,UH⁆ ≤ V2 := by
    apply commutator_le.mpr
    intro a ha u hu
    let aP : ↥(H ⊓ G2 V2) := ⟨a,hQP ha⟩
    have haP : aP ∈ pCore 2 ↥(H ⊓ G2 V2) := by
      obtain ⟨b,hb,he⟩ := hQc ha
      have he' : b = aP := Subtype.ext he
      exact he' ▸ hb
    have he : κ aP = 1 := by
      change aP ∈ κ.ker
      rwa [hκ]
    exact (dU.action_mem_ker_iff aP).mp (by
      change σ (κ aP) = 1
      rw [he,map_one]) u hu
  let C := commutatorPreimage (G2 V2) (Q2 V2) V2
  have hUC : UH ≤ C := le_commutatorPreimage (dU.section_le.trans inf_le_right)
    (by rwa [commutator_comm])
  have hGC : G2 V2 ≤ normalizer C := commutatorPreimage_normalized
    (G2 V2) (Q2 V2) V2 (G2 V2) le_rfl (G2 V2).le_normalizer hQN le_rfl
  rw [commutator_comm]
  exact (commutator_mono (conjugateSpanBy_le hUC hGC) le_rfl).trans
    (commutator_commutatorPreimage_le (G2 V2) (Q2 V2) V2 le_rfl)

/-- Construct the action through the original quotient, with canonical coordinates. -/
theorem source_U0_quotient_action
    {K D W : Type*} [Group K] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (H UH V2 : Subgroup G) [IsElementaryAbelian 2 (U0 UH V2)]
    (κ : ↥(H ⊓ G2 V2) →* K) (σ : Representation (ZMod 2) K W)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hκ : κ.ker = pCore 2 ↥(H ⊓ G2 V2)) (hcore : Q2 V2 ≤ H)
    (π : G2 V2 →* D) (hπ : Function.Surjective π) (hπker : π.ker = pCore 2 (G2 V2)) :
    ∃ (ρ : Representation (ZMod 2) D (Additive (U0 UH V2 ⧸ V2.subgroupOf (U0 UH V2))))
      (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π)),
      ∀ u : U0 UH V2, (d.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (V2.subgroupOf (U0 UH V2)) u) := by
  apply BinaryConjugationSection.exists_descended_actor (G2 V2) (U0 UH V2) V2
    (conjugateSpanBy_le_self (dU.section_le.trans inf_le_right))
    (dU.kernel_le.trans (UH_le_U0 UH V2)) (G2_normalizes_U0 UH V2) le_rfl π hπ
  intro a ha u hu
  have haQ : (a:G) ∈ Q2 V2 := by
    apply mem_map_of_mem (G2 V2).subtype
    rwa [←hπker]
  exact source_U0_core_commutator H UH V2 κ σ dU hκ hcore
    (commutator_mem_commutator haQ hu)



open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct

/-- One moved seed line fills the actual two-dimensional V/V₂, so V lies
in U₀ before the tensor coordinates are constructed. -/
theorem source_seed_plane_le_U0
    {I : Type*} [Group I] (UH V2 V3 V A : Subgroup G)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (ι : A →* I) (hι : Function.Surjective ι)
    (dV : BinaryConjugationSection A V V2 (μ.comp ι))
    (hAG : A ≤ G2 V2) (h2U : V2 ≤ UH) (h3U : V3 ≤ UH)
    (hpoint : dV.imageSpace V3 = Submodule.span (ZMod 2) {first})
    (a : I) (ha : μ a first = second) : V ≤ U0 UH V2 := by
  have hfirst : first ∈ dV.imageSpace (U0 UH V2) := by
    apply dV.imageSpace_mono (h3U.trans (UH_le_U0 UH V2))
    rw [hpoint]
    exact Submodule.subset_span (Set.mem_singleton first)
  have hsecond : second ∈ dV.imageSpace (U0 UH V2) := by
    obtain ⟨a',ha'⟩ := hι a
    have hh := dV.imageSpace_apply_mem (U0 UH V2) a'
      (G2_normalizes_U0 UH V2 (hAG a'.property)) first hfirst
    change μ (ι a') first ∈ _ at hh
    rwa [ha',ha] at hh
  have htop : dV.imageSpace (U0 UH V2) = ⊤ := by
    apply top_unique
    intro w _
    have he : w = w 0 • first + w 1 • second := by
      ext i
      fin_cases i <;> simp [first,second]
    rw [he]
    exact (dV.imageSpace (U0 UH V2)).add_mem
      (Submodule.smul_mem _ _ hfirst) (Submodule.smul_mem _ _ hsecond)
  exact (dV.le_sup_kernel_of_image_top _ htop).trans
    (sup_le le_rfl (h2U.trans (UH_le_U0 UH V2)))

/-- The original normal factors construct the whole section action and hence
its tensor coordinates; only the two smaller natural sections are supplied. -/
theorem source_tensor_from_local_sections
    {K I U : Type*} [Finite G] [Group K] [Group I]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (H UH V2 V3 V A L2 T : Subgroup G) [IsElementaryAbelian 2 (Source.VH H V)]
    (hK : ((K2 H V2).subgroupOf (G2 V2)).Normal)
    (hG : G2 V2 = K2 H V2 ⊔ L2 ⊔ T)
    (hV : L2 ⊔ T ≤ normalizer (V:Set G)) (h3V : V3 ≤ V)
    (π : G2 V2 →* K × I) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V2)) (hcore : Q2 V2 ≤ H)
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (κ : ↥(H ⊓ G2 V2) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V2))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V2))))
    (hπK : ∀ k : K2 H V2,
      π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V2) k),1))
    (ι : A →* I) (hι : Function.Surjective ι)
    (dV : BinaryConjugationSection A V V2 (μ.comp ι))
    (hAG : A ≤ G2 V2) (hπI : ∀ a : A, π (inclusion hAG a) = (1,ι a))
    (h3U : V3 ≤ UH)
    (hgen : UH = conjugateSpanBy V3 (K2 H V2)) (hindex : V2.relIndex V3 = 2)
    (hpoint : dV.imageSpace V3 = Submodule.span (ZMod 2) {first})
    (hdim : Module.finrank (ZMod 2) U = 3)
    (a b : I) (ha : μ a first = second)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) :
    ∃ (hVS : V ≤ U0 UH V2) (u₀ : U)
      (dt : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 ((externalTensor σ μ).comp π)),
      u₀ ≠ 0 ∧
      (∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd =
        (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first) ∧
      (∀ v : V, (dt.coordinates (inclusion hVS v)).toAdd =
        u₀ ⊗ₜ[ZMod 2] (dV.coordinates v).toAdd) ∧
      U0 UH V2 = UH ⊔ UH.conjBy ((g:G)⁻¹) ∧
      UH ⊓ UH.conjBy ((g:G)⁻¹) = V2 ∧ V.relIndex (U0 UH V2) = 16 := by
  have hVS := source_seed_plane_le_U0 UH V2 V3 V A μ ι hι dV hAG dU.kernel_le h3U hpoint a ha
  let : IsElementaryAbelian 2 (U0 UH V2) := IsElementaryAbelian.of_le
    (source_U0_le_VH_of_normal_factors H UH V2 V3 V L2 T hK hG hV hgen h3V)
  obtain ⟨ρ,d,_⟩ := source_U0_quotient_action H UH V2 κ σ dU hκker hcore π hπ hπker
  obtain ⟨u₀,E,hu,hEU,hEV,hprod,hint,hcard⟩ :=
    source_tensor_from_sections H UH V2 V3 V A π ρ σ μ d κ dU hκ hπK
      ι hι dV hAG hπI hVS h3U hgen hindex hpoint hdim a b ha hb0 hb1 g hg
  refine ⟨hVS,u₀,d.relabel π E.symm,hu,?_,?_,hprod,hint,hcard⟩
  · intro u
    change E.toLinearEquiv.symm ((d.coordinates (inclusion (UH_le_U0 UH V2) u)).toAdd) = _
    exact E.toLinearEquiv.symm_apply_eq.mpr (hEU u).symm
  · intro v
    change E.toLinearEquiv.symm ((d.coordinates (inclusion hVS v)).toAdd) = _
    exact E.toLinearEquiv.symm_apply_eq.mpr (hEV v).symm



open BinaryLinear.OuterCyclic
/-- The original natural marking and I₂ supplement discharge the normal-factor,
seed-generation and core hypotheses used to construct the whole action. -/
theorem source_U0_geometry_of_natural_section [Finite G]
    (H UH V1 V2 V3 V L2 : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h23 : V2 ≤ V3) (h3U : V3 ≤ UH) (h3V : V3 ≤ V)
    (hindex : V2.relIndex V3 = 2) (hV1 : Nat.card V1 = 2)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (hTH : (T:Subgroup G) ≤ H) (hT2 : (T:Subgroup G) ≤ G2 V2)
    (hH : H = normalizer (V1:Set G)) (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hI : I.map (G2 V2).subtype = H.pCoreIn 2 ⊔ L2)
    (ht : ∀ a b : V2, a ≠ 1 → b ≠ 1 →
      ∃ i : I, ((i : G2 V2) : G) * (a:G) * ((i : G2 V2) : G)⁻¹ = b) :
    ((K2 H V2).subgroupOf (G2 V2)).Normal ∧
      G2 V2 = K2 H V2 ⊔ L2 ⊔ (T:Subgroup G) ∧
      UH = conjugateSpanBy V3 (K2 H V2) ∧ Q2 V2 ≤ H ∧
      U0 UH V2 ≤ Source.VH H V ∧ ⁅Q2 V2,U0 UH V2⁆ ≤ V2 ∧
      IsElementaryAbelian 2 (U0 UH V2) := by
  have hcore : Q2 V2 ≤ H := by
    have hh := pCoreIn_le_sylow (G2 V2) (T.subtype hT2)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT2] at hh
    exact hh.trans hTH
  have hIP := source_I2_point_supplement H V1 V2 hH h12 hV1 I ht
  have hK := source_K2_normal_of_symmetric_supplement H UH V1 V2 ρ d φ hφ
    hnatural hker h12 (h23.trans h3U) v hv hpoint I eI hIP hcore
  have hG := source_normalizer_generated_factors H V2 L2 T hTH hT2 I hIP hI
  have hproper : ¬ V3 ≤ V2 := by
    intro hh
    have hi := relIndex_eq_one.mpr hh
    omega
  have hgen := source_K2_seed_span H UH V1 V2 V3 ρ d φ hφ hnatural hker
    h12 h23 h3U hproper v hv hpoint
  have hUV := source_U0_le_VH_of_normal_factors H UH V2 V3 V L2 T hK hG hV hgen h3V
  obtain ⟨κ,dU,_,_,hκ,_,_,_⟩ := source_point_quotient_marking H UH V1 V2 ρ d φ hφ
    hnatural hker h12 (h23.trans h3U) v hv hpoint
  exact ⟨hK,hG,hgen,hcore,hUV,
    source_U0_core_commutator H UH V2 κ _ dU hκ hcore,IsElementaryAbelian.of_le hUV⟩

/-- The same-conjugator intersection now uses the constructed whole action;
no action, tensor embedding or cyclic-vector premise on U₀/V₂ is supplied. -/
theorem source_tensor_intersection_from_local_sections
    {K I U : Type*} [Finite G] [Group K] [Group I]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (H UH V2 V3 V A L2 T : Subgroup G) [IsElementaryAbelian 2 (Source.VH H V)]
    (hK : ((K2 H V2).subgroupOf (G2 V2)).Normal)
    (hG : G2 V2 = K2 H V2 ⊔ L2 ⊔ T)
    (hV : L2 ⊔ T ≤ normalizer (V:Set G)) (h3V : V3 ≤ V)
    (π : G2 V2 →* K × I) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V2)) (hcore : Q2 V2 ≤ H)
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (κ : ↥(H ⊓ G2 V2) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2 (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V2))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V2))))
    (hπK : ∀ k : K2 H V2,
      π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V2) k),1))
    (ι : A →* I) (hι : Function.Surjective ι)
    (dV : BinaryConjugationSection A V V2 (μ.comp ι))
    (hAG : A ≤ G2 V2) (hπI : ∀ a : A, π (inclusion hAG a) = (1,ι a))
    (h3U : V3 ≤ UH)
    (hgen : UH = conjugateSpanBy V3 (K2 H V2)) (hindex : V2.relIndex V3 = 2)
    (hpoint : dV.imageSpace V3 = Submodule.span (ZMod 2) {first})
    (hdim : Module.finrank (ZMod 2) U = 3)
    (a b : I) (ha : μ a first = second)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (g : G2 V2) (hg : π g⁻¹ = (1,a))
    (L T₀ M : Subgroup G) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hact : ∀ h x, ξ h x = Atlas.Order20160A8.Bivectors.exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V2,
        (π₄ (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T₀ ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgenerate : L ⊔ T₀ ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  obtain ⟨_,_,_,_,_,_,hprod,_,_⟩ := source_tensor_from_local_sections
    H UH V2 V3 V A L2 T hK hG hV h3V π hπ hπker hcore σ μ κ dU hκker
      hκ hπK ι hι dV hAG hπI h3U hgen hindex hpoint hdim a b ha hb0 hb1 g hg
  have hk : π.ker ≤ H.subgroupOf (G2 V2) := by
    rw [hπker]
    intro x hx
    exact hcore (mem_map_of_mem (G2 V2).subtype hx)
  have hg1 : (π g).1 = 1 := by
    have hh := congrArg Prod.fst hg
    simpa only [map_inv,Prod.fst_inv,inv_eq_one] using hh
  exact source_tensor_intersection_of_product L T₀ H M UH V2 V3 V π hk
    (fun k => congrArg Prod.snd (hπK k)) g hg1 hgen h3V hseed hprod
    ξ dx π₄ hact hfirst hactors (IsElementaryAbelian.isPGroup 2 _) hne hu hHM hgenerate

/-- The same natural point coordinates mark both quotient factors and the
whole U₀/V₂ action. The I₂ map and both literal coordinate projections are retained. -/
theorem source_product_with_whole_section [Finite G]
    (H UH V1 V2 V3 V L2 : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h23 : V2 ≤ V3) (h3U : V3 ≤ UH) (h3V : V3 ≤ V)
    (hindex : V2.relIndex V3 = 2) (hV1 : Nat.card V1 = 2)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (hTH : (T:Subgroup G) ≤ H) (hT2 : (T:Subgroup G) ≤ G2 V2)
    (hH : H = normalizer (V1:Set G)) (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (I : Subgroup (G2 V2)) [I.Normal]
    (eI : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3))
    (hI : I.map (G2 V2).subtype = H.pCoreIn 2 ⊔ L2)
    (ht : ∀ a b : V2, a ≠ 1 → b ≠ 1 →
      ∃ i : I, ((i : G2 V2) : G) * (a:G) * ((i : G2 V2) : G)⁻¹ = b) :
    ∃ hU0 : IsElementaryAbelian 2 (U0 UH V2),
      let := hU0
      ∃ (κ : ↥(H ⊓ G2 V2) →* LinearGroup 3)
        (dU : BinaryConjugationSection (H ⊓ G2 V2) UH V2
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp κ))
        (eU : Theory.LinearAlgebra.BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2]
          (Fin 3 → ZMod 2))
        (π : G2 V2 →* LinearGroup 3 × Equiv.Perm (Fin 3))
        (ξ : Representation (ZMod 2) (LinearGroup 3 × Equiv.Perm (Fin 3))
          (Additive (U0 UH V2 ⧸ V2.subgroupOf (U0 UH V2))))
        (d0 : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ξ.comp π)),
        Function.Surjective κ ∧ κ.ker = pCore 2 ↥(H ⊓ G2 V2) ∧
        Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V2))) ∧
        Function.Surjective π ∧ π.ker = pCore 2 (G2 V2) ∧
        (∀ u : UH, (dU.coordinates u).toAdd =
          eU ((Theory.LinearAlgebra.BinaryFivePointStabilizer.line v).mkQ (d.coordinates u).toAdd)) ∧
        (∀ k : K2 H V2,
          π (inclusion ((K2_le_localNormalizer H V2).trans inf_le_right) k) =
            (κ (inclusion (K2_le_localNormalizer H V2) k),1)) ∧
        (∀ i : I, π i = (1,eI (QuotientGroup.mk' (pCore 2 I) i))) ∧
        ∀ u : U0 UH V2, (d0.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' (V2.subgroupOf (U0 UH V2)) u) := by
  obtain ⟨_,_,_,hcore,_,_,hU0⟩ := source_U0_geometry_of_natural_section H UH V1 V2 V3 V
    L2 T ρ d φ hφ hnatural hker h12 h23 h3U h3V hindex hV1 v hv hpoint
    hTH hT2 hH hV I eI hI ht
  let := hU0
  obtain ⟨κ,dU,eU,π,hκ,hκker,hκK,hπ,hπker,hcoord,hπK,hπI⟩ :=
    source_product_with_natural_section H UH V1 V2 ρ d φ hφ hnatural hker
      h12 (h23.trans h3U) v hv hpoint I eI
      (source_I2_point_supplement H V1 V2 hH h12 hV1 I ht)
  obtain ⟨ξ,d0,hcoord0⟩ := source_U0_quotient_action H UH V2 κ _ dU hκker hcore π hπ hπker
  exact ⟨hU0,κ,dU,eU,π,ξ,d0,hκ,hκker,hκK,hπ,hπker,hcoord,hπK,hπI,hcoord0⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
