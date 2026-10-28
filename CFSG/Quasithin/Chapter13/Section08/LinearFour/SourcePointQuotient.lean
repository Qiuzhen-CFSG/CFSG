module
public import Theory.Representation.BinaryConjugationSection.PointQuotient
public import Theory.Representation.BinaryConjugationSection.NaturalGeneration
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorActors

/-!
# The actual K₂ quotient and its natural three-section

The original natural marking of U_H/V₁ maps N_H(V₂) onto the full point
stabilizer. Passing to the quotient by V₂/V₁ constructs coordinates on the
literal U_H/V₂. The action is onto GL₃(2), both for the point normalizer and
for K₂ = O²(N_H(V₂)); each kernel is its intrinsic two-core. This identifies
K₂/O₂(K₂) with the concrete PSL₃(2) and constructs its natural module.

Transitivity on nonzero vectors in that quotient proves U_H = ⟨V₃^{K₂}⟩.
The original F.9 application obtains the point marking and proper seed from
the subgroup orders two, four and eight. The tensor-intersection application
then removes its separate K₂-generation premise, retaining the original
conjugator and quotient maps.

This supplies the quotient and natural-action parts of 13.8.29. Subnormality
inside the full G₂, the compatible tensor and exterior markings, extra-line
movement and the nine-factor/chief obstruction still require source assembly.
The four-dimensional natural marking remains an input. These results do not
complete 13.8.28. Earlier 13.8.27 setup and final 13.8.1 assembly retain their
existing owners.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, 13.8.29(1),(3), printed pp.963--964.
-/

public noncomputable section
open Subgroup Representation
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open Theory.LinearAlgebra BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G : Type*} [Group G] [Finite G]

private theorem point_quotient_marking_in_coordinates
    (H UH V1 V2 : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v})
    (e : QuotientSpace v ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    ∃ (ψ : ↥(H ⊓ G2 V2) →* LinearGroup 3)
      (d₃ : BinaryConjugationSection (H ⊓ G2 V2) UH V2
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ψ)),
      Function.Surjective ψ ∧ ψ.ker = pCore 2 ↥(H ⊓ G2 V2) ∧
      Function.Surjective (ψ.comp (inclusion (K2_le_localNormalizer H V2))) ∧
      (ψ.comp (inclusion (K2_le_localNormalizer H V2))).ker = pCore 2 (K2 H V2) ∧
      ∀ u : UH, (d₃.coordinates u).toAdd = e ((line v).mkQ (d.coordinates u).toAdd) := by
  let P := H ⊓ G2 V2
  let f := φ.comp (inclusion (show P ≤ H from inf_le_left))
  have himage : f.range = stabilizer v := source_local_normalizer_image H UH V1 V2 ρ d φ hφ hnatural h12 h2U v hv hpoint
  let α : P →* stabilizer v := f.codRestrict (stabilizer v)
    (fun x => by rw [←himage]; exact ⟨x,rfl⟩)
  have hα : Function.Surjective α := by
    intro a
    have ha : a.val ∈ f.range := by rw [himage]; exact a.property
    obtain ⟨x,hx⟩ := ha
    exact ⟨x,Subtype.ext hx⟩
  have hαker : IsPGroup 2 α.ker := by
    have he : α.ker = φ.ker.comap (inclusion (show P ≤ H from inf_le_left)) := by
      ext x
      change α x = 1 ↔ φ (inclusion _ x) = 1
      exact Subtype.ext_iff
    rw [he]
    exact hker.comap_of_injective _ (inclusion_injective _)
  let ψ : P →* LinearGroup 3 := (linearGroupCongr e).toMonoidHom.comp
    ((BinaryFivePointStabilizer.quotientAction v).comp α)
  have hψ : Function.Surjective ψ :=
    (linearGroupCongr e).surjective.comp ((quotientAction_surjective v).comp hα)
  have hψker : IsPGroup 2 ψ.ker := by
    have he : ψ.ker = (kernel v).comap α := by
      dsimp only [ψ]
      rw [MonoidHom.ker_comp_of_injective _ _ (linearGroupCongr e).injective]
      rfl
    rw [he]
    exact (IsElementaryAbelian.isPGroup 2 (kernel v)).comap_of_ker_isPGroup α hαker
  let : Finite (LinearGroup 3) := Finite.of_injective
    (fun g : LinearGroup 3 => (g : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective
  have hψcore : ψ.ker = pCore 2 P := by
    have hh := ψ.comap_pCore_of_ker_isPGroup hψ hψker
    rwa [linearGroup_twoCore_eq_bot,MonoidHom.comap_bot] at hh
  have hUH : UH ≤ P := le_inf d.section_le
    (((commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr
      (inferInstance : IsMulCommutative UH))).trans (centralizer_le h2U)).trans
      (Subgroup.centralizer_le_normalizer _))
  let d₃ := d.pointQuotientSection P V2 inf_le_left hUH h2U h12 v hpoint α e
    (fun a w => hnatural (inclusion (show P ≤ H from inf_le_left) a) w)
  let j := inclusion (K2_le_localNormalizer H V2)
  have hKonto : Function.Surjective (ψ.comp j) := by
    intro a
    obtain ⟨b,hb⟩ := (linearGroupCongr e).surjective a
    obtain ⟨s,hs⟩ := quotientAction_surjective v b
    have hK := source_K2_image H UH V1 V2 ρ d φ hφ hnatural h12 h2U v hv hpoint
    have hsK : s.val ∈ (φ.comp (inclusion ((K2_le_localNormalizer H V2).trans inf_le_left))).range := by
      rw [hK]; exact s.property
    obtain ⟨k,hk⟩ := hsK
    have he : α (j k) = s := Subtype.ext hk
    exact ⟨k,by change linearGroupCongr e (BinaryFivePointStabilizer.quotientAction v (α (j k))) = a; rw [he,hs,hb]⟩
  have hKcore : (ψ.comp j).ker = pCore 2 (K2 H V2) := by
    have hp : IsPGroup 2 (ψ.comp j).ker := by
      rw [←MonoidHom.comap_ker]
      exact hψker.comap_of_injective _ (inclusion_injective _)
    have hh := (ψ.comp j).comap_pCore_of_ker_isPGroup hKonto hp
    rwa [linearGroup_twoCore_eq_bot,MonoidHom.comap_bot] at hh
  exact ⟨ψ,d₃,hψ,hψcore,hKonto,hKcore,fun _ => rfl⟩

/-- Construct the literal natural three-section and both intrinsic two-core kernels. -/
theorem source_point_quotient_marking
    (H UH V1 V2 : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v}) :
    ∃ (ψ : ↥(H ⊓ G2 V2) →* LinearGroup 3)
      (d₃ : BinaryConjugationSection (H ⊓ G2 V2) UH V2
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ψ))
      (e : QuotientSpace v ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      Function.Surjective ψ ∧ ψ.ker = pCore 2 ↥(H ⊓ G2 V2) ∧
      Function.Surjective (ψ.comp (inclusion (K2_le_localNormalizer H V2))) ∧
      (ψ.comp (inclusion (K2_le_localNormalizer H V2))).ker = pCore 2 (K2 H V2) ∧
      ∀ u : UH, (d₃.coordinates u).toAdd = e ((line v).mkQ (d.coordinates u).toAdd) := by
  have hdim : Module.finrank (ZMod 2) (QuotientSpace v) = 3 := by
    have hh := (line v).finrank_quotient_add_finrank
    rw [finrank_span_singleton hv,Module.finrank_fin_fun] at hh
    change Module.finrank (ZMod 2) (QuotientSpace v) + 1 = 4 at hh
    omega
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (QuotientSpace v) hdim).equivFun
  obtain ⟨ψ,d₃,hψ,hcore,hK,hKcore,hcoord⟩ := point_quotient_marking_in_coordinates
    H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint e
  exact ⟨ψ,d₃,e,hψ,hcore,hK,hKcore,hcoord⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour




namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Subgroup Representation
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open Theory.LinearAlgebra BinaryFivePointStabilizer
variable {G : Type*} [Group G] [Finite G]

/-- The actual K₂ has the source quotient PSL₃(2), through its original
point-normalizer action and intrinsic two-core. -/
theorem source_K2_quotient_three
    (H UH V1 V2 : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h2U : V2 ≤ UH)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v}) :
    Nonempty ((K2 H V2 ⧸ pCore 2 (K2 H V2)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨ψ,_,_,_,_,honto,hcore,_⟩ :=
    source_point_quotient_marking H UH V1 V2 ρ d φ hφ hnatural hker h12 h2U v hv hpoint
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ honto).trans linearThreeEquivProjective)⟩

/-- Transitivity on the constructed quotient U_H/V₂ gives the exact
K₂-conjugate span of the original seed, as used in the first tensor. -/
theorem source_K2_seed_span
    (H UH V1 V2 V3 : Subgroup G) [IsMulCommutative UH]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (φ : H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (h12 : V1 ≤ V2) (h23 : V2 ≤ V3) (h3U : V3 ≤ UH) (hproper : ¬ V3 ≤ V2)
    (v : Fin 4 → ZMod 2) (hv : v ≠ 0)
    (hpoint : d.imageSpace V2 = Submodule.span (ZMod 2) {v}) :
    UH = conjugateSpanBy V3 (K2 H V2) := by
  obtain ⟨ψ,d₃,_,_,_,honto,_,_⟩ := source_point_quotient_marking
    H UH V1 V2 ρ d φ hφ hnatural hker h12 (h23.trans h3U) v hv hpoint
  exact (d₃.conjugateSpan_eq_of_surjective_linear_action (K2 H V2) V3
    (K2_le_localNormalizer H V2) h3U h23 hproper
    (ψ.comp (inclusion (K2_le_localNormalizer H V2))) honto (fun _ _ => rfl)).symm

/-- On the original F.9 seed, the orders two, four and eight construct the
point marking and prove the first tensor's K₂-generation premise. -/
theorem source_UH_eq_K2_seed_span
    (F : ChapterF.Section09.Setup G) (hF : F.Hypothesis)
    [IsMulCommutative (Source.UH F.H F.Vplus)]
    (ρ : Representation (ZMod 2) F.H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection F.H (Source.UH F.H F.Vplus) F.V₁ ρ)
    (φ : F.H →* LinearGroup 4) (hφ : Function.Surjective φ)
    (hnatural : ∀ h x, ρ h x = φ h x) (hker : IsPGroup 2 φ.ker)
    (V2 : Subgroup G) (h12 : F.V₁ ≤ V2) (h23 : V2 ≤ F.Vplus)
    (hV2 : Nat.card V2 = 4) (hV3 : Nat.card F.Vplus = 8) :
    Source.UH F.H F.Vplus = conjugateSpanBy F.Vplus (K2 F.H V2) := by
  have hi : F.V₁.relIndex V2 = 2 := by
    have hh := (F.V₁.subgroupOf V2).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h12).toEquiv,hF.point_card,hV2] at hh
    change 2 * F.V₁.relIndex V2 = 4 at hh
    omega
  have h2U : V2 ≤ Source.UH F.H F.Vplus := h23.trans (le_conjugateSpanBy _ _)
  have hd := d.imageSpace_finrank_of_index V2 h2U 1 (by simpa using hi)
  have hn : d.imageSpace V2 ≠ ⊥ := by intro he; rw [he] at hd; simp at hd
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hp := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  have hproper : ¬ F.Vplus ≤ V2 := by
    intro h
    have hh := card_dvd_of_le h
    rw [hV3,hV2] at hh
    norm_num at hh
  exact source_K2_seed_span F.H (Source.UH F.H F.Vplus) F.V₁ V2 F.Vplus
    ρ d φ hφ hnatural hker h12 h23 (le_conjugateSpanBy _ _) hproper v hv0 hp

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I U W : Type*} [Group G] [Group K] [Group I] [Group.IsSolvable I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
/-- The constructed K₂ generation discharges the orbit premise in the
literal tensor intersection. The source conjugator and both action maps
are unchanged; the remaining tensor and exterior markings stay explicit. -/
theorem source_first_tensor_intersection_of_generated_seed [Finite G]
    (L T H M UH V2 V3 V : Subgroup G) (π : G2 V2 →* K × I)
    (ρ : Representation (ZMod 2) (K × I) W)
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
    (himage : f.range.toSubmodule = d.imageSpace UH)
    (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
    (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
    (ht : t first = f u₀) (a : I) (ha : μ a first = second)
    (hf : Function.Injective f) (b : I)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (hker : π.ker ≤ H.subgroupOf (G2 V2))
    (g : G2 V2) (hg : π g⁻¹ = (1,a)) (hV2U : V2 ≤ UH)
    [IsMulCommutative UH]
    (h23 : V2 ≤ V3) (h3U : V3 ≤ UH) (hproper : ¬ V3 ≤ V2)
    (hV3 : V3 ≤ V) (hseed : V3.conjBy ((g:G)⁻¹) ≤ V)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* SL(4,ZMod 2)) (hπ₄ : Function.Surjective π₄)
    (V1 : Subgroup G) (h12 : V1 ≤ V2)
    (ρ₄ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d₄ : BinaryConjugationSection H UH V1 ρ₄)
    (hnatural : ∀ h x, ρ₄ h x = (π₄ h).val.mulVec x)
    (hkernel : IsPGroup 2 π₄.ker)
    (hpoint : d₄.imageSpace V2 = Submodule.span (ZMod 2) {Pi.single 0 1})
    (hact : ∀ h x, ξ h x = exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V2) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hp : IsPGroup 2 (Source.VH H V)) (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgen : L ⊔ T ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V2 := by
  let φ := (slEquivLinear 4).toMonoidHom.comp π₄
  have hφ : Function.Surjective φ := (slEquivLinear 4).surjective.comp hπ₄
  have hnat : ∀ h x, ρ₄ h x = φ h x := fun h x =>
    (hnatural h x).trans (slEquivLinear_apply 4 (π₄ h) x).symm
  have hφker : IsPGroup 2 φ.ker := by
    have he : φ.ker = π₄.ker := by
      ext h
      change slEquivLinear 4 (π₄ h) = 1 ↔ π₄ h = 1
      exact (slEquivLinear 4).map_eq_one_iff
    exact he.symm ▸ hkernel
  have hv : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp at hh
  have hUH := source_K2_seed_span H UH V1 V2 V3 ρ₄ d₄ φ hφ hnat hφker
    h12 h23 h3U hproper (Pi.single 0 1) hv hpoint
  exact source_first_tensor_intersection_of_natural_action L T H M UH V2 V3 V
    π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1 hker g hg hV2U hUH
    hV3 hseed ξ dx π₄ hπ₄ V1 h12 ρ₄ d₄ hnatural hkernel hpoint
    hact hfirst hp hne hu hHM hgen

end CFSG.Quasithin.Chapter13.Section08.LinearFour
