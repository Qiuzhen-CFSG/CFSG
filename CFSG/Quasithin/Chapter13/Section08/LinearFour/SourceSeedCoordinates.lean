module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedDuality
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorAction
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.Representation.BinaryConjugationSection.FullLinearCoordinates
public import Theory.LinearAlgebra.BinaryTwoTransitivity
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# Compatible covered-case seed coordinates and the first tensor

The original centralizer identity O₂(I₂)=C_I₂(V₂), together with the
Lagrangian kernel comparison, constructs a faithful action of the supplied
I₂/O₂(I₂) on the literal V/V₂. Its order and dimension identify its image
with GL₂(2). Choose coordinates sending V₃/V₂ to the first line and its
image under the specified g⁻¹ to the second line. The I₂ quotient map is
unchanged; the second tensor actor is obtained from the full linear image.

The first-tensor application retains the natural U_H/V₂ coordinates and
both factors of the original G₂ quotient. It now derives the compatible
seed coordinates, both generating actors, the product U_H U_H^g, the
intersection V₂ and |U₀:V|=16 from the original natural-six data. The final
application uses the same g to prove V_H intersect V_H^g=U₀, conditional
on the compatible exterior marking and the earlier uniqueness geometry.

The exterior and second-tensor markings, extra-line movement and chief
obstruction remain with qt-d-138-linear-four-source. These applications do
not complete 13.8.28. Earlier13.8.27 retains qt-d-138-six-g2-source, and
final13.8.1 assembly retains qt-d-1381-source.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
13.5.4(6),13.8.29(3), printed pp.916,964.
-/

public noncomputable section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open SourceCompletion TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

open BinaryLinear.OuterCyclic
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification

include d in
/-- The supplied I₂ map gives natural coordinates on the actual seed quotient.
The chosen g determines the second coordinate, retaining its original conjugation. -/
theorem source_seed_natural_marking
    (A : Subgroup G) [IsElementaryAbelian 2 V]
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A)
    (hA2 : A ≤ normalizer (V₂:Set G))
    (ι : A →* Equiv.Perm (Fin 3)) (hι : Function.Surjective ι)
    (hιker : ∀ a : A, ι a = 1 ↔ (a:G) ∈ centralizer (V₂:Set G))
    (g : A) (hg : (g:G) ∉ normalizer (V₃:Set G)) :
    ∃ (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
      (c : BinaryConjugationSection A V V₂
        ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom).comp ι))
      (E : Additive (V ⧸ V₂.subgroupOf V) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)),
      (∀ v : V, (c.coordinates v).toAdd = E (Additive.ofMul (QuotientGroup.mk' (V₂.subgroupOf V) v))) ∧
      c.imageSpace V₃ = Submodule.span (ZMod 2) {first} ∧
      e (ι g⁻¹) first = second ∧
      ∃ b : Equiv.Perm (Fin 3), e b first = first ∧ e b second = first + second := by
  have h2V := d.plane_le_seed.trans d.seed_le
  let : (V₂.subgroupOf V).Normal := normal_of_isMulCommutative _
  obtain ⟨σ,c,hfaith,hcoord⟩ := BinaryConjugationSection.exists_faithful_quotient_actor
    A V V₂ hVA h2V (hALT.trans d.normalizes_V) hA2 ι hι (by
      intro a
      exact (hιker a).trans (source_seed_kernel_iff d ⟨a,hALT a.property⟩).symm)
  let W := Additive (V ⧸ V₂.subgroupOf V)
  have hV : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hdim : Module.finrank (ZMod 2) W = 2 := by
    have hh := c.card_section
    rw [hV,d.plane_card] at hh
    change 16 = Nat.card W * 4 at hh
    have hc : Nat.card W = 4 := by omega
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [Nat.card_zmod,hc] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  have hidx : V₂.relIndex V₃ = 2 := by
    have hh := (V₂.subgroupOf V₃).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe d.plane_le_seed).toEquiv,d.plane_card,d.seed_card] at hh
    change 4 * V₂.relIndex V₃ = 8 at hh
    omega
  have hline := c.imageSpace_finrank_of_index V₃ d.seed_le 1 (by simpa using hidx)
  have hne : c.imageSpace V₃ ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hline
    contradiction
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hline hu hu0
  have hmove : σ (ι g⁻¹) u ≠ u := by
    intro he
    apply hg
    rw [← inv_inv (g:G)]
    apply (normalizer (V₃:Set G)).inv_mem
    change ((g⁻¹:A):G) ∈ normalizer (V₃:Set G)
    rw [← c.subspacePreimage_imageSpace V₃ d.seed_le d.plane_le_seed,
      c.mem_normalizer_subspacePreimage_iff]
    rw [hspan,Submodule.map_span,Set.image_singleton]
    change Submodule.span (ZMod 2) {σ (ι g⁻¹) u} = _
    rw [he]
  let E₀ : W ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  have hu' : E₀ u ≠ 0 := E₀.map_ne_zero_iff.mpr hu0
  have hv' : E₀ (σ (ι g⁻¹) u) ≠ 0 := E₀.map_ne_zero_iff.mpr (by
    intro he
    have hh := congrArg (σ (ι g⁻¹)⁻¹) he
    rw [Representation.inv_self_apply,map_zero] at hh
    exact hu0 hh)
  have hf : (first : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hs : (second : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hfs : (first : Fin 2 → ZMod 2) ≠ second := by decide
  obtain ⟨r,hr₀,hr₁⟩ := BinaryLinear.exists_linearEquiv_pair
    (E₀ u) (E₀ (σ (ι g⁻¹) u)) first second hu' hv' hf hs
    (fun he => hmove (E₀.injective he).symm) hfs
  let E := E₀.trans r
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = Nat.card (LinearGroup 2) := by
    rw [Nat.card_perm,Nat.card_fin,BinaryLinear.card_GL_of_finrank (show Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 by simp)]
    decide
  obtain ⟨e,c',hc'⟩ := c.full_linear_coordinates ι hfaith E hcard
  have hfirst : c'.imageSpace V₃ = Submodule.span (ZMod 2) {first} := by
    apply eq_span_singleton_of_mem_of_finrank_eq_one
      (c'.imageSpace_finrank_of_index V₃ d.seed_le 1 (by simpa using hidx)) _ hf
    obtain ⟨v,hv,hvu⟩ := (c.mem_imageSpace_iff V₃ u).mp hu
    exact (c'.mem_imageSpace_iff V₃ first).mpr ⟨v,hv,(hc' v).trans (by rw [hvu]; exact hr₀)⟩
  have hgact : e (ι g⁻¹) first = second := by
    obtain ⟨v,hv,hvu⟩ := (c.mem_imageSpace_iff V₃ u).mp hu
    have hh := c'.equivariant g⁻¹ v
    rw [hc',c.equivariant,hc'] at hh
    change E (σ (ι g⁻¹) (c.coordinates v).toAdd) = e (ι g⁻¹) (E (c.coordinates v).toAdd) at hh
    rw [hvu,show E u = first from hr₀,show E (σ (ι g⁻¹) u) = second from hr₁] at hh
    exact hh.symm
  obtain ⟨s,hs₀,hs₁⟩ := BinaryLinear.exists_linearEquiv_pair
    first second first (first+second) hf hs hf (by decide) hfs (by decide)
  refine ⟨e,c',E,fun v => (hc' v).trans (congrArg E (hcoord v)),hfirst,hgact,e.symm s,?_,?_⟩
  · simpa only [e.apply_symm_apply] using hs₀
  · simpa only [e.apply_symm_apply] using hs₁

open scoped TensorProduct

include d in
/-- Original natural-six data constructs the seed action used by the first tensor.
Both quotient factors, the natural U_H coordinates and the specified g are retained. -/
theorem source_tensor_from_original_seed
    {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (H UH A L2 : Subgroup G) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (hH : H = normalizer (V₁:Set G))
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) UH V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (h3U : V₃ ≤ UH) (hgen : UH = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H) :
    ∃ (e : Equiv.Perm (Fin 3) ≃* LinearGroup 2)
      (E : Additive (V ⧸ V₂.subgroupOf V) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (hVS : V ≤ U0 UH V₂) (u₀ : U)
      (dt : BinaryConjugationSection (G2 V₂) (U0 UH V₂) V₂
        ((externalTensor σ
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)).comp π)),
      u₀ ≠ 0 ∧
      (∀ u : UH, (dt.coordinates (inclusion (UH_le_U0 UH V₂) u)).toAdd =
        (dU.coordinates u).toAdd ⊗ₜ[ZMod 2] first) ∧
      (∀ v : V, (dt.coordinates (inclusion hVS v)).toAdd =
        u₀ ⊗ₜ[ZMod 2] E (Additive.ofMul (QuotientGroup.mk' (V₂.subgroupOf V) v))) ∧
      U0 UH V₂ = UH ⊔ UH.conjBy ((g:G)⁻¹) ∧
      UH ⊓ UH.conjBy ((g:G)⁻¹) = V₂ ∧ V.relIndex (U0 UH V₂) = 16 := by
  let ι := eI.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hι : Function.Surjective ι := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have hιker : ∀ a : A, ι a = 1 ↔ (a:G) ∈ centralizer (V₂:Set G) := by
    intro a
    change eI (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ _
    rw [eI.map_eq_one_iff]
    change (QuotientGroup.mk a : A ⧸ pCore 2 A) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      have hh : (a:G) ∈ A.pCoreIn 2 := mem_map_of_mem A.subtype ha
      rw [hAcore] at hh
      exact hh.2
    · intro ha
      have hh : (a:G) ∈ A.pCoreIn 2 := hAcore ▸ ⟨a.property,ha⟩
      exact (mem_map_iff_mem A.subtype_injective).mp hh
  have hgmove := source_seed_moved_of_point_moved d ⟨g,hALT g.property⟩ (by
    change (g:G) ∉ normalizer (V₁:Set G)
    rwa [← hH])
  obtain ⟨e,cV,E,hcoord,hpoint,ha,b,hb₀,hb₁⟩ :=
    source_seed_natural_marking d A hALT hVA hAG ι hι hιker g hgmove
  have hindex : V₂.relIndex V₃ = 2 := by
    have hh := (V₂.subgroupOf V₃).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe d.plane_le_seed).toEquiv,d.plane_card,d.seed_card] at hh
    change 4 * V₂.relIndex V₃ = 8 at hh
    omega
  obtain ⟨hVS,u₀,dt,hu,hU,hseed,hprod,hint,hcard⟩ :=
    source_tensor_from_local_sections H UH V₂ V₃ V A L2 (T:Subgroup G)
      hK hG hV d.seed_le π hπ hπker hcore σ
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp e.toMonoidHom)
      κ dU hκker hκ hπK ι hι cV hAG hπI h3U hgen hindex hpoint hdim
      (ι g⁻¹) b ha hb₀ hb₁ (inclusion hAG g) (hπI g⁻¹)
  refine ⟨e,E,hVS,u₀,dt,hu,hU,?_,hprod,hint,hcard⟩
  intro v
  rw [hseed v,hcoord v]

include d in
/-- The literal V_H intersection uses the constructed seed marking and the same g.
Only the exterior module and the earlier uniqueness inputs remain explicit. -/
theorem source_tensor_intersection_from_original_seed
    {K U : Type*} [Group K] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (H UH A L2 : Subgroup G) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (hH : H = normalizer (V₁:Set G))
    (hK : ((K2 H V₂).subgroupOf (G2 V₂)).Normal)
    (hG : G2 V₂ = K2 H V₂ ⊔ L2 ⊔ (T:Subgroup G))
    (hV : L2 ⊔ (T:Subgroup G) ≤ normalizer (V:Set G))
    (π : G2 V₂ →* K × Equiv.Perm (Fin 3)) (hπ : Function.Surjective π)
    (hπker : π.ker = pCore 2 (G2 V₂)) (hcore : Q2 V₂ ≤ H)
    (σ : Representation (ZMod 2) K U)
    (κ : ↥(H ⊓ G2 V₂) →* K)
    (dU : BinaryConjugationSection (H ⊓ G2 V₂) UH V₂ (σ.comp κ))
    (hκker : κ.ker = pCore 2 ↥(H ⊓ G2 V₂))
    (hκ : Function.Surjective (κ.comp (inclusion (K2_le_localNormalizer H V₂))))
    (hπK : ∀ k : K2 H V₂,
      π (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_right) k) =
        (κ (inclusion (K2_le_localNormalizer H V₂) k),1))
    (eI : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hAcore : A.pCoreIn 2 = A ⊓ centralizer (V₂:Set G))
    (hALT : A ≤ L ⊔ (T:Subgroup G)) (hVA : V ≤ A) (hAG : A ≤ G2 V₂)
    (hπI : ∀ a : A, π (inclusion hAG a) = (1,eI (QuotientGroup.mk' (pCore 2 A) a)))
    (h3U : V₃ ≤ UH) (hgen : UH = conjugateSpanBy V₃ (K2 H V₂))
    (hdim : Module.finrank (ZMod 2) U = 3)
    (g : A) (hg : (g:G) ∉ H)
    (ξ : Representation (ZMod 2) H BinaryParabolicExteriorSquare.PlaneSpan.Six)
    (dx : BinaryConjugationSection H (Source.VH H V) UH ξ)
    (π₄ : H →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hact : ∀ h x, ξ h x = Atlas.Order20160A8.Bivectors.exteriorMap (π₄ h).val x)
    (hfirst : dx.imageSpace (U0 UH V₂) = BinaryParabolicExteriorSquare.PlaneSpan.firstSpace)
    (hactors : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j →
      ∃ k : K2 H V₂,
        (π₄ (inclusion ((K2_le_localNormalizer H V₂).trans inf_le_left) k)).val =
          Matrix.transvection i j 1)
    (hne : Source.VH H V ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T:Subgroup G) ≤ N → N = M)
    (hHM : ¬ H ≤ M) (hgenerate : L ⊔ (T:Subgroup G) ≤ H ⊔ zpowers (g:G)) :
    Source.VH H V ⊓ (Source.VH H V).conjBy ((g:G)⁻¹) = U0 UH V₂ := by
  obtain ⟨_,_,_,_,_,_,_,_,hprod,_,_⟩ := source_tensor_from_original_seed d
    H UH A L2 hH hK hG hV π hπ hπker hcore σ κ dU hκker hκ hπK
    eI hAcore hALT hVA hAG hπI h3U hgen hdim g hg
  have hk : π.ker ≤ H.subgroupOf (G2 V₂) := by
    rw [hπker]
    intro x hx
    exact hcore (mem_map_of_mem (G2 V₂).subtype hx)
  have hseed : V₃.conjBy ((g:G)⁻¹) ≤ V := by
    rintro x ⟨v,hv,rfl⟩
    exact (mem_normalizer_iff.mp (d.normalizes_V (hALT g⁻¹.property)) v).mp (d.seed_le hv)
  exact source_tensor_intersection_of_product L (T:Subgroup G) H M UH V₂ V₃ V π hk
    (fun k => congrArg Prod.snd (hπK k)) (inclusion hAG g)
    (congrArg Prod.fst (hπI g)) hgen d.seed_le hseed hprod ξ dx π₄ hact hfirst hactors
    (IsElementaryAbelian.isPGroup 2 _) hne hu hHM hgenerate

end CFSG.Quasithin.Chapter13.Section08.LinearFour
