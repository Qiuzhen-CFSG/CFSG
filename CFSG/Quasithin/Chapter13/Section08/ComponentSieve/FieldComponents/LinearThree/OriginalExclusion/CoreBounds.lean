module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.NaturalReduction
public import CFSG.Quasithin.Chapter13.Section07.SourceDuality
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# The fixed core and size bounds in the original binary whole quotient

The marked natural three-space U_H/V₁ is irreducible. The original seed
noncentrality therefore identifies C_{U_H}(O₂(H)) with V₁. The literal
central commutator pairing then gives |O₂(H):H_C| = 8. Since U_H has
order sixteen and lies in H_C, the two-core has order at least 128.
The common Sylow has index eight over O₂(H) and index at most sixteen
over O₂(LT), giving |O₂(LT)| ≥ 64.

These are the numerical inputs to the C₃-system argument in 13.7.6(1),
used by 13.8.19. They apply to the original abelian span; no nonabelian
V_H hypothesis or discarded central line is used. The local residues
and final binary exclusion remain with the field-sieve assembly owner.
Source: Aschbacher–Smith, F.9.7, 13.7.6(1), and 13.8.19,
printed pp.321,940,953 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The radical fixed by the whole two-core is the original central line. -/
theorem source_binary_fixed_core
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G) = V₁ := by
  have h := c.f9 H c.component.local_overgroup
  obtain ⟨e,⟨f⟩,_⟩ := source_binary_marked_natural c act e₀
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let σ := BinaryLinearThree.W.comp π
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let : IsIrreducible σ := (irreducible_comp_surjective_iff π hπ _).mpr
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let q := QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
  let s : BinaryConjugationSection H (Source.UH H V₃) V₁ σ := {
    section_le := h.UH_le_H
    kernel_le := act.line_le
    normalized := le_normalizer_conjugateSpanBy V₃ H
    coordinates := {
      toFun := fun u => Multiplicative.ofAdd (f (Additive.ofMul (q u)))
      map_one' := by change f (0 : Additive (Source.Utilde H V₃ V₁)) = 0; exact map_zero f
      map_mul' := fun a b => by
        change f (Additive.ofMul (q (a * b))) = f (Additive.ofMul (q a)) + f (Additive.ofMul (q b))
        rw [map_mul]; exact map_add f _ _ }
    onto := fun w => by
      obtain ⟨v,hv⟩ := f.toLinearEquiv.surjective w.toAdd
      obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
      exact ⟨u,by change f (Additive.ofMul (q u)) = w.toAdd; rw [hu]; exact hv⟩
    kernel_eq := by
      ext u
      change f.toLinearEquiv (Additive.ofMul (q u)) = 0 ↔ _
      rw [map_eq_zero_iff f.toLinearEquiv f.toLinearEquiv.injective]
      exact QuotientGroup.eq_one_iff u
    equivariant := fun a u => by
      change f (Additive.ofMul (q _)) = BinaryLinearThree.W (e (QuotientGroup.mk' (pCore 2 H) a)) _
      apply (congrArg f (act.conjugation a u).symm).trans
      have hh := LinearMap.congr_fun (f.isIntertwining'
        (e (QuotientGroup.mk' (pCore 2 H) a))) (Additive.ofMul (q u))
      change f (act.representation (e.symm (e (QuotientGroup.mk' (pCore 2 H) a)))
        (Additive.ofMul (q u))) = BinaryLinearThree.W (e (QuotientGroup.mk' (pCore 2 H) a))
          (f (Additive.ofMul (q u))) at hh
      rw [e.symm_apply_apply] at hh
      exact hh }
  apply s.inf_eq_kernel_of_irreducible (centralizer (Source.QH H : Set G))
  · exact (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).trans
      (normalizer_le_normalizer_centralizer _)
  · exact le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes)
  · intro hc
    exact Section07.seed_noncentral_on_local_core h c.component.local_overgroup.2.1
      c.noncentral_core (commutator_eq_bot_iff_le_centralizer.mpr
        ((le_conjugateSpanBy V₃ H).trans hc))

/-- The full centralizer quotient has the order of the dual natural three-space. -/
theorem source_binary_dual_index
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    (Source.HC H V₃).relIndex (Source.QH H) = 8 := by
  have h := c.f9 H c.component.local_overgroup
  obtain ⟨hE,ρ,sU,sQ,_,_⟩ := Section07.source_central_duality (localNaturalSetup c.localSetup) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  let := hE
  let U := Source.UH H V₃
  let U₀ := U ⊓ centralizer (Source.QH H : Set G)
  let W := Additive (U ⧸ U₀.subgroupOf U)
  let := sQ.kernel_normal
  have hcard : Nat.card W = 8 := by
    have hm := sU.card_section
    have hs := (source_binary_module_size c act e₀).2
    have hz : Nat.card U₀ = 2 := by
      rw [show U₀ = V₁ from source_binary_fixed_core c act e₀,c.localSetup.line_card]
    change Nat.card U = Nat.card W * Nat.card U₀ at hm
    change Nat.card U = 16 at hs
    rw [hs,hz] at hm
    omega
  change ((Source.HC H V₃).subgroupOf (Source.QH H)).index = 8
  rw [index_eq_card]
  calc
    _ = Nat.card (Module.Dual (ZMod 2) W) := Nat.card_congr sQ.quotientEquiv.toEquiv
    _ = 8 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
        ←Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),hcard]


/-- The central binary pairing forces a two-core of order at least 128. -/
theorem source_binary_core_card
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    128 ≤ Nat.card (Source.QH H) := by
  have h := c.f9 H c.component.local_overgroup
  have hUC : Source.UH H V₃ ≤ Source.HC H V₃ :=
    le_inf h.UH_le_H (commutator_eq_bot_iff_le_centralizer.mp
      (commutator_self_eq_bot_iff.mpr inferInstance))
  have hCQ : Source.HC H V₃ ≤ Source.QH H := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro z hz
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hz.1, fun u hu => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hz.2 u hu)]
      exact V₁.one_mem⟩
  have hl := Nat.card_le_card_of_injective (inclusion hUC) (inclusion_injective hUC)
  rw [(source_binary_module_size c act e₀).2] at hl
  have hm := ((Source.HC H V₃).subgroupOf (Source.QH H)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv] at hm
  change Nat.card (Source.HC H V₃) * (Source.HC H V₃).relIndex (Source.QH H) = _ at hm
  rw [source_binary_dual_index c act e₀] at hm
  omega

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The original common Sylow has index at most sixteen over O₂(LT). -/
theorem source_local_core_index_le_sixteen
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (T : Subgroup G) ≤ 16 := by
  let d := localNaturalSetup c.localSetup
  have h := c.f9 H c.component.local_overgroup
  rw [Section07.core_relIndex_eq_image_card d h (T : Subgroup G) le_rfl]
  let X := L ⊔ (T : Subgroup G)
  let R := ((T : Subgroup G).subgroupOf X).map (Section07.NaturalAction.permutation d)
  have hp : IsPGroup 2 R :=
    ((T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).isPGroup').map _
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hc := Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)
  have hs : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  exact hc.trans_eq hs

/-- The original binary whole quotient gives the strict core bound required
by I.5, without any assumption that V_H is nonabelian. -/
theorem source_binary_large_local_core
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e₀ : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    64 ≤ Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have h := c.f9 H c.component.local_overgroup
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTH : (T : Subgroup G) ≤ H := h.T_le_H
  have hQHT : Source.QH H ≤ (T : Subgroup G) := h.QH_le_T
  have hQT : Q ≤ (T : Subgroup G) := h.sylow_centralizer.symm.le.trans inf_le_left
  have hi : (Source.QH H).relIndex (T : Subgroup G) = 8 := by
    have he := relIndex_map_map_of_injective (pCore 2 H)
      ((T : Subgroup G).subgroupOf H) H.subtype_injective
    rw [map_subgroupOf_eq_of_le hTH,←QuotientGroup.ker_mk' (pCore 2 H),relIndex_ker] at he
    let P := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
    rw [QuotientGroup.ker_mk'] at he
    change (Source.QH H).relIndex (T : Subgroup G) = Nat.card P at he
    rw [he,P.card_eq_multiplicity,Nat.card_congr e₀.toEquiv,Matrix.PSL3Two.card_PSL]
    decide +kernel
  have hm := ((Source.QH H).subgroupOf (T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQHT).toEquiv] at hm
  change Nat.card (Source.QH H) * (Source.QH H).relIndex (T : Subgroup G) = _ at hm
  rw [hi] at hm
  have hq := (Q.subgroupOf (T : Subgroup G)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv] at hq
  change Nat.card Q * Q.relIndex (T : Subgroup G) = _ at hq
  have hb := source_local_core_index_le_sixteen c
  have hc := source_binary_core_card c act e₀
  change Q.relIndex (T : Subgroup G) ≤ 16 at hb
  change 64 ≤ Nat.card Q
  nlinarith [Nat.mul_le_mul_left (Nat.card Q) hb]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
