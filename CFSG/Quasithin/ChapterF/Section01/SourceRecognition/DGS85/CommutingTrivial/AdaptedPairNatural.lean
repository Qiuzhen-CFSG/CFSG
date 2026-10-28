module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedCoreQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairConstruction
public import Theory.Representation.BinaryConjugationSection.Restriction
public import Theory.Representation.BinaryConjugationSection.Relabel

/-!
# The natural subgroup after adapted splitting

The source two natural core layers construct one adapted complement and its
exchanged partner. Their elementary normal join M has order q⁴. The natural
quotient Q_x/(Q_beta ∩ Q_d) restricts surjectively to M, and orders identify
its kernel with Z_x. The original adapted-factor escape gives M ∩ Q_d ≰ Q_r.

Both local fields remain distinct. Source: DGS, *Groups and Graphs* (1985),
printed p.150, the paragraph after the construction of M.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

private theorem natural_section_restrict_order
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (H Q₀ N M Z₀ : Subgroup G) [Finite Q₀]
    (π : H →* SL(2,F)) (hπ : Function.Surjective π)
    (c : BinaryConjugationSection H Q₀ N
      (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π))
    (hMQ : M ≤ Q₀) (hMN : H ≤ normalizer (M : Set G))
    (hZ : Z₀ ≤ M ⊓ N)
    (hQcard : Nat.card Q₀ = Nat.card F ^ 5)
    (hMcard : Nat.card M = Nat.card F ^ 4)
    (hZcard : Nat.card Z₀ = Nat.card F ^ 2) :
    M ⊓ N = Z₀ ∧ Nonempty (BinaryConjugationSection H M Z₀
      (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π)) := by
  let : Finite N := Finite.of_injective (inclusion c.kernel_le) (inclusion_injective _)
  let : Finite M := Finite.of_injective (inclusion hMQ) (inclusion_injective _)
  let : Finite (M ⊓ N : Subgroup G) := Finite.of_injective
    (inclusion (show M ⊓ N ≤ M from inf_le_left)) (inclusion_injective _)
  have hNcard : Nat.card N = Nat.card F ^ 3 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := F)) 2)
    have hh := c.card_section
    rw [Nat.card_fun,Nat.card_fin,hQcard] at hh
    calc Nat.card F ^ 2 * Nat.card N = Nat.card F ^ 5 := hh.symm
         _ = Nat.card F ^ 2 * Nat.card F ^ 3 := by ring
  have hMesc : ¬ M ≤ N := by
    intro hle
    have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
    rw [hMcard,hNcard] at hc
    exact (not_le_of_gt (Nat.pow_lt_pow_right (Finite.one_lt_card) (by decide : 3 < 4))) hc
  have honto := c.restricted_coordinates_surjective_of_transitive M hMQ hMN hMesc (by
    intro v w hv hw
    obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw
    obtain ⟨k,rfl⟩ := hπ g
    exact ⟨k,hg⟩)
  let cM := c.restrict M hMQ hMN honto
  have hIcard : Nat.card (M ⊓ N : Subgroup G) = Nat.card F ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := F)) 2)
    have hh := cM.card_section
    rw [Nat.card_fun,Nat.card_fin,hMcard] at hh
    calc Nat.card F ^ 2 * Nat.card (M ⊓ N : Subgroup G) = Nat.card F ^ 4 := hh.symm
         _ = Nat.card F ^ 2 * Nat.card F ^ 2 := by ring
  have he : M ⊓ N = Z₀ := (eq_of_le_of_card_ge hZ (by rw [hIcard,hZcard])).symm
  exact ⟨he,⟨cM.replaceKernel Z₀ he⟩⟩


/-- The q⁴ normal subgroup inherits the natural middle-core quotient, with
its literal kernel identified as the original center of order q². -/
theorem middle_core_natural_subgroup
    (Γ : Bool → Subgroup G) (beta x d : Vertex Γ)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup Γ x ⧸ pCore 2 (graphLocalGroup Γ x)) ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hsec : CoreQuotientSection Γ beta x d F ex)
    (M : Subgroup G) [Finite (Q Γ x)]
    (hMQ : M ≤ Q Γ x) (hMN : graphLocalGroup Γ x ≤ normalizer (M : Set G))
    (hZM : Z Γ x ≤ M) (hZN : Z Γ x ≤ Q Γ beta ⊓ Q Γ d)
    (hQcard : Nat.card (Q Γ x) = Nat.card F ^ 5)
    (hMcard : Nat.card M = Nat.card F ^ 4)
    (hZcard : Nat.card (Z Γ x) = Nat.card F ^ 2) :
    let π := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ x)))
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    M ⊓ (Q Γ beta ⊓ Q Γ d) = Z Γ x ∧
      Nonempty (BinaryConjugationSection (graphLocalGroup Γ x) M (Z Γ x)
        (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π)) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hN,_,hE,σ,c,_,he⟩ := hsec
  let := hN
  let := hE
  obtain ⟨E,hE⟩ := he n hn hF
  let ι : σ.Equiv ((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)) :=
    Representation.Equiv.mk E (by intro g; apply LinearMap.ext; intro v; exact hE g v)
  let π := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ x)))
  exact natural_section_restrict_order (graphLocalGroup Γ x) (Q Γ x)
    (Q Γ beta ⊓ Q Γ d) M (Z Γ x) π
    (ex.surjective.comp (QuotientGroup.mk'_surjective _)) (c.relabel π ι)
    hMQ hMN (le_inf hZM hZN) hQcard hMcard hZcard


variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The two original source core layers construct the natural q⁴ subgroup
and its terminal-core escape. Both local fields and all literal kernels are retained. -/
theorem reduced_core_adapted_natural_pair
    (h : HypothesisF11 L S)
    {x beta d r : Vertex (Reduction.reducedFamily L S)}
    (hb : (graph (Reduction.reducedFamily L S)).Adj x beta)
    (hd : (graph (Reduction.reducedFamily L S)).Adj x d) (hne : beta ≠ d)
    (hb3 : b (Reduction.reducedFamily L S) = 3)
    {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    (ex : (graphLocalGroup (Reduction.reducedFamily L S) x ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) x)) ≃* SL(2,K))
    (ed : (graphLocalGroup (Reduction.reducedFamily L S) d ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) d)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hres : NaturalResidualSection h d ed n)
    (hsec : CoreQuotientSection (Reduction.reducedFamily L S) r d x F ed)
    (hNspan : Q (Reduction.reducedFamily L S) r ⊓ Q (Reduction.reducedFamily L S) x =
      V (Reduction.reducedFamily L S) d 1)
    (hωd : Z (Reduction.reducedFamily L S) d =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) d))
    (hc : ⁅Q (Reduction.reducedFamily L S) d,V (Reduction.reducedFamily L S) d 1⁆ ≤
      Z (Reduction.reducedFamily L S) d)
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) d 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) d) = Nat.card F)
    (hZspan : Z (Reduction.reducedFamily L S) x =
      Z (Reduction.reducedFamily L S) beta ⊔ Z (Reduction.reducedFamily L S) d)
    (hZxcard : Nat.card (Z (Reduction.reducedFamily L S) x) = Nat.card K ^ 2) :
    let Γ := Reduction.reducedFamily L S
    let N := Q Γ beta ⊓ Q Γ d
    let π := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ x)))
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    ⁅Q Γ d,Q Γ d⁆ ≤ Z Γ d ∧ Nat.card N = Nat.card K ^ 3 ∧
      N ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (N : Set (Reduction.G₀ L S)) ∧
      CoreQuotientSection Γ beta x d K ex ∧
      ∃ M : Subgroup (Reduction.G₀ L S),
        M ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (M : Set (Reduction.G₀ L S)) ∧
        IsElementaryAbelian 2 M ∧ Nat.card M = Nat.card K ^ 4 ∧
        M ⊓ N = Z Γ x ∧
        Nonempty (BinaryConjugationSection (graphLocalGroup Γ x) M (Z Γ x)
          (((specialLinearNatural (k := K) 2).restrictScalars (k := ZMod 2)).comp π)) ∧
        ¬ M ⊓ Q Γ d ≤ Q Γ r := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (Q Γ x) := Finite.of_injective
    (inclusion (Q_le_stabilizer Γ x)) (inclusion_injective _)
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hob := Reduction.reduced_graph_core_obstruction h
  obtain ⟨hdd,Wd,hWd,hWVd,_,_,_,hWE,_,g,hgd,_,_,hWVb,_,_,_,hMQ,hMN,hME,hMcard,_,_,hDesc⟩ :=
    reduced_core_adapted_pair h hb hd hne ex ed hKF hn hF hres hsec hNspan hωd hc hVcard hZcard
  let f := (MulAut.conj (g : Reduction.G₀ L S)).toMonoidHom
  let Wb := Wd.map f
  let M := (Wb ⊓ Q Γ x) ⊔ (Wd ⊓ Q Γ x)
  have hmapQ : (Q Γ d).map f = Q Γ beta := by rw [←Q_translate,hgd]
  have hmapZ : (Z Γ d).map f = Z Γ beta := by rw [←Z_translate,hgd]
  have hdb : ⁅Q Γ beta,Q Γ beta⁆ ≤ Z Γ beta := by
    have hh := map_mono (f := f) hdd
    rwa [map_commutator,hmapQ,hmapZ] at hh
  obtain ⟨_,fb,_,_,_⟩ := local_quotient_parameter_transport ht (g : Reduction.G₀ L S) hgd
  let eb := fb.symm.trans ed
  have hZxQ {v : Vertex Γ} (hv : (graph Γ).Adj x v) : Z Γ x ≤ Q Γ v :=
    Z_le_Q_of_dist_lt_b Γ (fun z => (source_Z_Q_U ht z).1) (source_kernel_sylow ht hB hS)
      x v (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hv,hb3]; decide)
  have hZb : Z Γ beta ≤ Z Γ x := hZspan ▸ le_sup_left
  have hZd : Z Γ d ≤ Z Γ x := hZspan ▸ le_sup_right
  have hZbd := hZb.trans (hZxQ hd)
  have hZdb := hZd.trans (hZxQ hb)
  have hbes := core_escape_of_intersection_obstruction Γ (hob beta x hb.symm)
  have hdes := core_escape_of_intersection_obstruction Γ (hob d x hd.symm)
  obtain ⟨hNQ,hNN⟩ := adjacent_core_intersection_normal ht hB hS hb hd hne hbes hdes ex
    hZbd hZdb hdb hdd
  have hsection := adjacent_core_intersection_natural_section ht hB hS hob hb hd hne
    eb ex ed hKF hZbd hZdb hdb hdd
  have hZM : Z Γ x ≤ M := by
    rw [hZspan]
    exact sup_le ((le_inf (hWVb ▸ inf_le_left) (hZb.trans
      ((source_Z_Q_U ht x).1.trans (map_subtype_le _)))).trans le_sup_left)
      ((le_inf (hWVd ▸ inf_le_left) (hZd.trans
        ((source_Z_Q_U ht x).1.trans (map_subtype_le _)))).trans le_sup_right)
  have hQdcard : Nat.card (Q Γ d) = Nat.card F ^ 5 := by
    obtain ⟨hN,hcard,hE,_,cD,_,_⟩ := hsec
    let := hN
    let := hE
    have hh := cD.card_section
    change Nat.card (Q Γ d) = Nat.card (Q Γ d ⧸ (Q Γ r ⊓ Q Γ x).subgroupOf (Q Γ d)) *
      Nat.card (Q Γ r ⊓ Q Γ x : Subgroup (Reduction.G₀ L S)) at hh
    rw [hcard,hNspan,hVcard] at hh
    exact hh.trans (by ring)
  have hQxcard : Nat.card (Q Γ x) = Nat.card K ^ 5 := by
    have hx := relIndex_mul_card_of_le (show Q Γ d ⊓ Q Γ x ≤ Q Γ x from inf_le_right)
    have hd' := relIndex_mul_card_of_le (show Q Γ d ⊓ Q Γ x ≤ Q Γ d from inf_le_left)
    have hix : (Q Γ d).relIndex (Q Γ x) = Nat.card F :=
      linear_adjacent_core_index ht hB hS hd.symm
        (core_escape_of_intersection_obstruction Γ (hob x d hd)) ed
    have hid : (Q Γ x).relIndex (Q Γ d) = Nat.card K :=
      linear_adjacent_core_index ht hB hS hd hdes ex
    rw [inf_relIndex_right,hix] at hx
    rw [inf_relIndex_left,hid,hKF] at hd'
    rw [←hx,hd',hQdcard,hKF]
  have hNcard : Nat.card (Q Γ beta ⊓ Q Γ d : Subgroup (Reduction.G₀ L S)) = Nat.card K ^ 3 := by
    obtain ⟨hN,hcard,_⟩ := hsection
    let := hN
    have hh := relIndex_mul_card_of_le hNQ
    change Nat.card (Q Γ x ⧸ (Q Γ beta ⊓ Q Γ d).subgroupOf (Q Γ x)) *
      Nat.card (Q Γ beta ⊓ Q Γ d : Subgroup (Reduction.G₀ L S)) = Nat.card (Q Γ x) at hh
    change Nat.card (Q Γ x ⧸ (Q Γ beta ⊓ Q Γ d).subgroupOf (Q Γ x)) = Nat.card K ^ 2 at hcard
    rw [hcard,hQxcard] at hh
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := K)) 2)
    exact hh.trans (by ring)
  have hMcardK : Nat.card M = Nat.card K ^ 4 := by rw [hKF]; exact hMcard
  obtain ⟨hinter,hcM⟩ := middle_core_natural_subgroup Γ beta x d ex hn (hKF.trans hF)
    hsection M hMQ hMN hZM (le_inf (hZxQ hb) (hZxQ hd)) hQxcard hMcardK hZxcard
  refine ⟨hdd,hNcard,hNQ,hNN,hsection,M,hMQ,hMN,hME,hMcardK,hinter,hcM,?_⟩
  intro hle
  apply hDesc
  rw [←hNspan]
  exact le_inf ((le_inf le_sup_right (inf_le_left.trans hWd)).trans hle) inf_le_right

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
