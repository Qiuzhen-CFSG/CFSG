module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesAction
public import CFSG.Quasithin.ChapterG.Section02.Binary.CoreIntersection
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences

/-!
# The faithful opposite-subgroup image

G.2.3 identifies the exact kernel of the opposite subgroup on U/V₁.
Its two-core image therefore agrees in order with its faithful action
image, which is elementary and satisfies |U:S₂| = 2 |A*|.
The Cartan application is re-exported through EscapeModulesBinary.
Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

namespace SpanAction
variable {D : Setup G}

/-- The exact kernel on the opposite subgroup in the faithful span action. -/
theorem binary_opposite_kernel (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    (projection h).ker ⊓ (conjugate (D.W g) g).subgroupOf D.H =
      (D.S₂ g).subgroupOf D.H := by
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ :=
    Setup.binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hA, σ, d, hS, hprod, hVE, hES, hVcentral, hVN, hEN,
    hEC, hEE, hcoord, hfinite, hcompl, htensor, hcard, hmarks, hfix⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI (Setup.binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  let := hN
  let := hA
  have hXS : conjugate (D.W g) g ≤ D.S g := le_sup_right.trans hS.ge
  have hEX : D.S₂ g ≤ conjugate (D.W g) g := by
    rw [D.binary_marked_intersection g hgI hES]
    exact inf_le_right
  have hUneW : ¬ D.U ≤ D.W g := by
    intro hu
    have heq : D.W g = D.U := le_antisymm inf_le_left hu
    rw [heq, relIndex_self] at hindex
    omega
  obtain ⟨u, hu, huw⟩ := SetLike.not_le_iff_exists.mp hUneW
  let ui : D.I g := ⟨u, mem_sup_left hu⟩
  apply le_antisymm
  · intro x hx
    let xs : D.S g := ⟨x, hXS hx.2⟩
    have hxc : (d.coordinates xs).toAdd ∈ d.imageSpace (conjugate (D.W g) g) :=
      (d.mem_imageSpace_iff _ _).mpr ⟨xs, hx.2, rfl⟩
    have hcomm : ⁅u, (x : G)⁆ ∈ D.S₂ g :=
      hVE (h.point_le ((projection_eq_one_iff h x).mp hx.1 u hu))
    have hxf : σ (D.binaryCoreProjection g
        (Setup.binarySourceCoreEquiv h b hUT g hgL hgN) ui) (d.coordinates xs).toAdd =
        (d.coordinates xs).toAdd := by
      let xa : D.S g := ⟨u * (x : G) * u⁻¹,
        (mem_normalizer_iff.mp (d.normalized ui.property) x).mp xs.property⟩
      have hz := (d.coordinates_eq_one_iff (xa * xs⁻¹)).mpr hcomm
      rw [map_mul, map_inv, mul_inv_eq_one] at hz
      exact (d.equivariant ui xs).symm.trans (congrArg Multiplicative.toAdd hz)
    have hxw : (d.coordinates xs).toAdd ∈ d.imageSpace (D.W g) := by
      rw [← (hmarks ui hu huw).1]
      exact sub_eq_zero.mpr hxf
    have hzero : (d.coordinates xs).toAdd = 0 :=
      hcompl.disjoint.le_bot ⟨hxw, hxc⟩
    exact (d.coordinates_eq_one_iff xs).mp hzero
  · intro x hx
    refine ⟨?_, hEX hx⟩
    apply (projection_eq_one_iff h x).mpr
    intro u hu
    exact h.commutator_U_core_le_point
      (commutator_mem_commutator hu (h.U_le_core (show (x : G) ∈ D.U from hx.1)))

/-- G.2.2 kills the original two-core in the faithful action. -/
theorem core_le_projection_kernel (h : D.Hypothesis) :
    pCore 2 D.H ≤ (projection h).ker := by
  intro x hx
  apply (projection_eq_one_iff h x).mpr
  intro u hu
  exact h.commutator_U_core_le_point
    (commutator_mem_commutator hu (mem_map_of_mem D.H.subtype hx))

/-- The opposite image in the faithful action, with the same exact source index. -/
theorem binary_opposite_image (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    IsElementaryAbelian 2 E ∧ (D.S₂ g).relIndex D.U = 2 * Nat.card E := by
  have hUT := h.U_normal_in_T.1
  obtain ⟨hinter, hEE, _⟩ := Setup.binary_source_core_intersection_and_index h b hUT
    h.frattini_U_le_point h.U_le_core h.commutator_U_core_le_point g hgL hgN
  obtain ⟨helem, hindex⟩ := Setup.binary_source_opposite_image h b hUT
    h.frattini_U_le_point h.U_le_core h.commutator_U_core_le_point g hgL hgN
  let q := QuotientGroup.mk' (pCore 2 D.H)
  let B := (conjugate (D.W g) g).subgroupOf D.H
  have hcore (x : D.H) : x ∈ pCore 2 D.H ↔ (x : G) ∈ D.QH := by
    constructor
    · exact mem_map_of_mem D.H.subtype
    · rintro ⟨y,hy,he⟩
      exact (Subtype.ext he : y = x) ▸ hy
  have hcap : q.ker ⊓ B = (D.S₂ g).subgroupOf D.H := by
    ext x
    rw [QuotientGroup.ker_mk', mem_inf, hcore]
    change (x : G) ∈ D.QH ∧ (x : G) ∈ conjugate (D.W g) g ↔ (x : G) ∈ D.S₂ g
    rw [← hinter]
    exact and_comm
  have hc : Nat.card (B.map (projection h)) = Nat.card (B.map q) := by
    have hk : (projection h).ker ⊓ B = q.ker ⊓ B :=
      (binary_opposite_kernel h b g hgL hgN).trans hcap.symm
    have hi := congrArg (fun K : Subgroup D.H => K.relIndex B) hk
    simpa only [inf_relIndex_right, relIndex_ker] using hi
  let f : (D.H ⧸ pCore 2 D.H) →* Actor h :=
    QuotientGroup.lift (pCore 2 D.H) (projection h)
      (fun x hx => core_le_projection_kernel h hx)
  have hfac : f.comp q = projection h := by ext x; rfl
  have hel : IsElementaryAbelian 2 (B.map (projection h)) := by
    let : IsElementaryAbelian 2 (B.map q) := helem
    rw [← hfac, ← map_map]
    exact IsElementaryAbelian.map f
  refine ⟨hel, ?_⟩
  change (D.S₂ g).relIndex D.U = 2 * Nat.card (B.map (projection h))
  rw [hc]
  exact hindex

end SpanAction
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
