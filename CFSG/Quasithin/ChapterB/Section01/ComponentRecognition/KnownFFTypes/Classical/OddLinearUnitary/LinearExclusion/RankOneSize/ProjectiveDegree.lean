module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.RankOne
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.FrobeniusExclusions
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The binary projective-degree bound on the actual central cover

A faithful irreducible binary action makes the component's two-core trivial.
For odd q > 3 other than nine, the proved universal SL₂ cover then identifies
the original component with PSL₂(q). The actual projective Borel has abelian
odd kernel of order q and a complement of order (q - 1)/2 acting freely on
its nonzero elements. Its nontrivial weights give the same lower bound for
the binary degree, without absolute irreducibility or a scalar-field change.

This discharges the degree input in RankOneSize.Reduction for every requested
q > 25. The normalizer's SQTK status and a choice of constituent over a larger
coefficient field are not needed.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript p.8; Aschbacher--Smith K.2, printed p.453. The Borel-weight bound
was proved for G.7.2, and the cover comparison for I.1.3(1),(3).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- The literal source component has trivial two-core by modular irreducibility. -/
theorem source_component_twoCore_eq_bot : pCore 2 (generalizedFitting G) = ⊥ := by
  let σ := ρ.comp (generalizedFitting G).subtype
  let : IsIrreducible σ := h.irreducible
  have hf : Function.Injective σ := h.faithful.comp Subtype.val_injective
  have hk := normal_p_subgroup_le_ker σ (pCore 2 (generalizedFitting G))
    (pCore_isPGroup (p := 2))
  exact bot_unique (hk.trans ((MonoidHom.ker_eq_bot_iff σ).mpr hf).le)

/-- The actual covering group is PSL₂(q) outside the exceptional parameter nine. -/
theorem source_component_isPSL {q : ℕ} (hq : 3 < q) (ho : Odd q) (h9 : q ≠ 9)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q) :
    ClassicalGroup.IsPSL (generalizedFitting G) 2 q := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  exact isPSL_of_odd_rank_one (source_component_twoCore_eq_bot ρ h) hq ho h9 hm

/-- The Borel weight orbit gives the degree minimum on the original binary space. -/
theorem source_projective_degree {q : ℕ} (hq : 3 < q) (ho : Odd q) (h9 : q ≠ 9)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q) :
    q - 1 ≤ 2 * Module.finrank (ZMod 2) V := by
  have hd := CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.psl2_frobenius_degree_bound
    (ρ.comp (generalizedFitting G).subtype) (h.faithful.comp Subtype.val_injective)
    ho (source_component_isPSL ρ h hq ho h9 hm)
  obtain ⟨k, hk⟩ := ho
  omega

omit h ρ in
/-- The independent projective-degree premise of the rank-one size reduction is proved. -/
theorem projectiveDegreeBound : ProjectiveDegreeBound.{u, v} := by
  intro G V _ _ _ _ _ ρ h p e _ ho _ hlarge hm
  exact source_projective_degree ρ h (by omega) (ho.pow (n := e)) (by omega) hm

/-- Only the independent concrete generation calculation remains in the source
field-order bound; the projective degree premise is discharged here. -/
theorem source_field_order_le_twentyFive_of_generation
    (hgenerators : SourceGenerationBounds.{u, v})
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlo : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (hq : cubicRatio ρ ≤ 2) : p ^ e ≤ 25 :=
  source_field_order_le_twentyFive_of_bounds ρ h projectiveDegreeBound
    hgenerators hp ho he hlo hm hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
