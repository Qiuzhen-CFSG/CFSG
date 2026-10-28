module

public import Theory.Representation.HexacodeAction.WeightFourVectorResidual
public import Theory.Representation.BinaryOffender.CubicQuotient

/-!
# Binary quotient ranks at a weight-four scalar point

The actual vector-stabilizer residual contains a single cubic whose
displacements generate the quotient by the scalar point. Every invariant
quotient killing that point therefore has a surjective displacement map.
In finite dimension this map is injective, so the cubic has no nonzero
fixed vector and the quotient dimension is even. Killing the binary
two-dimensional point bounds that dimension by four.

Source: Aschbacher--Smith12.7.15(4), printed p.843. The specified hexacode
point and the literal two-residual action are retained throughout.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender

/-- Every quotient killing the weight-four scalar point and invariant
under the actual vector-stabilizer two-residual has even binary dimension. -/
theorem weightFourResidualQuotient_finrank_even (v : hexacode)
    (hv : hammingNorm v.val=4) (E : Submodule Bit hexacode)
    (hPE : (Submodule.span F {v}).restrictScalars Bit ≤ E)
    (hE : ((pResidual 2 (fullWeightVectorStabilizer v)).map
      (fullWeightVectorStabilizer v).subtype) ≤ subspaceStabilizer evenAction E) :
    Even (Module.finrank Bit (hexacode ⧸ E)) := by
  let R := (pResidual 2 (fullWeightVectorStabilizer v)).map
    (fullWeightVectorStabilizer v).subtype
  let ρ := evenAction.comp R.subtype
  let N : Subrepresentation ρ := {
    toSubmodule := E
    apply_mem_toSubmodule := fun g w hw => (hE g.property w).mpr hw }
  let σ := N.quotientRepresentation
  obtain ⟨g,hg,hg3,hd⟩ := weightFourVector_cubic_displacement v hv
  have hgr : g ∈ R := by
    apply mem_map_of_mem (fullWeightVectorStabilizer v).subtype
      (x := (⟨g,hg⟩ : fullWeightVectorStabilizer v))
    apply mem_pResidual_of_orderOf_coprime
    apply (by decide : Nat.Coprime 2 3).of_dvd_right
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (show g^3=1 from hg3)
  let r : R := ⟨g,hgr⟩
  have hr3 : r^3=1 := Subtype.ext hg3
  let δ : Module.End Bit (hexacode ⧸ E) := σ r-1
  have hδ : Function.Surjective δ := by
    intro w
    obtain ⟨x,rfl⟩ := E.mkQ_surjective w
    obtain ⟨y,c,hy⟩ := hd x
    refine ⟨E.mkQ y,?_⟩
    change E.mkQ (evenAction g y)-E.mkQ y=E.mkQ x
    rw [←map_sub,hy,map_add]
    have hc : E.mkQ (c•v)=0 :=
      (Submodule.Quotient.mk_eq_zero E).mpr
        (hPE (Submodule.mem_span_singleton.mpr ⟨c,rfl⟩))
    rw [hc,add_zero]
  have hδinj : Function.Injective δ := LinearMap.injective_iff_surjective.mpr hδ
  have hfix (w : hexacode ⧸ E) (hw : σ r w=w) : w=0 := by
    apply hδinj
    change σ r w-w=σ r 0-0
    rw [hw,map_zero,sub_self,sub_zero]
  exact even_finrank_of_fixedFree_cubic_quotient σ σ (Representation.IntertwiningMap.id σ)
    (fun w => ⟨w,rfl⟩) r hr3 hfix

/-- A nonzero quotient by a residual-invariant binary subspace containing
the same scalar point has rank two or four. -/
theorem weightFourResidualQuotient_finrank_two_or_four (v : hexacode)
    (hv : hammingNorm v.val=4) (E : Submodule Bit hexacode)
    (hPE : (Submodule.span F {v}).restrictScalars Bit ≤ E)
    (hE : ((pResidual 2 (fullWeightVectorStabilizer v)).map
      (fullWeightVectorStabilizer v).subtype) ≤ subspaceStabilizer evenAction E)
    (hne : E≠⊤) :
    Module.finrank Bit (hexacode ⧸ E)=2 ∨ Module.finrank Bit (hexacode ⧸ E)=4 := by
  have hv0 : v≠0 := by intro h; simp [h] at hv
  have hp := fieldPoint_binary_finrank (Submodule.span F {v}) (finrank_span_singleton hv0)
  have hdim := Submodule.finrank_mono hPE
  rw [hp] at hdim
  have hsum := E.finrank_quotient_add_finrank
  rw [hexacode_finrank] at hsum
  have hzero : Module.finrank Bit (hexacode ⧸ E)≠0 := by
    intro h0
    apply hne
    apply Submodule.eq_top_of_finrank_eq
    rw [hexacode_finrank]
    omega
  obtain ⟨n,hn⟩ := weightFourResidualQuotient_finrank_even v hv E hPE hE
  omega

/-- Full vector-stabilizer invariance also forces even quotient dimension. -/
theorem weightFourQuotient_finrank_even (v : hexacode)
    (hv : hammingNorm v.val=4) (E : Submodule Bit hexacode)
    (hPE : (Submodule.span F {v}).restrictScalars Bit ≤ E)
    (hE : fullWeightVectorStabilizer v ≤ subspaceStabilizer evenAction E) :
    Even (Module.finrank Bit (hexacode ⧸ E)) :=
  weightFourResidualQuotient_finrank_even v hv E hPE ((map_subtype_le _).trans hE)

/-- The nonzero binary quotient by a vector-stabilizer invariant subspace
containing its scalar point has exactly rank two or four. -/
theorem weightFourQuotient_finrank_two_or_four (v : hexacode)
    (hv : hammingNorm v.val=4) (E : Submodule Bit hexacode)
    (hPE : (Submodule.span F {v}).restrictScalars Bit ≤ E)
    (hE : fullWeightVectorStabilizer v ≤ subspaceStabilizer evenAction E)
    (hne : E≠⊤) :
    Module.finrank Bit (hexacode ⧸ E)=2 ∨ Module.finrank Bit (hexacode ⧸ E)=4 :=
  weightFourResidualQuotient_finrank_two_or_four v hv E hPE ((map_subtype_le _).trans hE) hne

end Representation.Hexacode
