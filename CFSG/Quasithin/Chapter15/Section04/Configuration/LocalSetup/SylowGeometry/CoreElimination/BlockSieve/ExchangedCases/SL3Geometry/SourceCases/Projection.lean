module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives

/-! # The natural projection in C.1.34(4)
The direct sum Z(Q)=C_Q(L)⊕U gives an actual quotient isomorphism
Z(Q)/C_Q(L)≃U. Its conjugation compatibility follows by writing an element
as u c: L fixes c and preserves U. This constructs the projection and does
not assume a section witness. Source: C.1.34(4), printed p.136.
-/

@[expose] public section
open Subgroup Representation CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

variable {D F T V : Type*} [Group D] [Field F] [Group T] [AddCommGroup V] [Module F V]

/-- A layer with trivial lower subgroup identifies the whole upper subgroup. -/
noncomputable def LayerModel.upperIso {L U : Subgroup D}
    {e : (L ⧸ pCore 2 L) ≃* T} {ρ : Representation F T V}
    (m : LayerModel L U ⊥ e ρ) : U ≃* Multiplicative V := by
  letI := m.lower_normal
  exact ((QuotientGroup.quotientBot (G := U)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf U).symm)).trans m.quotientIso

/-- Its action remains the literal conjugation action. -/
theorem LayerModel.upperIso_intertwining {L U : Subgroup D}
    {e : (L ⧸ pCore 2 L) ≃* T} {ρ : Representation F T V}
    (m : LayerModel L U ⊥ e ρ) (l : L) (u : U) :
    Multiplicative.toAdd (m.upperIso (layerConjugate L U m.normalized l u)) =
      ρ (e (QuotientGroup.mk' _ l)) (Multiplicative.toAdd (m.upperIso u)) :=
  m.intertwining l u

/-- Project a direct sum with a fixed summand onto its natural summand. -/
noncomputable def LayerModel.projectDirectSum
    {L Z U C : Subgroup D} [IsMulCommutative Z]
    {e : (L ⧸ pCore 2 L) ≃* T} {ρ : Representation F T V}
    (m : LayerModel L U ⊥ e ρ) (hUZ : U ≤ Z) (hCZ : C ≤ Z)
    (hn : L ≤ normalizer (Z : Set D)) (hc : C ≤ centralizer (L : Set D))
    (hs : (U.subgroupOf Z).IsComplement' (C.subgroupOf Z)) :
    LayerModel L Z C e ρ := by
  letI : (C.subgroupOf Z).Normal := inferInstance
  let q := QuotientGroup.mk' (C.subgroupOf Z)
  let e₁ := hs.QuotientMulEquiv
  let e₂ := subgroupOfEquivOfLe hUZ
  let e₃ := e₁.trans (e₂.trans m.upperIso)
  refine {
    lower_le := hCZ
    normalized := hn
    lower_normal := inferInstance
    quotientIso := e₃
    intertwining := ?_ }
  have hu : ∀ u : U.subgroupOf Z, e₁ (q (u : Z)) = u := fun u => e₁.apply_symm_apply u
  have hcq : ∀ c : C.subgroupOf Z, q (c : Z) = 1 :=
    fun c => (QuotientGroup.eq_one_iff (N := C.subgroupOf Z) (c : Z)).mpr c.property
  intro l z
  obtain ⟨⟨u, c⟩, hz⟩ := hs.2 z
  have hz' : (u : Z) * (c : Z) = z := hz
  let lu : U := layerConjugate L U m.normalized l (e₂ u)
  let lu' : U.subgroupOf Z := ⟨⟨lu, hUZ lu.property⟩, lu.property⟩
  have hconj : layerConjugate L Z hn l z = (lu' : Z) * (c : Z) := by
    apply Subtype.ext
    have he : (u.val : D) * (c.val : D) = (z : D) := congrArg Subtype.val hz'
    change (l : D) * (z : D) * (l : D)⁻¹ =
      ((l : D) * (u.val : D) * (l : D)⁻¹) * (c.val : D)
    rw [← he]
    have hcomm := mem_centralizer_iff.mp (hc c.property) l l.property
    calc
      (l : D) * ((u.val : D) * (c.val : D)) * (l : D)⁻¹ =
          (l : D) * (u.val : D) * ((c.val : D) * (l : D)⁻¹) := by group
      _ = (l : D) * (u.val : D) * ((l : D)⁻¹ * (c.val : D)) := by
        rw [show (c.val : D) * (l : D)⁻¹ = (l : D)⁻¹ * (c.val : D) by
          exact (Commute.symm hcomm).inv_right.eq]
      _ = _ := by group
  change Multiplicative.toAdd (m.upperIso (e₂ (e₁ (q (layerConjugate L Z hn l z))))) =
    ρ (e (QuotientGroup.mk' _ l)) (Multiplicative.toAdd (m.upperIso (e₂ (e₁ (q z)))))
  rw [hconj, map_mul, hcq, mul_one, hu, ← hz', map_mul, hcq, mul_one, hu]
  exact m.upperIso_intertwining l (e₂ u)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
