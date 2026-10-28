module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.AdjointModel
public import Theory.Representation.PGroupHomDimension
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The SL₅ adjoint common-fixed-space estimate

Write c = dim C_V(B), u = dim[V,B], and r = log₂|B| for the natural
five-space. Distinct displacements give r ≤ u(5−c). The two modular
Hom-space bounds from Corollary 2.11(a) give
dim C_End(V)(B) ≤ 5 min(c,5−u). For 0 < r ≤ 6 these inequalities imply
2r + dim C_End(V)(B) < 25. The fixed scalar line splits off by trace, so
this is exactly 2r < fixedCodim on the 24-dimensional adjoint module.

This proves the concrete common-centralizer step of Guralnick–Malle,
Classification of 2F-modules II, author manuscript, Lemma 4.5 step 2,
pp.23–24. Cubicity is not needed for this binary degree-five specialization.
The final theorem transports the bound along an actual equivariant linear
equivalence; existence of that equivalence belongs to endpoint recognition.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Adjoint

/-- Both the natural fixed space and the natural coinvariants bound the
common matrix centralizer. -/
theorem centralizer_finrank_le (B : Subgroup Group) (hB : IsElementaryTwo B) :
    Module.finrank (ZMod 2) (centralizer B) ≤
      5 * min (Module.finrank (ZMod 2) (fixedNatural B))
        (5 - Module.finrank (ZMod 2) (movedNatural B)) := by
  let : IsElementaryAbelian 2 B := hB.2
  have hp : IsPGroup (ringChar (ZMod 2)) B := by
    rw [ringChar.eq (ZMod 2) 2]
    exact IsElementaryAbelian.isPGroup 2 B
  have hc : ringChar (ZMod 2) ≠ 0 := by rw [ringChar.eq (ZMod 2) 2]; decide
  have hn : Module.finrank (ZMod 2) Natural = 5 := by simp [Natural]
  let ρ : Representation (ZMod 2) B Natural := natural.comp B.subtype
  have hi := LinearMap.finrank_le_finrank_of_injective
    (f := centralizerHom B) (centralizerHom_injective B)
  have hleft := PGroupHomDimension.finrank_le ρ ρ hc hp
  have hright := PGroupHomDimension.finrank_le_dual ρ ρ hc hp
  have hd := (invariants ρ.dual).finrank_quotient_add_finrank
  rw [finrank_quotient_dual_invariants_eq_commutator,
    Subspace.dual_finrank_eq, hn] at hd
  have he : Module.finrank (ZMod 2) (invariants ρ.dual) =
      5 - Module.finrank (ZMod 2) (movedNatural B) := by
    change Module.finrank (ZMod 2) (movedNatural B) + _ = 5 at hd
    omega
  rw [hn] at hleft hright
  rw [he] at hright
  rw [mul_min]
  exact le_min (hi.trans hleft) (hi.trans hright)

private theorem dimension_arithmetic (c u r : ℕ) (hc : c ≤ 5) (hu : u ≤ 5)
    (hr : 0 < r) (hr6 : r ≤ 6) (hcu : r ≤ u * (5 - c)) :
    2 * r + 5 * min c (5 - u) < 25 := by
  interval_cases c <;> interval_cases u <;> norm_num at * <;> omega

/-- The rank-dependent adjoint estimate for every elementary binary actor
of rank at most six. -/
theorem strict_fixedCodim (B : Subgroup Group) (hB : IsElementaryTwo B)
    (hr : rank B ≤ 6) : 2 * rank B < fixedCodim action B := by
  have hc : Module.finrank (ZMod 2) (fixedNatural B) ≤ 5 := by
    simpa [Natural] using (fixedNatural B).finrank_le
  have hu : Module.finrank (ZMod 2) (movedNatural B) ≤ 5 := by
    simpa [Natural] using (movedNatural B).finrank_le
  have ha := dimension_arithmetic _ _ _ hc hu hB.rank_pos hr
    (rank_le_moved_mul_fixedCodim B)
  have hcentral := centralizer_finrank_le B hB
  have hdim := fixedCodim_add_finrank_centralizer B
  omega

/-- The estimate in the exact cubic-actor form used by the endpoint branch. -/
theorem strict_fixedCodim_of_cubic (B : Subgroup Group) (hB : IsElementaryTwo B)
    (_hCubic : IsCubic action B) (hr : rank B ≤ 6) :
    2 * rank B < fixedCodim action B := strict_fixedCodim B hB hr

/-- Application to an actual equivariant realization of the endpoint module.
The endpoint-recognition owner constructs the equivalence. -/
theorem strict_fixedCodim_of_equivariant
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (e : V ≃ₗ[ZMod 2] Space)
    (he : ∀ g v, e (σ g v) = action g (e v))
    (B : Subgroup Group) (hB : IsElementaryTwo B) (hr : rank B ≤ 6) :
    2 * rank B < fixedCodim σ B := by
  have h := fixedCodim_map_equivariant σ action (MonoidHom.id Group) e he B
  rw [Subgroup.map_id] at h
  rw [h]
  exact strict_fixedCodim B hB hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Adjoint
