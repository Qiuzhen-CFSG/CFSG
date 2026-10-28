module
public import CFSG.Quasithin.ChapterG.Section10.Basic
public import Theory.Representation.SymplecticOrbitCore

/-!
# G.10.3 on the original faithful action and its submodules

The odd point-centralizer index supplies an actual Sylow subgroup fixing the
marked vector. Its orbit spans V. Pairing against any invariant U transfers
that same orbit to U*, and faithfulness of the dual action excludes O₂ in
the actual action image on U.

Source: Aschbacher--Smith, G.10.3, printed p.357.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

omit [FiniteDimensional (ZMod 2) V] in
/-- The odd index is used to produce a Sylow of the original acting group. -/
theorem exists_sylow_fixes_point : ∃ S : Sylow 2 G, ∀ s : S, ρ s v = v := by
  let C := pointCentralizer ρ v
  let P : Sylow 2 C := Sylow.nonempty.some
  let Q := (P : Subgroup C).map C.subtype
  have hi : ¬ 2 ∣ Q.index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul (by decide : Nat.Prime 2) P.not_dvd_index h.odd_index.not_two_dvd_nat
  refine ⟨(P.isPGroup'.map C.subtype).toSylow hi, ?_⟩
  intro s
  obtain ⟨c, _, he⟩ := s.property
  exact he ▸ c.property

omit [FiniteDimensional (ZMod 2) V] in
/-- The faithful ambient actor has trivial two-core. -/
theorem twoCore_eq_bot : pCore 2 G = ⊥ := by
  obtain ⟨S, hS⟩ := h.exists_sylow_fixes_point
  apply twoCore_eq_bot_of_sylow_fixed_span ρ h.faithful S (Submodule.span (ZMod 2) {v})
  · apply Submodule.span_le.mpr
    rintro _ rfl s
    exact hS s
  · apply top_unique
    rw [← h.orbit_span]
    apply Submodule.span_mono
    rintro _ ⟨g, rfl⟩
    exact ⟨g, v, Submodule.mem_span_singleton_self _, rfl⟩

/-- G.10.3 for every actual invariant subspace. Its action image is exactly
G/C_G(U); the theorem also covers the zero subspace harmlessly. -/
theorem submodule_twoCore_eq_bot (U : Subrepresentation ρ) :
    pCore 2 (actionImage U.toRepresentation) = ⊥ := by
  obtain ⟨S, hS⟩ := h.exists_sylow_fixes_point
  exact submodule_actionImage_twoCore_eq_bot_of_sylow_fixed_orbit ρ B
    h.nondegenerate h.preserves S v hS h.orbit_span U

/-- The source quotient by the literal pointwise centralizer of U. -/
theorem submodule_quotient_twoCore_eq_bot (U : Subrepresentation ρ) :
    pCore 2 (G ⧸ U.toRepresentation.asGroupHom.ker) = ⊥ := by
  let e : (G ⧸ U.toRepresentation.asGroupHom.ker) ≃* actionImage U.toRepresentation :=
    QuotientGroup.quotientKerEquivRange U.toRepresentation.asGroupHom
  rw [← pCore_map_iso 2 e.symm, h.submodule_twoCore_eq_bot U, Subgroup.map_bot]


end CFSG.Quasithin.ChapterG.Section10.Hypothesis
