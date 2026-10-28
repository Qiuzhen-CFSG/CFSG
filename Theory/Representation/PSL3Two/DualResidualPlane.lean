module
public import Theory.Representation.PSL3.PointParabolicCoinvariants
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The moving dual plane of the binary point residual

The actual two-residual of the standard point parabolic acts on its dual
three-space with moved space the annihilator plane. A cubic and its inverse
show that the differences of each nonzero vector of this plane generate it.
The literal conjugation-section consumer retains the residual map and the
commutators of the original seed, rather than the whole dual support.

Source: Aschbacher--Smith, the last paragraph on printed p.1042.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Matrix
open scoped commutatorElement
namespace Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents

theorem dual_plane_card : Nat.card annihilator.toSubmodule = 4 := by
  rw [← Nat.card_congr dualPlaneEquiv.toEquiv]
  simp [W, K]

theorem dual_seed_generates (C : AddSubgroup V) (b : V)
    (hb : b 0 = 0) (hb0 : b ≠ 0)
    (hc : ∀ a : pointA, dual a b - b ∈ C) :
    ∀ v : V, v 0 = 0 → v ∈ C := by
  have hspan : ∀ b : V, b 0 = 0 → b ≠ 0 → ∀ v : V, v 0 = 0 →
      v = 0 ∨ v = dual ⟨cubic,cubic_mem⟩ b - b ∨
      v = dual ⟨cubic,cubic_mem⟩⁻¹ b - b ∨
      v = (dual ⟨cubic,cubic_mem⟩ b - b) + (dual ⟨cubic,cubic_mem⟩⁻¹ b - b) := by
    decide +kernel
  intro v hv
  rcases hspan b hb hb0 v hv with rfl | rfl | rfl | rfl
  · exact C.zero_mem
  · exact hc _
  · exact hc _
  · exact C.add_mem (hc _) (hc _)

theorem dual_moved_eq_plane :
    subspaceCommutator dual ⊤ (⊤ : Subgroup pointA) = annihilator.toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,_,v,_,rfl⟩
    change first (dual a v - v) = 0
    rw [map_sub, first_dual, sub_self]
  · intro v hv
    exact Matrix.PSL3.PointParabolicCoinvariants.binary_dual_planes_mem
      (ι := Unit) ((subspaceCommutator dual ⊤ (⊤ : Subgroup pointA)).toAddSubgroup.comap
        (Pi.evalAddMonoidHom (fun _ : Unit => V) ()))
      (fun a w => Submodule.subset_span ⟨a,trivial,w (),trivial,rfl⟩)
      (fun _ => v) (fun _ => hv)

variable {G : Type*} [Group G] [Finite G] {P B Z : Subgroup G}

abbrev fullDual : Representation K SL V :=
  (specialLinearNatural 3).comp inverseTranspose.toMonoidHom

theorem residual_image (f : P →* SL) (hf : f.range = pointParabolicSL) :
    (pResidual 2 P).map f = pointA := by
  have hm := map_embedded_pResidual 2 (⊤ : Subgroup P) f
  rw [← MonoidHom.range_eq_map, hf, ← residual, point_residual] at hm
  have ht : (pResidual 2 (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype = pResidual 2 P :=
    map_pResidual_of_surjective 2 _ (by intro x; exact ⟨⟨x,trivial⟩,rfl⟩)
  rwa [ht] at hm

theorem dual_section_image (f : P →* SL) (hf : f.range = pointParabolicSL)
    (d : BinaryConjugationSection P B Z (fullDual.comp f)) :
    d.imageSpace ⁅B,(pResidual 2 P).map P.subtype⁆ = annihilator.toSubmodule := by
  have htop : d.imageSpace B = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨b,hb⟩ := d.onto (Multiplicative.ofAdd v)
    exact (d.mem_imageSpace_iff B v).mpr ⟨b,b.property,congrArg Multiplicative.toAdd hb⟩
  have hsub : ((pResidual 2 P).map P.subtype).subgroupOf P = pResidual 2 P := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      exact (P.subtype_injective he) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  rw [commutator_comm B, d.imageSpace_commutator _ B (map_subtype_le _) le_rfl,
    htop,hsub,subspaceCommutator_comp_map, residual_image f hf]
  have hh := subspaceCommutator_comp_map fullDual pointA.subtype ⊤ (⊤ : Subgroup pointA)
  rw [← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh.symm.trans dual_moved_eq_plane

theorem dual_section_seed_generates (f : P →* SL) (hf : f.range = pointParabolicSL)
    (d : BinaryConjugationSection P B Z (fullDual.comp f))
    (b : B) (hb : (d.coordinates b).toAdd 0 = 0) (hb0 : d.coordinates b ≠ 1) :
    d.imageSpace ⁅B,(pResidual 2 P).map P.subtype⁆ ≤
      d.imageSpace (closure {x : G | ∃ r ∈ (pResidual 2 P).map P.subtype, x = ⁅(b : G),r⁆}) := by
  rw [dual_section_image f hf d]
  let C := closure {x : G | ∃ r ∈ (pResidual 2 P).map P.subtype, x = ⁅(b : G),r⁆}
  apply dual_seed_generates (d.imageSpace C).toAddSubgroup (d.coordinates b).toAdd hb hb0
  intro a
  obtain ⟨r,hr,he⟩ := (show a.val ∈ (pResidual 2 P).map f by
    rw [residual_image f hf]; exact a.property)
  let rb : B := ⟨(r : G)*b*(r : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized r.property) b).mp b.property⟩
  have hm : (↑(rb*b⁻¹) : G) ∈ C := by
    have hh : ⁅(b : G),(r : G)⁆ ∈ C := subset_closure ⟨r,⟨r,hr,rfl⟩,rfl⟩
    change ⁅(r : G),(b : G)⁆ ∈ C
    simpa only [commutatorElement_inv] using C.inv_mem hh
  apply (d.mem_imageSpace_iff C _).mpr
  refine ⟨rb*b⁻¹,hm,?_⟩
  rw [map_mul,map_inv]
  change (d.coordinates rb).toAdd + -(d.coordinates b).toAdd = _
  rw [d.equivariant]
  change fullDual (f r) _ + -_ = _
  rw [he]
  exact (sub_eq_add_neg _ _).symm

end Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
