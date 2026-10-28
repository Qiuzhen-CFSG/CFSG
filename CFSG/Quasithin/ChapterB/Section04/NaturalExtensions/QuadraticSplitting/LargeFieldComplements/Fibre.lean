module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Displacement

/-!
# Zero-adjoined displacement fibres

The source fibre notation on printed pp.93–94 of Aschbacher–Smith B.4.9
omits zero. Here the fibre consists of all Levi-fixed vectors whose
axis-group displacements lie in a prescribed subspace, including zero.
This is a binary subspace. A linear section of its map onto the complementary
quotient line constructs a local complement to the original submodule.
No defining-field action on the extension is used.

The fibre-surjectivity premise is an explicit remaining source obligation;
this module proves the linear-algebra construction, not B.4.9 itself.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (K Q : Subgroup G)

/-- The zero-adjoined displacement fibre inside the Levi-fixed space. -/
def displacementFibre (W : Submodule (ZMod 2) V) : Submodule (ZMod 2) V where
  carrier := {v | v ∈ fixedSpace ρ K ∧ ∀ x : Q, ρ x v - v ∈ W}
  zero_mem' := ⟨(fixedSpace ρ K).zero_mem, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨(fixedSpace ρ K).add_mem hu hv, fun x => ?_⟩
    simpa only [map_add, add_sub_add_comm] using W.add_mem (hu' x) (hv' x)
  smul_mem' := by
    rintro c v ⟨hv, hv'⟩
    refine ⟨(fixedSpace ρ K).smul_mem c hv, fun x => ?_⟩
    simpa only [map_smul, smul_sub] using W.smul_mem c (hv' x)

theorem mem_displacementFibre (W : Submodule (ZMod 2) V) (v : V) :
    v ∈ displacementFibre ρ K Q W ↔
      v ∈ fixedSpace ρ K ∧ ∀ x : Q, ρ x v - v ∈ W := Iff.rfl

/-- A binary section through the displacement fibre gives the explicit local
complement W + range(t). This form permits additional torus invariance. -/
theorem fibreSection_complement
    (N : Subrepresentation ρ) (W : Submodule (ZMod 2) V)
    (I L : Submodule (ZMod 2) (V ⧸ N.toSubmodule))
    (hIL : IsCompl I L)
    (hWdis : Disjoint N.toSubmodule W)
    (hWI : W.map N.toSubmodule.mkQ = I)
    (hWK : K ≤ subspaceStabilizer ρ W)
    (hWQ : W ≤ fixedSpace ρ Q)
    (t : L →ₗ[ZMod 2] V)
    (ht : ∀ z : L, N.toSubmodule.mkQ (t z) = z)
    (htf : ∀ z : L, t z ∈ displacementFibre ρ K Q W) :
    IsCompl N.toSubmodule (W ⊔ LinearMap.range t) ∧
      K ⊔ Q ≤ subspaceStabilizer ρ (W ⊔ LinearMap.range t) := by
  let C := W ⊔ LinearMap.range t
  have hWsub : W ≤ C := le_sup_left
  have htsub (z : L) : t z ∈ C := Submodule.mem_sup_right ⟨z, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Submodule.disjoint_def.mpr
    intro v hNv hCv
    obtain ⟨w, hw, z, ⟨l, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hCv
    have hz : N.toSubmodule.mkQ w + (l : V ⧸ N.toSubmodule) = 0 := by
      have h : N.toSubmodule.mkQ (w + t l) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hNv
      simpa only [map_add, ht] using h
    have hl0 : (l : V ⧸ N.toSubmodule) = 0 := by
      apply Submodule.disjoint_def.mp hIL.disjoint _ ?_ l.property
      rw [eq_neg_of_add_eq_zero_right hz]
      apply I.neg_mem
      rw [← hWI]
      exact ⟨w, hw, rfl⟩
    have hl : l = 0 := Subtype.ext hl0
    subst l
    simp only [map_zero, add_zero] at hNv ⊢
    exact Submodule.disjoint_def.mp hWdis _ hNv hw
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    have hv : N.toSubmodule.mkQ v ∈ I ⊔ L := by
      rw [hIL.sup_eq_top]
      trivial
    obtain ⟨i, hi, l, hl, hv⟩ := Submodule.mem_sup.mp hv
    rw [← hWI] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    let z : L := ⟨l, hl⟩
    have hN : v - (w + t z) ∈ N.toSubmodule := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change N.toSubmodule.mkQ (v - (w + t z)) = 0
      rw [map_sub, map_add, ht]
      exact sub_eq_zero.mpr hv.symm
    exact Submodule.mem_sup.mpr ⟨_, hN, w + t z, C.add_mem (hWsub hw) (htsub z),
      sub_add_cancel _ _⟩
  · have hgen (g : G) (hW : ∀ w ∈ W, ρ g w ∈ W)
        (hT : ∀ z : L, ρ g (t z) ∈ C) :
        ∀ v ∈ C, ρ g v ∈ C := by
      intro v hv
      obtain ⟨w, hw, z, ⟨l, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact C.add_mem (hWsub (hW w hw)) (hT l)
    apply sup_le
    · apply le_subspaceStabilizer
      intro k hk
      apply hgen k
      · intro w hw
        exact (hWK hk w).mpr hw
      · intro z
        rw [show ρ k (t z) = t z from (htf z).1 ⟨k, hk⟩]
        exact htsub z
    · apply le_subspaceStabilizer
      intro q hq
      apply hgen q
      · intro w hw
        rw [show ρ q w = w from hWQ hw ⟨q, hq⟩]
        exact hw
      · intro z
        have hh := C.add_mem (hWsub ((htf z).2 ⟨q, hq⟩)) (htsub z)
        simpa only [sub_add_cancel] using hh


/-- Lifting into the fibre suffices: choose a binary linear section there. -/
theorem complement_of_fibre_covers
    (N : Subrepresentation ρ) (W : Submodule (ZMod 2) V)
    (I L : Submodule (ZMod 2) (V ⧸ N.toSubmodule))
    (hIL : IsCompl I L)
    (hWdis : Disjoint N.toSubmodule W)
    (hWI : W.map N.toSubmodule.mkQ = I)
    (hWK : K ≤ subspaceStabilizer ρ W)
    (hWQ : W ≤ fixedSpace ρ Q)
    (hlift : L ≤ (displacementFibre ρ K Q W).map N.toSubmodule.mkQ) :
    ∃ C : Submodule (ZMod 2) V, IsCompl N.toSubmodule C ∧
      K ⊔ Q ≤ subspaceStabilizer ρ C := by
  let E := displacementFibre ρ K Q W ⊓ L.comap N.toSubmodule.mkQ
  let p : E →ₗ[ZMod 2] L :=
    (N.toSubmodule.mkQ.comp E.subtype).codRestrict L (fun z => z.property.2)
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨v, hv, hvz⟩ := hlift z.property
    exact ⟨⟨v, hv, by change N.toSubmodule.mkQ v ∈ L; rw [hvz]; exact z.property⟩,
      Subtype.ext hvz⟩
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  let t : L →ₗ[ZMod 2] V := E.subtype.comp s
  have ht (z : L) : N.toSubmodule.mkQ (t z) = z := by
    exact congrArg Subtype.val (LinearMap.congr_fun hs z)
  have htf (z : L) : t z ∈ displacementFibre ρ K Q W := (s z).property.1
  exact ⟨W ⊔ LinearMap.range t,
    fibreSection_complement ρ K Q N W I L hIL hWdis hWI hWK hWQ t ht htf⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
