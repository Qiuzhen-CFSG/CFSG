module
public import Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.Defs
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.LinearAlgebra.BinaryTwoTransitivity
public import Theory.LinearAlgebra.FiniteSubspaceTransport
public import Theory.GroupTheory.Amalgam.UniquenessSystem.TriangleBase

/-!
# The projective-plane base in the degree-five binary model

The vertices are the nonzero vectors of the literal binary five-space, with
SL₅(2) acting through its usual matrix action. The marked plane is the span of
the first three coordinate vectors. Its stabilizer is transitive on ordered
pairs of distinct points in that plane, so its local edge orbit is a seven-point
clique. Extending injections of subspaces moves every triangle into this plane.
Together with triangle contraction in the complete graph, this proves the
nonabelian cycle-base condition.

`NativeSystem` specifies the actual graph, subgroup and distinguished edge;
its existence is proved in `UniquenessLinearSystem`. The base theorem here
does not assume triangle transitivity or the desired group isomorphism.
Source: Aschbacher, *Sporadic Groups* (1994), Example 38.4, pp.206–207,
and the linear branch of Lemma 41.5, p.222.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open BinaryLinear.TransvectionFiveLocal
abbrev Space := Fin 5 → ZMod 2
abbrev Point := {v : Space // v ≠ 0}
abbrev linearEquiv := BinaryLinear.OuterCyclic.slEquivLinear 5

instance : MulAction SL Point where
  smul g v := ⟨linearEquiv g v, fun h => v.property ((linearEquiv g).injective (h.trans (map_zero _).symm))⟩
  one_smul v := Subtype.ext (by change linearEquiv 1 v = v; rw [map_one]; rfl)
  mul_smul g h v := Subtype.ext (by change linearEquiv (g * h) v = linearEquiv g (linearEquiv h v); rw [map_mul]; rfl)

@[simp] theorem smul_val (g : SL) (v : Point) :
    (g • v : Point).val = linearEquiv g v := rfl

def planeSpace : Submodule (ZMod 2) Space :=
  Pi.spanSubset (ZMod 2) ({0, 1, 2} : Set (Fin 5))

theorem planeSpace_finrank : Module.finrank (ZMod 2) planeSpace = 3 := by
  rw [planeSpace, Pi.dim_spanSubset]
  have he : ({0, 1, 2} : Set (Fin 5)) = (({0, 1, 2} : Finset (Fin 5)) : Set (Fin 5)) := by simp
  rw [he, Set.ncard_coe_finset]
  decide

def basisPoint (i : Fin 5) : Point :=
  ⟨Pi.single i 1, by simp⟩

theorem basisPoint_mem_plane {i : Fin 5} (hi : i ∈ ({0, 1, 2} : Set (Fin 5))) :
    (basisPoint i : Space) ∈ planeSpace := by
  rw [planeSpace, Pi.mem_spanSubset_iff]
  intro j hj
  change (Pi.single i (1 : ZMod 2) : Space) j = 0
  simp [show j ≠ i from fun he => hj (he.symm ▸ hi)]

def planeGroup : Subgroup SL :=
  (BinaryLinear.parabolic planeSpace).comap linearEquiv.toMonoidHom

/-- The literal model data of Example 38.4. Existence is a separate theorem. -/
structure NativeSystem where
  system : GraphUniquenessSystem.System SL Point
  graph_eq : system.graph = ⊤
  local_eq : system.H = planeGroup
  point_eq : system.x = basisPoint 0
  neighbor_eq : system.y = basisPoint 1

theorem exists_plane_pair (a b : Point) (ha : a.val ∈ planeSpace)
    (hb : b.val ∈ planeSpace) (hab : a ≠ b) :
    ∃ h : planeGroup, (h : SL) • basisPoint 0 = a ∧ (h : SL) • basisPoint 1 = b := by
  let x : planeSpace := ⟨(basisPoint 0).val, basisPoint_mem_plane (by simp)⟩
  let y : planeSpace := ⟨(basisPoint 1).val, basisPoint_mem_plane (by simp)⟩
  let a' : planeSpace := ⟨a.val, ha⟩
  let b' : planeSpace := ⟨b.val, hb⟩
  have hx : x ≠ 0 := fun he => (basisPoint 0).property (congrArg Subtype.val he)
  have hy : y ≠ 0 := fun he => (basisPoint 1).property (congrArg Subtype.val he)
  have ha' : a' ≠ 0 := fun he => a.property (congrArg Subtype.val he)
  have hb' : b' ≠ 0 := fun he => b.property (congrArg Subtype.val he)
  have hxy : x ≠ y := by
    intro he
    have hh := congrArg (fun v : planeSpace => v.val 0) he
    norm_num [x, y, basisPoint] at hh
  have hab' : a' ≠ b' := fun he => hab (Subtype.ext (show a.val = b.val from congrArg (fun v : planeSpace => (v : Space)) he))
  obtain ⟨f, hfx, hfy⟩ := BinaryLinear.exists_linearEquiv_pair x y a' b'
    hx hy ha' hb' hxy hab'
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hgp : g ∈ BinaryLinear.parabolic planeSpace := by
    intro v
    constructor
    · intro hv
      let w := f.symm ⟨g v, hv⟩
      have hw : (w : Space) = v := g.injective ((hg w).symm.trans
        (congrArg Subtype.val (f.apply_symm_apply ⟨g v, hv⟩)))
      exact hw ▸ w.property
    · intro hv
      rw [← hg ⟨v, hv⟩]
      exact (f ⟨v, hv⟩).property
  let h : SL := linearEquiv.symm g
  have hh : h ∈ planeGroup := by
    change linearEquiv (linearEquiv.symm g) ∈ BinaryLinear.parabolic planeSpace
    simpa using hgp
  refine ⟨⟨h, hh⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · change linearEquiv (linearEquiv.symm g) x = a.val
    rw [linearEquiv.apply_symm_apply, ← hg x, hfx]
  · change linearEquiv (linearEquiv.symm g) y = b.val
    rw [linearEquiv.apply_symm_apply, ← hg y, hfy]

namespace NativeSystem
variable (N : NativeSystem)

theorem localEdge_iff (a b : Point) :
    N.system.localEdge a b ↔ a ≠ b ∧ a.val ∈ planeSpace ∧ b.val ∈ planeSpace := by
  have hx : N.system.x.val ∈ planeSpace := by
    rw [N.point_eq]; exact basisPoint_mem_plane (by simp)
  have hy : N.system.y.val ∈ planeSpace := by
    rw [N.neighbor_eq]; exact basisPoint_mem_plane (by simp)
  constructor
  · intro hab
    refine ⟨(N.system.localEdge_adj hab).ne, ?_⟩
    obtain ⟨h, he | he⟩ := hab
    all_goals
      have hh : (h : SL) ∈ planeGroup := N.local_eq ▸ h.property
      change ∀ v, linearEquiv h v ∈ planeSpace ↔ v ∈ planeSpace at hh
    · exact ⟨he.1 ▸ (hh _).mpr hx, he.2 ▸ (hh _).mpr hy⟩
    · exact ⟨he.2 ▸ (hh _).mpr hy, he.1 ▸ (hh _).mpr hx⟩
  · rintro ⟨hab, ha, hb⟩
    obtain ⟨h, hxa, hyb⟩ := exists_plane_pair a b ha hb hab
    refine ⟨⟨h, N.local_eq.symm ▸ h.property⟩, Or.inl ?_⟩
    simpa only [N.point_eq, N.neighbor_eq] using And.intro hxa hyb

private theorem complete_simplyConnected {V : Type*} :
    (⊤ : SimpleGraph V).TriangleSimplyConnected := by
  apply SimpleGraph.TriangleContractionData.simplyConnected
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    by_cases h : a = b
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro a b hab hn
    exact (hn hab).elim
  · intro a b v hab hva hvb hn
    exact (hn hva).elim

/-- Every model triangle fits inside a translate of the actual plane orbit. -/
theorem trianglesInLocalOrbits : N.system.TrianglesInLocalOrbits := by
  intro a b c hab hbc hca
  let s : Finset Space := {a.val, b.val, c.val}
  have hs : s.card ≤ Module.finrank (ZMod 2) planeSpace := by
    rw [planeSpace_finrank]
    exact (Finset.card_insert_le _ _).trans (by
      have := Finset.card_insert_le b.val {c.val}
      simp only [Finset.card_singleton] at this
      omega)
  obtain ⟨f, hf⟩ := planeSpace.exists_linearEquiv_finset_mem s hs
  let g : SL := (linearEquiv.symm f)⁻¹
  have hm (v : Point) (hv : v.val ∈ s) : (g⁻¹ • v : Point).val ∈ planeSpace := by
    change linearEquiv ((linearEquiv.symm f)⁻¹)⁻¹ v.val ∈ planeSpace
    rw [inv_inv, linearEquiv.apply_symm_apply]
    exact hf v.val hv
  have ha := hm a (by simp [s])
  have hb := hm b (by simp [s])
  have hc := hm c (by simp [s])
  refine ⟨g, (N.localEdge_iff _ _).mpr ⟨?_, ha, hb⟩,
    (N.localEdge_iff _ _).mpr ⟨?_, hb, hc⟩, (N.localEdge_iff _ _).mpr ⟨?_, hc, ha⟩⟩
  · exact fun he => hab.ne (MulAction.injective g⁻¹ he)
  · exact fun he => hbc.ne (MulAction.injective g⁻¹ he)
  · exact fun he => hca.ne (MulAction.injective g⁻¹ he)

/-- The source nonabelian cycle-base condition for the literal linear model. -/
theorem isBase : N.system.IsBase :=
  N.system.isBase_of_triangleSimplyConnected
    (by rw [N.graph_eq]; exact complete_simplyConnected) N.trianglesInLocalOrbits
end NativeSystem
end Theory.GroupTheory.TransvectionFive.UniquenessLinear
