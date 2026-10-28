module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.DiagonalModel

/-!
# Norm images as relative centralizer components

The involution moves each B-conjugate of L, and the norm image on that
component is exactly the corresponding conjugate of the original norm image.
Every component of the orbit is normalized by the orbit: all other components
commute with it. Elements of C_E(a) therefore normalize its norm image.
Quasisimplicity and this relative normality place each image in the intrinsic
layer of C_E(a), proving D ≤ E(C_E(a)).

Source: GLS2, Chapter B, Lemma 3.27, first paragraph of the proof, and
Chapter G, Theorem 25.14, Step 2. No ambient normality of a component is assumed.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

private theorem conj_comm {a b : G} (hab : Commute a b) (x : G) :
    MulAut.conj a (MulAut.conj b x) = MulAut.conj b (MulAut.conj a x) := by
  change a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹
  calc
    _ = (a*b) * x * (a*b)⁻¹ := by group
    _ = (b*a) * x * (b*a)⁻¹ := by rw [hab.eq]
    _ = _ := by group

private theorem map_conj_comm (K : Subgroup G) {a b : G} (hab : Commute a b) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  exact conj_comm hab x

/-- The distinguished involution moves every component in the B-orbit. -/
theorem Hypotheses.conjugate_moved (h : Hypotheses ρ L B a) (b : B) :
    (L.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj a).toMonoidHom ≠
      L.map (MulAut.conj (b : G)).toMonoidHom := by
  have hab : Commute a (b : G) :=
    (mem_centralizer_singleton_iff.mp (h.fourGroup_le_centralizer b.property)).symm
  rw [map_conj_comm L hab]
  intro he
  exact h.moves ((map_injective (MulAut.conj (b : G)).injective) he)

/-- The norm image on a conjugate component is the literal conjugate of the
original norm image. -/
theorem Hypotheses.conjugate_norm_range (h : Hypotheses ρ L B a) (b : B) :
    (componentSwapNorm (h.component.map_conj (b : G)) (h.conjugate_moved b)).range =
      (componentSwapNorm h.component h.moves).range.map (MulAut.conj (b : G)).toMonoidHom := by
  have hab : Commute a (b : G) :=
    (mem_centralizer_singleton_iff.mp (h.fourGroup_le_centralizer b.property)).symm
  have he (x : G) :
      MulAut.conj (b : G) x * MulAut.conj a (MulAut.conj (b : G) x) =
        MulAut.conj (b : G) (x * MulAut.conj a x) := by
    rw [map_mul, conj_comm hab]
  apply le_antisymm
  · rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨componentSwapNorm h.component h.moves ⟨x,hx⟩, ⟨⟨x,hx⟩,rfl⟩, (he x).symm⟩
  · rintro _ ⟨_, ⟨x,rfl⟩, rfl⟩
    exact ⟨⟨_,mem_map_of_mem _ x.property⟩, he x⟩

/-- Every actual component norm belongs to the same orbit-generated diagonal. -/
theorem Hypotheses.conjugate_norm_mem (h : Hypotheses ρ L B a) (b : B)
    {x : G} (hx : x ∈ L.map (MulAut.conj (b : G)).toMonoidHom) :
    x * (a*x*a⁻¹) ∈ h.normDiagonal := by
  have he := h.conjugate_norm_range b
  have hx' : x * (a*x*a⁻¹) ∈
      (componentSwapNorm (h.component.map_conj (b : G)) (h.conjugate_moved b)).range :=
    ⟨⟨x,hx⟩,rfl⟩
  rw [he] at hx'
  exact (le_iSup (fun b : B =>
    (componentSwapNorm h.component h.moves).range.map (MulAut.conj (b : G)).toMonoidHom) b) hx'

private theorem orbit_le_normalizer_component (hL : IsComponent G L)
    {K : Subgroup G} (hK : IsComponent G K) :
    componentOrbit L B ≤ normalizer (K : Set G) := by
  apply iSup_le
  intro b
  by_cases he : L.map (MulAut.conj (b : G)).toMonoidHom = K
  · rw [he]
    exact K.le_normalizer
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      ((hL.map_conj (b : G)).commutator_eq_bot_of_ne hK he)).trans
      (centralizer_le_normalizer _)

private theorem norm_range_normalized {K C : Subgroup G} (hK : IsComponent G K)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K)
    (hCK : C ≤ normalizer (K : Set G)) (hCa : C ≤ centralizer ({a} : Set G)) :
    C ≤ normalizer ((componentSwapNorm hK hm).range : Set G) := by
  apply le_normalizer_iff.mpr
  rintro c hc _ ⟨x,rfl⟩
  have hcx : c * (x : G) * c⁻¹ ∈ K := (mem_normalizer_iff.mp (hCK hc) x).mp x.property
  refine ⟨⟨_,hcx⟩, ?_⟩
  have hca : Commute a c := (mem_centralizer_singleton_iff.mp (hCa hc)).symm
  change MulAut.conj c x * MulAut.conj a (MulAut.conj c x) =
    MulAut.conj c ((x : G) * MulAut.conj a x)
  rw [map_mul, conj_comm hca]

/-- Each norm image is normal and quasisimple inside the literal centralizer.
This is relative normality, not normality in the ambient group. -/
theorem Hypotheses.conjugate_norm_isComponent (h : Hypotheses ρ L B a) (b : B) :
    IsComponent (orbitCentralizer L B a)
      ((componentSwapNorm (h.component.map_conj (b : G)) (h.conjugate_moved b)).range.subgroupOf
        (orbitCentralizer L B a)) := by
  let N := (componentSwapNorm (h.component.map_conj (b : G)) (h.conjugate_moved b)).range
  have hNC : N ≤ orbitCentralizer L B a := by
    intro x hx
    apply h.normDiagonal_le_orbitCentralizer
    dsimp only [N] at hx
    rw [h.conjugate_norm_range b] at hx
    exact (le_iSup (fun b : B =>
      (componentSwapNorm h.component h.moves).range.map (MulAut.conj (b : G)).toMonoidHom) b) hx
  have hn : (N.subgroupOf (orbitCentralizer L B a)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNC).mpr
      (norm_range_normalized (h.component.map_conj (b : G)) (h.conjugate_moved b)
        (inf_le_left.trans (orbit_le_normalizer_component h.component (h.component.map_conj (b : G))))
        inf_le_right)
  let := componentSwapNorm_range_quasisimple (h.component.map_conj (b : G)) (h.conjugate_moved b)
  exact ⟨hn.isSubnormal, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hNC).symm⟩

/-- The explicit norm diagonal lies in the actual intrinsic centralizer layer. -/
theorem Hypotheses.normDiagonal_le_diagonalLayer (h : Hypotheses ρ L B a) :
    h.normDiagonal ≤ diagonalLayer L B a := by
  apply iSup_le
  intro b
  rw [← h.conjugate_norm_range b]
  let N := (componentSwapNorm (h.component.map_conj (b : G)) (h.conjugate_moved b)).range
  have hNC : N ≤ orbitCentralizer L B a := by
    intro x hx
    apply h.normDiagonal_le_orbitCentralizer
    dsimp only [N] at hx
    rw [h.conjugate_norm_range b] at hx
    exact (le_iSup (fun b : B =>
      (componentSwapNorm h.component h.moves).range.map (MulAut.conj (b : G)).toMonoidHom) b) hx
  have hi : N.subgroupOf (orbitCentralizer L B a) ≤ componentLayer (orbitCentralizer L B a) :=
    le_sSup (h.conjugate_norm_isComponent b)
  have := map_mono (f := (orbitCentralizer L B a).subtype) hi
  rwa [map_subgroupOf_eq_of_le hNC] at this

end Representation.QuadraticFourGroup

end
