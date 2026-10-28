module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeQuotient
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.TransvectionCommutator
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.GroupTheory.SylowKernelCore

/-!
# Crossing a neighboring symplectic parabolic core

Let E lie in a Sylow-normal subgroup T, with T normalizing E. If E has at
least q squared elements and escapes the plane radical, failure to cross
the two-core at the other point of the plane forces T to be the whole
point radical. Squares first put E in the point radical; commutators put
T there too. The two remaining coordinates then biject E with F squared.
Normality of T recovers its missing central coordinate.

The final statement uses the literal plane and point-parabolic two-cores.
The replacement-graph consumer excludes the point-radical alternative by
transporting the complete small-mover family through the full Q-kernel.
Source: MS93 (5.5), the crossing argument on printed p.916. Compatible
endpoint/path selection and the generation split are separate obligations.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.NeighborMoverCrossing
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem point_of_no_crossing
    (T E : Subgroup (unipotent (F := F))) [T.Normal]
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set (unipotent (F := F))))
    (hc : Nat.card F^2 ≤ Nat.card E) (hout : ¬ E ≤ wing true)
    (hzero : ∀ u w v : F, element 0 u w v ∈ E → u=0) :
    T = wing false := by
  obtain ⟨x,hx,hxp⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b≠0 := by simpa only [element_mem_wing,↓reduceIte] using hxp
  have all_v {c z t a : F} (hy : element c z t a ∈ E) (hc : c≠0) : a=0 := by
    have hs := E.pow_mem hy 2
    rw [element_square] at hs
    have hh := hzero _ _ _ hs
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hc)
  have hv : v=0 := all_v hx hb
  subst v
  have hEv {c z t a : F} (hy : element c z t a ∈ E) : a=0 := by
    by_cases hc : c=0
    · subst c
      have hm := E.mul_mem hx hy
      rw [element_mul] at hm
      simp only [add_zero,zero_add,mul_zero] at hm
      exact all_v hm hb
    · exact all_v hy hc
  have hTv {c z t a : F} (hy : element c z t a ∈ T) : a=0 := by
    have hm := (le_normalizer_iff_commutator_le_left.mp hTE)
      (commutator_mem_commutator hx hy)
    rw [element_commutator] at hm
    have hh := hzero _ _ _ hm
    simp only [mul_zero,zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hb)
  have hTP : T ≤ wing false := by
    intro y hy
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
    exact (element_mem_wing false _ _ _ _).mpr (hTv hy)
  let f : E → F × F := fun y =>
    (y.val.val.val (.inl 0) (.inl 1),y.val.val.val (.inl 1) (.inr 0))
  have hfi : Function.Injective f := by
    intro y z he
    obtain ⟨⟨c,s,t,a⟩,hy⟩ := element_surjective y.val
    obtain ⟨⟨c',s',t',a'⟩,hz⟩ := element_surjective z.val
    change element c s t a = y.val at hy
    change element c' s' t' a' = z.val at hz
    have hyE : element c s t a ∈ E := by rw [hy]; exact y.property
    have hzE : element c' s' t' a' ∈ E := by rw [hz]; exact z.property
    have ha := hEv hyE
    have ha' := hEv hzE
    subst a a'
    change (_,_) = (_,_) at he
    simp only [←hy,←hz,element_matrix,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Fin.isValue] at he
    have hc' : c=c' := congrArg Prod.fst he
    have ht' : t=t' := congrArg Prod.snd he
    subst c' t'
    have hm := E.mul_mem hyE hzE
    have hp : element c s t 0 * element c s' t 0 = theta (s+s') 0 := by
      rw [element_mul,theta,element_eq_iff]
      simp [CharTwo.add_self_eq_zero,mul_comm,add_assoc]
    rw [hp] at hm
    have hs : s=s' := CharTwo.add_eq_zero.mp (hzero _ _ _ hm)
    apply Subtype.ext
    rw [←hy,←hz,hs]
  have hfs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,
      le_antisymm (Nat.card_le_card_of_injective f hfi)
        (by simpa only [Nat.card_prod,pow_two] using hc)⟩).surjective
  have hcoords (c t : F) : ∃ s : F, element c s t 0 ∈ E := by
    obtain ⟨y,hy⟩ := hfs (c,t)
    obtain ⟨⟨c',s,t',a⟩,he⟩ := element_surjective y.val
    change element c' s t' a = y.val at he
    have hmem : element c' s t' a ∈ E := by rw [he]; exact y.property
    have ha := hEv hmem
    subst a
    change (_,_) = (_,_) at hy
    simp only [←he,element_matrix,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Fin.isValue] at hy
    have hc' : c'=c := congrArg Prod.fst hy
    have ht' : t'=t := congrArg Prod.snd hy
    subst c' t'
    exact ⟨s,hmem⟩
  have hshort (t : F) : theta 0 t ∈ E := by
    obtain ⟨s,hs⟩ := hcoords 0 t
    have he := hzero s t 0 hs
    change element 0 0 t 0 ∈ E
    simpa only [he] using hs
  obtain ⟨s,hs⟩ := hcoords 1 0
  have hlong (a : F) : theta a 0 ∈ T := by
    have hm := (commutator_le_left T ⊤)
      (commutator_mem_commutator (hET hs) (mem_top (element 0 0 0 a)))
    rw [element_commutator] at hm
    simp only [zero_pow (by decide : 2≠0),mul_zero,zero_add,one_pow,one_mul] at hm
    have hh := T.mul_mem hm (hET (hshort a))
    simpa only [theta_add,add_zero,CharTwo.add_self_eq_zero] using hh
  apply le_antisymm hTP
  intro y hy
  obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
  have ha : a=0 := (element_mem_wing false _ _ _ _).mp hy
  subst a
  obtain ⟨s,hs⟩ := hcoords c t
  have hm := T.mul_mem (hET hs) (hlong (z+s))
  simpa [theta,element_mul,add_assoc,add_left_comm,CharTwo.add_self_eq_zero] using hm

/-- A large neighboring mover crosses the other point's core, unless its
normalizing edge is the entire point radical. Only T is Sylow-normal. -/
theorem crossing_or_point
    (T E : Subgroup (unipotent (F := F))) [T.Normal]
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set (unipotent (F := F))))
    (hc : Nat.card F^2 ≤ Nat.card E) (hout : ¬ E ≤ wing true) :
    (∃ u w v : F, u≠0 ∧ element 0 u w v ∈ E) ∨ T = wing false := by
  by_cases he : ∃ u w v : F, u≠0 ∧ element 0 u w v ∈ E
  · exact Or.inl he
  right
  apply point_of_no_crossing T E hET hTE hc hout
  intro u w v hu
  by_contra hn
  exact he ⟨u,w,v,hn,hu⟩

end Theory.SpecificGroups.SymplecticFour.NeighborMoverCrossing

namespace Theory.SpecificGroups.SymplecticFour.NeighborMoverCrossing
open CentralRootGeometry Matrix Theory.GroupTheory
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
private def swap : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1

omit [Finite F] in
private theorem swap_matrix : (swap (F := F)).val =
    fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0] := by
  change rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem swap_square : swap (F := F) * swap = 1 := by
  apply Subtype.ext
  change (swap (F := F)).val * swap.val = 1
  rw [swap_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]

omit [Finite F] in
private theorem swap_shear (u w v : F) :
    swap * (element 0 u w v).val * swap⁻¹ = (element 0 v w u).val := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (swap (F := F)).val * (element 0 u w v).val.val =
    (element 0 v w u).val.val * swap.val
  rw [swap_matrix,element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]

/-- The coordinate crossing is a noncontainment between actual parabolic
two-cores at two different points of the same plane. -/
theorem parabolic_crossing_or_point {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (T E : Subgroup (unipotent (F := F))) [T.Normal]
    (hET : E ≤ T) (hTE : T ≤ normalizer (E : Set (unipotent (F := F))))
    (hc : Nat.card F^2 ≤ Nat.card E) (hout : ¬ E ≤ wing true) :
    (∃ s : Sp F, s ∈ planeLocal ∧ s ∉ pointParabolic ∧
      ¬ E.map unipotent.subtype ⊓ (planeParabolic (F := F)).pCoreIn 2 ≤
        ((pointParabolic (F := F)).map (MulAut.conj s).toMonoidHom).pCoreIn 2) ∨
      T = wing false := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rcases crossing_or_point T E hET hTE hc hout with ⟨u,w,v,hu,hE⟩ | hpoint
  swap
  · exact Or.inr hpoint
  left
  refine ⟨swap,?_,?_,?_⟩
  · apply (Plane.mem_local_iff _).mpr
    refine ⟨?_,?_⟩
    · rw [mem_planeParabolic_iff]
      intro i j
      rw [swap_matrix]
      rfl
    · rw [swap_matrix]
      simp [Matrix.toBlocks₁₁,Matrix.fromBlocks,Matrix.det_fin_two,CharTwo.neg_eq]
  · intro hs
    have hh := ((mem_pointParabolic_iff _).mp hs).1
    rw [swap_matrix] at hh
    exact one_ne_zero hh
  intro hle
  have hplane : (element 0 u w v).val ∈ (planeParabolic (F := F)).pCoreIn 2 := by
    rw [pCoreIn,planeParabolic_core_map_eq_radical hF hn]
    change (element 0 u w v).val ∈ SymplecticConjugatePair.planeRadical
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)
  have hmem := hle ⟨mem_map_of_mem unipotent.subtype hE,hplane⟩
  rw [←map_pCoreIn_of_injective 2 pointParabolic _ (MulAut.conj swap).injective] at hmem
  obtain ⟨y,hy,he⟩ := hmem
  change swap*y*swap⁻¹ = (element 0 u w v).val at he
  have hsInv : (swap (F := F))⁻¹=swap := inv_eq_of_mul_eq_one_left swap_square
  have he' : (element 0 v w u).val = y := by
    rw [←swap_shear u w v,←he]
    rw [hsInv]
    calc
      swap * (swap*y*swap)*swap = (swap*swap)*y*(swap*swap) := by group
      _ = y := by rw [swap_square]; simp
  rw [pCoreIn,pointParabolic_core_map_eq_radical hF hn] at hy
  change y ∈ SymplecticConjugatePair.pointRadical at hy
  rw [←he',SymplecticConjugatePair.pointRadical_eq_wing] at hy
  obtain ⟨k,hk,hval⟩ := hy
  have hk' : k=element 0 v w u := Subtype.ext hval
  rw [hk'] at hk
  exact hu ((element_mem_wing false _ _ _ _).mp hk)

end Theory.SpecificGroups.SymplecticFour.NeighborMoverCrossing
