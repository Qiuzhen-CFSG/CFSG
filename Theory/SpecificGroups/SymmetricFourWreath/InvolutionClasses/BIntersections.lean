module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.BModel

/-!
# The literal B intersections and their Sylow actions

Transport the sixteen-parameter certificates to the actual subgroup B.
The six involution classes meet B in sizes 1, 2, 4, 4, 4, and 0, with the
first intersection equal to {z}. Each nonempty intersection is a Sylow orbit.
The two diagonal four-point intersections have pointwise centralizer B in T,
providing the faithful four-point action used by the growth argument.

Source: Aschbacher–Smith 13.9.4–5, printed p.970.
-/

@[expose] public noncomputable section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup

theorem parameters_class_iff (i : Fin 6) (a : Parameters) :
    IsConj (representative i) (parametersToW a) ↔ a≠1 ∧ parameterIndex a=i := by
  rw [isConj_representative_iff,parametersToW_index]
  constructor
  · rintro ⟨ho,hi⟩
    refine ⟨?_,hi⟩
    intro he
    simp [he] at ho
  · rintro ⟨ha,hi⟩
    refine ⟨orderOf_eq_prime ?_ ?_,hi⟩
    · apply elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=B)
      rw [←parametersToW_range]
      exact ⟨a,rfl⟩
    · intro h
      exact ha (parametersToW_injective (h.trans (map_one parametersToW).symm))

theorem card_B_class (i : Fin 6) :
    Nat.card {x:B // IsConj (representative i) (x:W)}=orbitSize i := by
  let e : {a:Parameters // a≠1 ∧ parameterIndex a=i} ≃
      {x:B // IsConj (representative i) (x:W)} :=
    parametersEquivB.toEquiv.subtypeEquiv (fun a=>(parameters_class_iff i a).symm)
  rw [←Nat.card_congr e,Nat.card_eq_fintype_card,parameter_class_card]

theorem representative_mem_B : ∀i:Fin 6,i≠5 → representative i∈B := by
  have h : ∀i:Fin 6,i≠5 → (representative i).right=1 ∧
      (representative i).left 1∈(plane false).map square ∧
      (representative i).left turn∈(plane false).map square := by
    change ∀i:Fin 6,i≠5 → (representative i).right=1 ∧
      (∃a,a∈plane false ∧ square a=(representative i).left 1) ∧
      (∃a,a∈plane false ∧ square a=(representative i).left turn)
    decide +kernel
  intro i hi
  exact (mem_elementary false false _).mpr (h i hi)

theorem B_class_zero : {x:W | x∈B ∧ IsConj (representative 0) x}={z} := by
  have hz : z∈B := representative_mem_B 0 (by decide)
  have hzz : IsConj (representative 0) z := IsConj.refl z
  have hcard := card_B_class 0
  have hs : Subsingleton {x:B // IsConj (representative 0) (x:W)} :=
    Finite.card_le_one_iff_subsingleton.mp (by rw [hcard];decide)
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    exact congrArg (fun a:{x:B // IsConj (representative 0) (x:W)}=>(a.1:W))
      (@Subsingleton.elim _ hs ⟨⟨x,hx⟩,hc⟩ ⟨⟨z,hz⟩,hzz⟩)
  · rintro rfl
    exact ⟨hz,hzz⟩

theorem B_class_sylow_transitive (i : Fin 6) (x y : B)
    (hx : IsConj (representative i) (x:W)) (hy : IsConj (representative i) (y:W)) :
    ∃g∈(standardSylow:Subgroup W),g*(x:W)*g⁻¹=(y:W) := by
  obtain ⟨a,rfl⟩ := parametersEquivB.surjective x
  obtain ⟨b,rfl⟩ := parametersEquivB.surjective y
  have ha := (parameters_class_iff i a).mp hx
  have hb := (parameters_class_iff i b).mp hy
  obtain ⟨s,hs⟩ := parameter_orbit a b ha.1 hb.1 (ha.2.trans hb.2.symm)
  refine ⟨sylowEmbedding (orbitActor s),⟨orbitActor s,rfl⟩,?_⟩
  change sylowEmbedding (orbitActor s)*sylowEmbedding (parametersToP a)*
    (sylowEmbedding (orbitActor s))⁻¹=sylowEmbedding (parametersToP b)
  simpa only [map_mul,map_inv] using congrArg sylowEmbedding hs

/-- Source Δ4 and Δ5, indexed by 3 and 4, have pointwise stabilizer B in T. -/
theorem B_class_pointwise_centralizer (i : Fin 6) (hi : i=3 ∨ i=4) :
    (standardSylow:Subgroup W) ⊓ centralizer
      {x:W | x∈B ∧ IsConj (representative i) x}=B := by
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    obtain ⟨p,rfl⟩ := hx
    have hfix : ∀a:Parameters,a≠1 → parameterIndex a=i →
        p*parametersToP a=parametersToP a*p := by
      intro a ha hai
      apply sylowEmbedding_injective
      have ham : parametersToW a∈B := by rw [←parametersToW_range];exact ⟨a,rfl⟩
      have h := hc (parametersToW a) ⟨ham,(parameters_class_iff i a).mpr ⟨ha,hai⟩⟩
      simpa only [parametersToW,MonoidHom.comp_apply,map_mul] using h.symm
    have hp := (parameter_class_centralizer i hi p).mp hfix
    exact (mem_elementary false false _).mpr
      ⟨hp.1,⟨p.left 1,hp.2.1,rfl⟩,⟨p.left turn,hp.2.2,rfl⟩⟩
  · intro x hx
    refine ⟨elementary_le_standardSylow false false hx,?_⟩
    intro y hy
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=B)).is_comm.comm
        (⟨y,hy.1⟩:B) ⟨x,hx⟩)

end SymmetricFourWreath.InvolutionClasses
