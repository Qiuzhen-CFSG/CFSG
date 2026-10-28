module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.Geometry
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.GroupTheory.CentralCoprimePrimeLift
/-!
# Transport of the marked classical local geometry through an odd center

Two-subgroups lift isomorphically through an actual central coprime kernel,
so cyclicity of their centers is preserved. Through a central cube kernel,
involutions lift and their full centralizers map onto the quotient centralizers;
the derived-subgroup cardinal bound therefore descends. This retains the
literal SL₃/PSL₃ and SU₃/PSU₃ maps in the C.5.12 application.
Source: Aschbacher–Smith A.3.21(a), p.55, and C.5.12, p.163.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {G Q F : Type*} [Group G] [Finite G] [Group Q] [Field F]
theorem center_isCyclic_of_central_coprime_cover
    (j : G →* GL (Fin 3) F) (hj : Function.Injective j)
    (hdet : ∀ g, GeneralLinearGroup.det (j g) = 1) (h2 : (2 : F) ≠ 0)
    (f : G →* Q) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (ho : Nat.Coprime 2 (Nat.card f.ker))
    (T : Subgroup Q) (hT : IsPGroup 2 T) (hn : ¬ IsMulCommutative T) : IsCyclic (center T) := by
  obtain ⟨A,hA,hAT,_,_,hi⟩ := T.exists_prime_lift_of_central_coprime f hf hc ho hT
  let g : A →* T := (f.comp A.subtype).codRestrict T (fun x => hAT ▸ mem_map_of_mem f x.property)
  have hg : Function.Bijective g := by
    constructor
    · intro x y he; exact hi (congrArg Subtype.val he)
    · intro t
      obtain ⟨x,hx,he⟩ := show t.val ∈ A.map f from hAT.symm ▸ t.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let e : A ≃* T := MulEquiv.ofBijective g hg
  have hnA : ¬ IsMulCommutative A := by
    intro ha
    let := ha
    apply hn
    apply IsMulCommutative.of_comm
    intro x y
    apply e.symm.injective
    rw [map_mul,map_mul,mul_comm]
  let := center_isCyclic_of_nonabelian_two_subgroup j hj hdet h2 A hA hnA
  exact (centerCongr e).isCyclic.mp inferInstance

omit [Field F] in
theorem derived_centralizer_bound_of_central_cube_cover
    (f : G →* Q) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1) {n : ℕ}
    (hb : ∀ z : G, orderOf z = 2 → Nat.card (commutator (centralizer ({z} : Set G))) ≤ n)
    (z : Q) (hz : orderOf z = 2) : Nat.card (commutator (centralizer ({z} : Set Q))) ≤ n := by
  obtain ⟨x,hx,rfl⟩ := Matrix.SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel f hf h3 z hz
  let C := centralizer ({x} : Set G)
  have hm : C.map f = centralizer ({f x} : Set Q) :=
    Matrix.SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel f hf hc h3 x
      (by simpa only [hx] using pow_orderOf_eq_one x)
  let e := MulEquiv.subgroupCongr hm
  let g := e.toMonoidHom.comp (f.subgroupMap C)
  have hg : Function.Surjective g := e.surjective.comp (f.subgroupMap_surjective C)
  have hgm : (commutator C).map g = commutator (centralizer ({f x} : Set Q)) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hg]
    rfl
  have hd := Nat.card_le_card_of_surjective (g.subgroupMap (commutator C))
    (g.subgroupMap_surjective (commutator C))
  rw [hgm] at hd
  exact hd.trans (hb x hx)
end Theory.SpecificGroups.Classical.SylowMarkedSL2
