module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Actors
public import Theory.GroupTheory.QuaternionCentralProductIntrinsicFrame

/-!
# Involutive frames in the two actual root-pair factors

The source residual is transitive on noncentral involutions of the core.
Transporting the checked quaternion central-product frame along this orbit
gives involutions generating the first factor over E. The marked returning
core equivalence gives the same result for the second factor. Both exact
frames are therefore consequences of IsType, with no model or generating
set supplied to the source theorem.

Source: Aschbacher, *Sporadic Groups* (1994),45.2–45.3, pp.242–243.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

private theorem core_aut_involution_orbit (h : IsType z)
    (x y : core z) (hx : orderOf x=2) (hy : orderOf y=2)
    (hxZ : x∉center (core z)) (hyZ : y∉center (core z)) :
    ∃ α : MulAut (core z), α x=y := by
  have hxGZ : (x:G)∉zpowers z := by
    intro hh
    apply hxZ
    rw [← h.toCentralizerHypothesis.core_center] at hh
    obtain ⟨v,hv,he⟩ := hh
    have hveq : v=x := Subtype.ext he
    exact hveq ▸ hv
  have hyGZ : (y:G)∉zpowers z := by
    intro hh
    apply hyZ
    rw [← h.toCentralizerHypothesis.core_center] at hh
    obtain ⟨v,hv,he⟩ := hh
    have hveq : v=y := Subtype.ext he
    exact hveq ▸ hv
  obtain ⟨k,hk,hkx⟩ := h.toCentralizerHypothesis.core_involution_orbit
    x y x.property y.property ((orderOf_coe x).trans hx) ((orderOf_coe y).trans hy)
    hxGZ hyGZ
  have hkN : k∈normalizer (core z : Set G) :=
    CentralizerHypothesis.centralizer_normalizes_core
      ((map_subtype_le _ : residual z ≤ centralizer z) hk)
  exact ⟨(core z).normalizerMonoidHom ⟨k,hkN⟩,Subtype.ext hkx⟩

private theorem returning_aut_involution_orbit (h : IsType z)
    (x y : P.conjugateCore) (hx : orderOf x=2) (hy : orderOf y=2)
    (hxZ : x∉center P.conjugateCore) (hyZ : y∉center P.conjugateCore) :
    ∃ α : MulAut P.conjugateCore, α x=y := by
  let e := P.conjugateCoreEquiv
  have hx' : orderOf (e.symm x)=2 := by rw [e.symm.orderOf_eq]; exact hx
  have hy' : orderOf (e.symm y)=2 := by rw [e.symm.orderOf_eq]; exact hy
  have hxZ' : e.symm x∉center (core z) := by
    intro hh
    apply hxZ
    rw [← e.apply_symm_apply x]
    exact (centerCongr e ⟨e.symm x,hh⟩).property
  have hyZ' : e.symm y∉center (core z) := by
    intro hh
    apply hyZ
    rw [← e.apply_symm_apply y]
    exact (centerCongr e ⟨e.symm y,hh⟩).property
  obtain ⟨α,hα⟩ := core_aut_involution_orbit h (e.symm x) (e.symm y) hx' hy' hxZ' hyZ'
  refine ⟨MulAut.congr e α, ?_⟩
  change e (α (e.symm x))=y
  rw [hα,e.apply_symm_apply]

/-- The original involution centralizer has a marked involutive frame. -/
theorem exists_left_frame (h : IsType z) :
    ∃ a b : G, a∈P.leftCore ∧ b∈P.leftCore ∧ a^2=1 ∧ b^2=1 ∧
      b*a=a*b*z ∧
      ∀ D : Subgroup G, P.E≤D → a∈D → b∈D → P.leftCore≤D := by
  let Q:=core z
  let Z : Q := ⟨z,z_mem_core h⟩
  let U : Q := ⟨P.u,P.mem_core⟩
  have hzZ : Z∈center Q := mem_center_iff.mpr (fun q =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (core_le_centralizer q.property)))
  have hz1 : Z≠1 := by
    intro hh
    have he : z=1 := congrArg Subtype.val hh
    have hi := h.involution
    simp [he] at hi
  have hu2 : orderOf U=2 := (orderOf_coe U).symm.trans (P.u_order h)
  have huZ : U∉center Q := by
    intro hh
    apply P.not_mem_line
    rw [← h.toCentralizerHypothesis.core_center]
    exact mem_map_of_mem Q.subtype hh
  obtain ⟨a,b,ha2,hb2,hau,hbu,hswap,hgen⟩ :=
    h.toCentralizerHypothesis.coreData.exists_hyperbolic_generators Z U hzZ hz1
      (fun x hx hxZ => core_aut_involution_orbit h x U hx hu2 hxZ huZ)
  have haL : (a:G)∈P.leftCore := ⟨a.property,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val hau.eq)⟩
  have hbL : (b:G)∈P.leftCore := ⟨b.property,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val hbu.eq)⟩
  refine ⟨a,b,haL,hbL,congrArg Subtype.val ha2,congrArg Subtype.val hb2,
    congrArg Subtype.val hswap,?_⟩
  intro D hED haD hbD x hx
  let J := D.subgroupOf Q
  have hZJ : Z∈J := hED P.z_mem_E
  have hUJ : U∈J := hED P.u_mem_E
  have haJ : a∈J := haD
  have hbJ : b∈J := hbD
  exact hgen J hZJ hUJ haJ hbJ ⟨x,hx.1⟩ (by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp hx.2)

/-- The returning involution centralizer has its corresponding marked frame. -/
theorem exists_right_frame (h : IsType z) :
    ∃ a b : G, a∈P.rightCore ∧ b∈P.rightCore ∧ a^2=1 ∧ b^2=1 ∧
      b*a=a*b*P.u ∧
      ∀ D : Subgroup G, P.E≤D → a∈D → b∈D → P.rightCore≤D := by
  let Q:=P.conjugateCore
  let Z : Q := ⟨P.u,P.u_mem_conjugateCore h⟩
  let U : Q := ⟨z,P.z_mem_conjugateCore h⟩
  have hzZ : Z∈center Q := mem_center_iff.mpr (fun q =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le q.property)))
  have hz1 : Z≠1 := by
    intro hh
    have he : P.u=1 := congrArg Subtype.val hh
    have hi := P.u_order h
    simp [he] at hi
  have hu2 : orderOf U=2 := (orderOf_coe U).symm.trans h.involution
  have huZ : U∉center Q := by
    intro hh
    have hm : z∈zpowers P.u := P.conjugateCore_center h ▸ mem_map_of_mem Q.subtype hh
    have hle : P.E ≤ zpowers P.u := sup_le (zpowers_le.mpr hm) le_rfl
    have he := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [P.E_card h,Nat.card_zpowers,P.u_order h] at he
    omega
  let d := h.toCentralizerHypothesis.coreData.map P.conjugateCoreEquiv
  obtain ⟨a,b,ha2,hb2,hau,hbu,hswap,hgen⟩ :=
    d.exists_hyperbolic_generators Z U hzZ hz1
      (fun x hx hxZ => P.returning_aut_involution_orbit h x U hx hu2 hxZ huZ)
  have haL : (a:G)∈P.rightCore := ⟨a.property,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val hau.eq)⟩
  have hbL : (b:G)∈P.rightCore := ⟨b.property,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val hbu.eq)⟩
  refine ⟨a,b,haL,hbL,congrArg Subtype.val ha2,congrArg Subtype.val hb2,
    congrArg Subtype.val hswap,?_⟩
  intro D hED haD hbD x hx
  let J := D.subgroupOf Q
  have hZJ : Z∈J := hED P.u_mem_E
  have hUJ : U∈J := hED P.z_mem_E
  have haJ : a∈J := haD
  have hbJ : b∈J := hbD
  exact hgen J hZJ hUJ haJ hbJ ⟨x,hx.1⟩ (by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp hx.2)

private def left_frame_of_generators (h : IsType z) (a b : G)
    (ha : a∈P.leftCore) (hb : b∈P.leftCore) (ha2 : a^2=1) (hb2 : b^2=1)
    (hswap : b*a=a*b*z)
    (hgen : ∀ D : Subgroup G, P.E≤D → a∈D → b∈D → P.leftCore≤D) :
    HyperbolicFrame (P.hyperbolicFactors h).A (P.hyperbolicFactors h).z where
  a := ⟨a,mem_sup_left ha⟩
  b := ⟨b,mem_sup_left hb⟩
  a_mem := ha
  b_mem := hb
  a_square := Subtype.ext ha2
  b_square := Subtype.ext hb2
  swap := Subtype.ext hswap
  generate := by
    intro D hZD haD hbD x hx
    have hED : P.E ≤ D.map P.R.subtype := by
      rw [← P.R_center h]
      exact map_mono hZD
    have hxD := hgen (D.map P.R.subtype) hED
      (mem_map_of_mem P.R.subtype haD) (mem_map_of_mem P.R.subtype hbD) hx
    obtain ⟨y,hy,he⟩ := hxD
    have heq : y=x := Subtype.ext he
    exact heq ▸ hy

private def right_frame_of_generators (h : IsType z) (a b : G)
    (ha : a∈P.rightCore) (hb : b∈P.rightCore) (ha2 : a^2=1) (hb2 : b^2=1)
    (hswap : b*a=a*b*P.u)
    (hgen : ∀ D : Subgroup G, P.E≤D → a∈D → b∈D → P.rightCore≤D) :
    HyperbolicFrame (P.hyperbolicFactors h).B (P.hyperbolicFactors h).u where
  a := ⟨a,mem_sup_right ha⟩
  b := ⟨b,mem_sup_right hb⟩
  a_mem := ha
  b_mem := hb
  a_square := Subtype.ext ha2
  b_square := Subtype.ext hb2
  swap := Subtype.ext hswap
  generate := by
    intro D hZD haD hbD x hx
    have hED : P.E ≤ D.map P.R.subtype := by
      rw [← P.R_center h]
      exact map_mono hZD
    have hxD := hgen (D.map P.R.subtype) hED
      (mem_map_of_mem P.R.subtype haD) (mem_map_of_mem P.R.subtype hbD) hx
    obtain ⟨y,hy,he⟩ := hxD
    have heq : y=x := Subtype.ext he
    exact heq ▸ hy

/-- Both exact factor frames are produced by the original involution orbits. -/
theorem exists_hyperbolic_frames (h : IsType z) :
    Nonempty (HyperbolicFrame (P.hyperbolicFactors h).A (P.hyperbolicFactors h).z ×
      HyperbolicFrame (P.hyperbolicFactors h).B (P.hyperbolicFactors h).u) := by
  obtain ⟨a,b,ha,hb,ha2,hb2,hab,hgen⟩ := P.exists_left_frame h
  obtain ⟨c,d,hc,hd,hc2,hd2,hcd,hgen'⟩ := P.exists_right_frame h
  exact ⟨P.left_frame_of_generators h a b ha hb ha2 hb2 hab hgen,
    P.right_frame_of_generators h c d hc hd hc2 hd2 hcd hgen'⟩

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
