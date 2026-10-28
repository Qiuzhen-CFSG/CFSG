module
public import Theory.GroupTheory.SymmetricFourNormalFour
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-!
# Residual generators in a symmetric-four group

The center of a Sylow two-subgroup of S₄ lies in its self-centralizing Klein
four core. A nonidentity core involution and any nonidentity cubic generate
the actual two-residual A₄ and satisfy the A₄ conjugate relations. Twelve
short words cover the even permutations; Lean's kernel checks this finite
calculation and its relations. Equivalences and subgroup maps then transport
the results while retaining the chosen elements and literal residual images.

These facts supply the common involution and residual generators for the
binary action recognition in Aschbacher–Smith, *The Classification of
Quasithin Groups*, 14.3.19(4). The companion group-action consumer applies
them to the two actual symmetric-four automizer subgroups.
-/

namespace SymmetricFourResidualGenerators
open Subgroup Theory.SpecificGroups.SymmetricSix.DuadCalculation
set_option maxRecDepth 4096
local notation "S4" => Equiv.Perm (Fin 4)
private def words : Fin 12 → List (Fin 2) := ![
[],
[1],
[1, 1],
[0],
[0, 1],
[0, 1, 1],
[1, 0, 1, 1],
[1, 0, 1, 1, 1],
[1, 0, 1, 1, 1, 1],
[1, 1, 0, 1],
[1, 1, 0, 1, 1],
[1, 1, 0, 1, 1, 1]]
private def word (r t : S4) (k : Fin 12) : S4 := ((words k).map (![r,t])).prod

private theorem relations (r t : S4) (h1 : r.sign = 1) (h2 : r^2=1)
    (h3 : r≠1) (h4 : t^3=1) (h5 : t≠1) : (r*t)^3=1 ∧ Commute r (t*r*t⁻¹) ∧
      r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1 := by
  have h : ∀ r t : S4, (r.sign=1 ∧ r^2=1 ∧ r≠1 ∧ t^3=1 ∧ t≠1) →
      (r*t)^3=1 ∧ r*(t*r*t⁻¹)=(t*r*t⁻¹)*r ∧
        r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1 := by decide +kernel
  exact h r t ⟨h1,h2,h3,h4,h5⟩

private theorem covered (r t : S4) (h1 : r.sign = 1) (h2 : r^2=1) (h3 : r≠1)
    (h4 : t^3=1) (h5 : t≠1) (x : S4) (hx : x.sign=1) :
    ∃ k : Fin 12, word r t k=x := by
  have h : ∀ r t x : S4, (r.sign=1 ∧ r^2=1 ∧ r≠1 ∧ t^3=1 ∧ t≠1 ∧ x.sign=1) →
      ∃ k : Fin 12, word r t k=x := by decide +kernel
  exact h r t x ⟨h1,h2,h3,h4,h5,hx⟩

private theorem concrete_generates (r t : S4) (hr : r ∈ core) (hrne : r≠1)
    (ht3 : t^3=1) (htne : t≠1) : closure ({r,t} : Set S4) = pResidual 2 S4 := by
  have hr' := (core_mem_iff r).mp hr
  rw [Theory.SpecificGroups.SymmetricFourResidual.residual_eq]
  apply le_antisymm
  · rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · subst x
      exact hr'.1
    · rw [h]
      exact (show ∀ t : S4, t^3=1 → t.sign=1 from by decide +kernel) t ht3
  · intro x hx
    obtain ⟨k,rfl⟩ := covered r t hr'.1 hr'.2 hrne ht3 htne x hx
    apply list_prod_mem
    intro y hy
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hy
    fin_cases i
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)

private theorem core_image {X : Type*} [Group X] (e : X ≃* S4) :
    (pCore 2 X).map e.toMonoidHom = core := by rw [pCore_map_iso,← core_eq]

private theorem core_mem {X : Type*} [Group X] (e : X ≃* S4) (r : X) :
    r ∈ pCore 2 X ↔ e r ∈ core := by
  rw [← core_image e]
  exact ⟨mem_map_of_mem e.toMonoidHom,fun h => by
    simpa only [e.symm_apply_apply] using mem_map_equiv.mp h⟩

public theorem core_square {X : Type*} [Group X] (e : X ≃* S4)
    (r : X) (hr : r ∈ pCore 2 X) : r^2=1 := by
  apply e.injective
  simpa only [map_pow,map_one] using ((core_mem_iff (e r)).mp ((core_mem e r).mp hr)).2

public theorem core_card {X : Type*} [Group X] (e : X ≃* S4) :
    Nat.card (pCore 2 X) = 4 := by
  rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,core_image e]
  exact Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card

public theorem core_self_centralizing {X : Type*} [Group X] (e : X ≃* S4) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  intro r hr
  apply (core_mem e r).mpr
  rw [← centralizer_core,mem_centralizer_iff]
  intro x hx
  have hx' : e.symm x ∈ pCore 2 X := (core_mem e _).mpr (by simpa using hx)
  simpa only [map_mul,e.apply_symm_apply] using congrArg e (hr (e.symm x) hx')

public theorem central_sylow_mem_core {X : Type*} [Group X]
    (e : X ≃* S4) (S : Sylow 2 X) (r : S) (hr : r ∈ center S) :
    (r : X) ∈ pCore 2 X := by
  apply core_self_centralizing e
  intro x hx
  have hxS : x ∈ S := (pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal S hx
  exact congrArg Subtype.val ((mem_center_iff.mp hr) ⟨x,hxS⟩)

public theorem exists_central_sylow_involution {X : Type*} [Group X] [Finite X]
    (e : X ≃* S4) (S : Sylow 2 X) :
    ∃ r : X, r ∈ S ∧ r≠1 ∧ r^2=1 ∧ (∀ s : X, s∈S → Commute r s) ∧
      r∈pCore 2 X ∧ r∈pResidual 2 X := by
  have hCS : pCore 2 X ≤ (S : Subgroup X) := pCore_isPGroup.le_sylow_of_normal S
  have hcard : 1 < Nat.card S := by
    have hle := card_le_of_le hCS
    rw [core_card e] at hle
    change 4 ≤ Nat.card S at hle
    omega
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp hcard
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  obtain ⟨r,hr⟩ := exists_ne (1 : center S)
  have hrcore := central_sylow_mem_core e S r.val r.property
  refine ⟨r.val.val,r.val.property,?_,core_square e _ hrcore,?_,hrcore,?_⟩
  · intro h
    exact hr (Subtype.ext (Subtype.ext h))
  · intro s hs
    exact (show Commute s r.val.val from
      congrArg Subtype.val ((mem_center_iff.mp r.property) ⟨s,hs⟩)).symm
  · exact Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual_of_equiv e hrcore

public theorem residual_generators {X : Type*} [Group X]
    (e : X ≃* S4) (r t : X) (hr : r∈pCore 2 X) (hrne : r≠1)
    (ht3 : t^3=1) (htne : t≠1) :
    (r*t)^3=1 ∧ Commute r (t*r*t⁻¹) ∧
      r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1 ∧
      closure ({r,t} : Set X) = pResidual 2 X := by
  have hr' := (core_mem e r).mp hr
  have hrt := relations (e r) (e t) ((core_mem_iff _).mp hr').1
    ((core_mem_iff _).mp hr').2 (by simpa using hrne)
    (by simpa only [map_pow,map_one] using congrArg e ht3) (by simpa using htne)
  refine ⟨?_,?_,?_,?_⟩
  · apply e.injective
    simpa only [map_pow,map_mul,map_one] using hrt.1
  · show r*(t*r*t⁻¹) = (t*r*t⁻¹)*r
    apply e.injective
    simpa only [map_mul,map_inv] using hrt.2.1.eq
  · apply e.injective
    simpa only [map_mul,map_inv,map_pow,map_one] using hrt.2.2
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [MonoidHom.map_closure,map_pResidual]
    have hi : e.toMonoidHom '' ({r,t} : Set X) = {e r,e t} := by
      rw [Set.image_insert_eq,Set.image_singleton]
      rfl
    rw [hi]
    exact concrete_generates (e r) (e t) hr' (by simpa using hrne)
      (by simpa only [map_pow,map_one] using congrArg e ht3) (by simpa using htne)

public theorem exists_cubic {X : Type*} [Group X]
    (e : X ≃* S4) : ∃ t : X, t^3=1 ∧ t≠1 := by
  let c : S4 := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc : c^3=1 ∧ c≠1 := by decide +kernel
  refine ⟨e.symm c,?_,?_⟩
  · simpa only [map_pow,map_one] using congrArg e.symm hc.1
  · simpa only [ne_eq,EmbeddingLike.map_eq_one_iff] using hc.2

public theorem embedded_central_sylow_mem_core
    {G : Type*} [Group G] (X : Subgroup G) (e : X ≃* S4) (S : Sylow 2 X)
    (r : G) (hr : r∈(S : Subgroup X).map X.subtype)
    (hcentral : ∀ s : G, s∈(S : Subgroup X).map X.subtype → Commute r s) :
    r∈(pCore 2 X).map X.subtype := by
  obtain ⟨x,hx,rfl⟩ := hr
  apply mem_map_of_mem
  exact central_sylow_mem_core e S ⟨x,hx⟩ (by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (hcentral y.val.val (mem_map_of_mem X.subtype y.property)).symm.eq)

public theorem embedded_residual_generators
    {G : Type*} [Group G] (X : Subgroup G) (e : X ≃* S4) (r t : G)
    (hr : r∈(pCore 2 X).map X.subtype) (ht : t∈X)
    (hrne : r≠1) (ht3 : t^3=1) (htne : t≠1) :
    r^2=1 ∧ (r*t)^3=1 ∧ Commute r (t*r*t⁻¹) ∧
      r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹)=1 ∧
      closure ({r,t} : Set G) = (pResidual 2 X).map X.subtype := by
  obtain ⟨rX,hrX,rfl⟩ := hr
  let tX : X := ⟨t,ht⟩
  have hrneX : rX≠1 := by intro h; exact hrne (congrArg Subtype.val h)
  have htneX : tX≠1 := by intro h; exact htne (congrArg Subtype.val h)
  obtain ⟨hprod,hcomm,hnorm,hgen⟩ := residual_generators e rX tX hrX hrneX
    (Subtype.ext ht3) htneX
  refine ⟨congrArg Subtype.val (core_square e rX hrX),
    congrArg Subtype.val hprod,?_,congrArg Subtype.val hnorm,?_⟩
  · exact hcomm.map X.subtype
  · have h := congrArg (Subgroup.map X.subtype) hgen
    rw [MonoidHom.map_closure] at h
    have hi : X.subtype '' ({rX,tX} : Set X) = {rX.val,t} := by
      rw [Set.image_insert_eq,Set.image_singleton]
      rfl
    rwa [hi] at h

end SymmetricFourResidualGenerators
