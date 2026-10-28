module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.CyclicImages

/-!
# The order-two transvection branch on the marked chief space

An involution in the wreath base fixes eight of the sixteen natural vectors
only when it is supported in a single coordinate. An equivariant bijection
of fixed spaces therefore places every order-two image of fixed codimension
one in one of the literal marked factors. This calculation takes place in
the action image and does not require an involution lift to the original group.

InternalLift applies this to every original noncentral chief factor under
the order-two premise. Exclusion of the remaining order-four branch stays
with the offender-plane owner.

Source: Aschbacher--Smith B.1.8(4) and Notation 15.2.9,
printed pp.70,1110; refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath
private instance : Fintype Actor := Fintype.ofEquiv ((C2 → SL2) × C2)
  (RegularWreathProduct.equivProd SL2 C2).symm
private instance : DecidableEq Actor := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) RegularWreathProduct.ext_iff.symm
set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 10000 in
private theorem rank_one_involution_factor : ∀ g : Actor,
    g.right=1 → g^2=1 → g≠1 →
    Fintype.card {v : Space // action g v=v}=8 →
      g∈factor 1 ∨ g∈factor flip := by
  simp only [mem_factor]
  decide +kernel
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) D W}

omit [Finite D] in
/-- An order-two image of fixed codimension one is supported on one of the
literal marked natural planes. -/
theorem order_two_image_le_factor (c : ChiefWreathCoordinates ρ) (A : Subgroup D)
    (hbase : A.map c.actor ≤ ChiefWreath.base)
    (hcard : Nat.card (A.map c.actor)=2) (hcod : fixedCodim ρ A=1) :
    ∃ i : ChiefWreath.C2, A ≤ c.factor i := by
  classical
  let E := A.map c.actor
  let : IsCyclic E := isCyclic_of_prime_card hcard
  obtain ⟨g,hg⟩ := E.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hz : zpowers g=E := hg
  have hgm : g∈E := hz ▸ mem_zpowers g
  have ho : orderOf g=2 := by rw [←Nat.card_zpowers,hz]; exact hcard
  have hgn : g≠1 := by intro hh; rw [hh,orderOf_one] at ho; contradiction
  have hg2 : g^2=1 := by
    have hh := pow_orderOf_eq_one g
    rwa [ho] at hh
  have hfix (v : W) : v∈fixedSpace ρ A ↔
      ChiefWreath.action g (c.vectors (Multiplicative.ofAdd v)) = c.vectors (Multiplicative.ofAdd v) := by
    constructor
    · intro hv
      obtain ⟨a,ha,hag⟩ := hgm
      rw [←hag,←c.vectors_action]
      exact congrArg (fun w => c.vectors (Multiplicative.ofAdd w)) (hv ⟨a,ha⟩)
    · intro hv a
      have hvg : ∀ x : ChiefWreath.Actor, x∈zpowers g →
          ChiefWreath.action x (c.vectors (Multiplicative.ofAdd v)) = c.vectors (Multiplicative.ofAdd v) := by
        intro x hx
        rcases Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx) with ⟨k,hk,hkx⟩
        have hk := Finset.mem_range.mp hk
        rw [ho] at hk
        interval_cases k
        · have hx1 : x=1 := by simpa using hkx.symm
          rw [hx1]
          funext j
          simp [ChiefWreath.action]
        · have hxg : x=g := by simpa using hkx.symm
          rw [hxg]
          exact hv
      apply Multiplicative.ofAdd.injective
      apply c.vectors.injective
      change c.vectors (Multiplicative.ofAdd (ρ a v)) = c.vectors (Multiplicative.ofAdd v)
      exact (c.vectors_action a (Multiplicative.ofAdd v)).trans
        (hvg (c.actor a) (by rw [hz]; exact mem_map_of_mem c.actor a.property))
  let F : fixedSpace ρ A ≃ {v : ChiefWreath.Space // ChiefWreath.action g v=v} :=
    { toFun := fun v => ⟨c.vectors (Multiplicative.ofAdd v.val),(hfix v).mp v.property⟩
      invFun := fun v => ⟨(c.vectors.symm v.val).toAdd,(hfix _).mpr (by simpa using v.property)⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  have hdim : Module.finrank (ZMod 2) W=4 := by
    have hc : Nat.card W=16 := by
      change Nat.card (Multiplicative W)=16
      rw [Nat.card_congr c.vectors.toEquiv]
      change Nat.card (ZMod 2 → Fin 2 → ZMod 2)=16
      simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
      rfl
    have hp := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=W)
    rw [Nat.card_zmod,hc] at hp
    exact (Nat.pow_right_injective (by decide : 1<2) hp).symm
  have hdimF : Module.finrank (ZMod 2) (fixedSpace ρ A)=3 := by
    have hh := fixedCodim_add_finrank ρ A
    rw [hdim,hcod] at hh
    omega
  have hcount : Fintype.card {v : ChiefWreath.Space // ChiefWreath.action g v=v}=8 := by
    have hp := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=fixedSpace ρ A)
    rw [Nat.card_zmod,hdimF] at hp
    rw [←Nat.card_eq_fintype_card,←Nat.card_congr F,hp]
    rfl
  have hfac := ChiefWreath.rank_one_involution_factor g (hbase hgm) hg2 hgn hcount
  have hle (i : ChiefWreath.C2) (hi : g∈ChiefWreath.factor i) : A ≤ c.factor i := by
    apply map_le_iff_le_comap.mp
    change E ≤ ChiefWreath.factor i
    rw [←hz]
    exact zpowers_le.mpr hi
  rcases hfac with hi | hi
  · exact ⟨1,hle 1 hi⟩
  · exact ⟨ChiefWreath.flip,hle ChiefWreath.flip hi⟩
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreathCoordinates
