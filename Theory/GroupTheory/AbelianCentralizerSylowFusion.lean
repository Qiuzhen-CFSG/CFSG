module
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.Sylow

/-!
# Normalizer fusion for an abelian centralizer Sylow subgroup

If an abelian p-subgroup is Sylow in the full centralizer of one of its
elements, every ambient conjugate of that element lying in the subgroup
is obtained by a conjugator in its full normalizer. Sylow conjugacy in the
target element centralizer corrects the original ambient transporter.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open scoped IsMulCommutative
namespace Subgroup

/-- Correct an ambient transporter inside the target centralizer, retaining
the original abelian subgroup and its full normalizer. -/
theorem exists_normalizer_conjugator_of_centralizer_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) [IsMulCommutative E] (a b : E)
    (P : Sylow p (centralizer ({(a : G)} : Set G)))
    (hP : (P : Subgroup (centralizer ({(a : G)} : Set G))) =
      E.subgroupOf (centralizer ({(a : G)} : Set G)))
    (hab : IsConj (a : G) (b : G)) :
    ∃ n ∈ normalizer (E : Set G), n * (a : G) * n⁻¹ = b := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hab
  let A := centralizer ({(a : G)} : Set G)
  let B := centralizer ({(b : G)} : Set G)
  have hEA : E ≤ A := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : E) a))
  have hEB : E ≤ B := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : E) b))
  have hAB : A.map (MulAut.conj g).toMonoidHom = B := by
    rw [Theory.GroupTheory.CentralizerSmallKernelTransport.map_centralizer]
    change centralizer ({g*(a:G)*g⁻¹} : Set G)=B
    rw [hg]
  let e : A ≃* B := ((MulAut.conj g).subgroupMap A).trans (MulEquiv.subgroupCongr hAB)
  let Q : Sylow p B := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card (E.subgroupOf B) = p ^ (Nat.card B).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv,
      ←Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv,←hP,P.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  let R := Sylow.ofCard (E.subgroupOf B) hc
  obtain ⟨c,hcR⟩ := MulAction.exists_smul_eq B Q R
  have hQmap : (Q : Subgroup B).map B.subtype = E.map (MulAut.conj g).toMonoidHom := by
    change ((P : Subgroup A).map e.toMonoidHom).map B.subtype = _
    rw [map_map]
    have he : B.subtype.comp e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp A.subtype := rfl
    rw [he,←map_map,hP,map_subgroupOf_eq_of_le hEA]
  have hmap : (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (c:G)).toMonoidHom = E := by
    have hh := congrArg (fun S : Sylow p B => (S : Subgroup B).map B.subtype) hcR
    change ((Q : Subgroup B).map (MulAut.conj c).toMonoidHom).map B.subtype =
      (E.subgroupOf B).map B.subtype at hh
    rw [map_subgroupOf_eq_of_le hEB,map_map] at hh
    have he : B.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj (c:G)).toMonoidHom.comp B.subtype := by
      ext x
      rfl
    rw [he,←map_map,hQmap] at hh
    exact hh
  refine ⟨(c:G)*g,mem_normalizer_iff_map_conj_eq.mpr ?_,?_⟩
  · rw [map_map] at hmap
    have he : (MulAut.conj (c:G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj ((c:G)*g)).toMonoidHom := by
      ext x
      change (c:G) * (g*x*g⁻¹) * (c:G)⁻¹ = ((c:G)*g)*x*((c:G)*g)⁻¹
      group
    rwa [he] at hmap
  · calc
      _ = (c:G) * (g*(a:G)*g⁻¹) * (c:G)⁻¹ := by group
      _ = (c:G) * (b:G) * (c:G)⁻¹ := by rw [hg]
      _ = b := by
        rw [mem_centralizer_singleton_iff.mp c.property,mul_inv_cancel_right]

/-- The ambient fusion-class intersection times the full abelian subgroup
order divides the order of its literal normalizer. -/
theorem fusion_card_mul_card_dvd_normalizer_of_centralizer_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) [IsMulCommutative E] (a : E)
    (P : Sylow p (centralizer ({(a : G)} : Set G)))
    (hP : (P : Subgroup (centralizer ({(a : G)} : Set G))) =
      E.subgroupOf (centralizer ({(a : G)} : Set G))) :
    Nat.card {b : E // IsConj (a : G) (b : G)} * Nat.card E ∣
      Nat.card (normalizer (E : Set G)) := by
  let N := normalizer (E : Set G)
  let S := MulAction.stabilizer N a
  have horbit (b : E) : b ∈ MulAction.orbit N a ↔ IsConj (a:G) (b:G) := by
    constructor
    · intro hb
      obtain ⟨n,hn⟩ := MulAction.mem_orbit_iff.mp hb
      exact isConj_iff.mpr ⟨n,congrArg Subtype.val hn⟩
    · intro hb
      obtain ⟨n,hn,he⟩ := exists_normalizer_conjugator_of_centralizer_sylow E a b P hP hb
      exact MulAction.mem_orbit_iff.mpr ⟨⟨n,hn⟩,Subtype.ext he⟩
  have hcard : Nat.card (MulAction.orbit N a) = Nat.card {b:E // IsConj (a:G) (b:G)} :=
    Nat.card_congr (Equiv.subtypeEquivRight horbit)
  have hES : E.subgroupOf N ≤ S := by
    intro e he
    apply MulAction.mem_stabilizer_iff.mpr
    apply Subtype.ext
    change (e:G)*(a:G)*(e:G)⁻¹=(a:G)
    rw [show (e:G)*(a:G)=(a:G)*(e:G) from
      congrArg Subtype.val (mul_comm (⟨(e:G),he⟩:E) a),mul_inv_cancel_right]
  have hd : Nat.card E ∣ Nat.card S := by
    have hh := card_dvd_of_le hES
    rwa [Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv] at hh
  have hm := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N a)
  rw [Nat.card_prod,hcard] at hm
  exact hm ▸ Nat.mul_dvd_mul_left _ hd

end Subgroup
