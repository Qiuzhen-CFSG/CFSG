module
public import Theory.GroupTheory.CoprimeQuotientSubgroups.MarkedPair
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.QuotientIntersection
public import Theory.ElementaryAbelian.Join

/-!
# Independent prime factors with separated fixed subgroups

Two elementary factors of order p whose images commute through a coprime
kernel lift to an elementary plane inside their original join. If the kernel
lies in two fixed subgroups and the factors have the prescribed opposite
containments and trivial intersections, the lifted plane meets their common
fixed subgroup trivially. The literal containment survives the lift.

Source application: Aschbacher--Smith, 10.2.9, printed p.753, the two cubic
factors in the original moving parabolics.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- A common coprime lift retains separation from both original fixed subgroups. -/
theorem exists_separated_elementary_pair {p : ℕ} [Fact p.Prime]
    (f : G →* Q) (hker : Nat.Coprime p (Nat.card f.ker))
    (A B C D : Subgroup G) [IsElementaryAbelian p A] [IsElementaryAbelian p B]
    (hAc : Nat.card A = p) (hBc : Nat.card B = p)
    (hcomm : A.map f ≤ centralizer (B.map f : Set Q))
    (hkerCD : f.ker ≤ C ⊓ D) (hAD : A ≤ D) (hBC : B ≤ C)
    (hAC : Disjoint A C) (hBD : Disjoint B D) :
    ∃ E : Subgroup G, E ≤ A ⊔ B ∧ IsElementaryAbelian p E ∧
      Nat.card E = p^2 ∧ Disjoint E (C ⊓ D) := by
  let K := A ⊔ B
  let q := f.comp K.subtype
  have hq : Nat.Coprime p (Nat.card q.ker) := by
    have hc : Nat.card q.ker ∣ Nat.card f.ker := by
      have hh := card_dvd_of_le (show q.ker.map K.subtype ≤ f.ker from by
        rintro _ ⟨x,hx,rfl⟩
        exact hx)
      rwa [card_map_of_injective K.subtype_injective] at hh
    exact hker.of_dvd_right hc
  have hAC' : Disjoint (A.map f) (C.map f) := by
    rw [disjoint_iff,←map_inf_of_ker_le f A C (hkerCD.trans inf_le_left),hAC.eq_bot,map_bot]
  have hBD' : Disjoint (B.map f) (D.map f) := by
    rw [disjoint_iff,←map_inf_of_ker_le f B D (hkerCD.trans inf_le_right),hBD.eq_bot,map_bot]
  have hdis : Disjoint (A.map f) (B.map f) := hBD'.symm.mono_left (map_mono hAD)
  have hrange : A.map f ⊔ B.map f ≤ q.range := by
    rw [←map_sup]
    exact le_of_eq (by change K.map f = (f.comp K.subtype).range; rw [MonoidHom.range_comp,range_subtype])
  let : IsElementaryAbelian p (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian p (B.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian p (A.map f ⊔ B.map f : Subgroup Q) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hcomm)
  obtain ⟨P,R,hP,hR,hPc,hRc,_,_,hE,hEc⟩ :=
    exists_elementary_pair_lift q hq (A.map f) (B.map f) hrange hdis
  let E := (P ⊔ R).map K.subtype
  have hcA : Nat.card (A.map f) = p := by
    let e := MulEquiv.ofBijective (f.subgroupMap A)
      ⟨fun x y h => injective_comp_subtype_of_coprime_ker f hker A
        (IsElementaryAbelian.isPGroup p A) (congrArg Subtype.val h), f.subgroupMap_surjective A⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hAc
  have hcB : Nat.card (B.map f) = p := by
    let e := MulEquiv.ofBijective (f.subgroupMap B)
      ⟨fun x y h => injective_comp_subtype_of_coprime_ker f hker B
        (IsElementaryAbelian.isPGroup p B) (congrArg Subtype.val h), f.subgroupMap_surjective B⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hBc
  let := hE
  have he : IsElementaryAbelian p E := IsElementaryAbelian.map K.subtype
  refine ⟨E,map_subtype_le _,he,?_,?_⟩
  · rw [card_map_of_injective K.subtype_injective,hEc,
      card_sup_eq_mul_of_normalizes_of_disjoint _ _
        ((le_centralizer_iff.mp hcomm).trans (centralizer_le_normalizer _)) hdis,hcA,hcB,pow_two]
  · apply disjoint_def.mpr
    intro x hx hxCD
    have him : f x ∈ A.map f ⊔ B.map f := by
      obtain ⟨z,hz,rfl⟩ := hx
      have hm : (P ⊔ R).map q = A.map f ⊔ B.map f := by rw [map_sup,hP,hR]
      exact hm ▸ mem_map_of_mem q hz
    have hnorm : B.map f ≤ normalizer (A.map f : Set Q) :=
      (le_centralizer_iff.mp hcomm).trans (centralizer_le_normalizer _)
    have himul : f x ∈ (A.map f : Set Q) * (B.map f : Set Q) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hnorm]
      exact him
    obtain ⟨a,ha,b,hb,hab⟩ := himul
    have hfa : a ∈ C.map f := by
      have hxC := mem_map_of_mem f hxCD.1
      rw [←hab] at hxC
      exact (C.map f).mul_mem_cancel_right (map_mono hBC hb) |>.mp hxC
    have ha1 : a = 1 := hAC'.le_bot ⟨ha,hfa⟩
    have hbD : b ∈ D.map f := by
      have hxD := mem_map_of_mem f hxCD.2
      simpa only [←hab,ha1,one_mul] using hxD
    have hb1 : b = 1 := hBD'.le_bot ⟨hb,hbD⟩
    have hf1 : f x = 1 := by simpa only [ha1,hb1,one_mul] using hab.symm
    have hii := injective_comp_subtype_of_coprime_ker f hker E he.isPGroup
    exact congrArg Subtype.val (hii (show f x = f 1 from by simpa using hf1) : (⟨x,hx⟩ : E) = 1)
end Subgroup
