module

public import Theory.SpecificGroups.SymmetricFive.StarCenterGeometry
public import Theory.SpecificGroups.SymmetricFive.PentagonNormalizer
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# The two invariant pentagons through a central coprime cover

Prime-five subgroups lift uniquely through a central kernel of order
coprime to five. An automorphism lifting an even involution of S₅ can
therefore normalize at most two such subgroups: each image is a Sylow five,
and a normalizing involution must invert it because its centralizer has
odd order. The concrete S₅ two-pentagon count completes the bound.

Source application: uniqueness of the I-invariant fives in the original
SL₂(5) centralizer factor before Aschbacher–Smith J.4.8, printed p.443.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SymmetricFive.CentralLiftPentagons
open Subgroup
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {K:Type*} [Group K] [Finite K]

omit [Finite K] in
private theorem pow_five {A:Subgroup K} (hA:Nat.card A=5) (x:K) (hx:x∈A) : x^5=1 := by
  have hh := pow_card_eq_one' (x:=(⟨x,hx⟩:A))
  rw [hA] at hh
  exact congrArg Subtype.val hh

omit [Finite K] in
private theorem map_five_card (f:K→*Equiv.Perm (Fin 5)) (hc:f.ker≤center K)
    (hcop:(Nat.card f.ker).Coprime 5) (A:Subgroup K) (hA:Nat.card A=5) :
    Nat.card (A.map f)=5 := by
  have hi : Function.Injective (f.comp A.subtype) := by
    intro x y hxy
    exact Subtype.ext (f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hc hcop hxy
      (pow_five hA x x.property) (pow_five hA y y.property))
  have he : (f.comp A.subtype).range=A.map f := by
    rw [MonoidHom.range_comp,A.range_subtype]
  rw [← he]
  exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hA

/-- Prime-five subgroups have unique lifts through a central coprime kernel. -/
theorem five_eq_of_image_eq (f:K→*Equiv.Perm (Fin 5)) (hc:f.ker≤center K)
    (hcop:(Nat.card f.ker).Coprime 5) (A B:Subgroup K) (hA:Nat.card A=5)
    (hB:Nat.card B=5) (he:A.map f=B.map f) : A=B := by
  apply eq_of_le_of_card_ge _ (by rw [hA,hB])
  intro x hx
  obtain ⟨y,hy,heq⟩ := show f x∈B.map f from he ▸ mem_map_of_mem f hx
  have hxy : x=y := f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hc hcop heq.symm
    (pow_five hA x hx) (pow_five hB y hy)
  exact hxy ▸ hy

private theorem normalized_five_inverted (A:Subgroup (Equiv.Perm (Fin 5))) (hA:Nat.card A=5)
    (v:Equiv.Perm (Fin 5)) (hv:orderOf v=2) (hn:v∈normalizer (A:Set _)) :
    ∀x∈A,v*x*v⁻¹=x⁻¹ := by
  rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one A
    (by rw [hA]; decide) v
    ((orderOf_eq_prime_iff.mp hv).1) hn with hc|hi
  · have hvc : v∈centralizer (A:Set _) := by
      intro x hx
      exact (hc x hx).eq.symm
    have hh := orderOf_dvd_natCard (⟨v,hvc⟩:centralizer (A:Set _))
    rw [← orderOf_coe,hv,Equiv.Perm.five_subgroup_centralizer_card A hA] at hh
    contradiction
  · exact hi

/-- An automorphism lifting an even involution of S₅ normalizes at most
two order-five subgroups when its map has central kernel coprime to five. -/
theorem invariant_five_card_le_two (f:K→*Equiv.Perm (Fin 5)) (hc:f.ker≤center K)
    (hcop:(Nat.card f.ker).Coprime 5) (a:MulAut K) (v:Equiv.Perm (Fin 5))
    (hv:orderOf v=2) (heven:v∈alternatingGroup (Fin 5))
    (heq:∀x:K,f (a x)=v*f x*v⁻¹) :
    Nat.card {A:Subgroup K // Nat.card A=5 ∧ A.map a.toMonoidHom=A}≤2 := by
  let imageSylow (A:Subgroup K) (hA:Nat.card A=5) : Sylow 5 (Equiv.Perm (Fin 5)) :=
    Sylow.ofCard (A.map f) (by
      rw [map_five_card f hc hcop A hA,Nat.card_eq_fintype_card,Fintype.card_perm]
      decide +kernel)
  have hinv (A:Subgroup K) (hA:Nat.card A=5) (ha:A.map a.toMonoidHom=A) :
      ∀x∈A.map f,v*x*v⁻¹=x⁻¹ := by
    apply normalized_five_inverted _ (map_five_card f hc hcop A hA) v hv
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hcomp : (MulAut.conj v).toMonoidHom.comp f=f.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (heq x).symm
    change (A.map f).map (MulAut.conj v).toMonoidHom=A.map f
    rw [map_map,hcomp,← map_map,ha]
  let F : {A:Subgroup K // Nat.card A=5 ∧ A.map a.toMonoidHom=A} →
      {P:Sylow 5 (Equiv.Perm (Fin 5)) // ∀x∈(P:Subgroup _),v*x*v⁻¹=x⁻¹} :=
    fun A => ⟨imageSylow A A.property.1,hinv A A.property.1 A.property.2⟩
  have hF : Function.Injective F := by
    intro A B hab
    apply Subtype.ext
    apply five_eq_of_image_eq f hc hcop A B A.property.1 B.property.1
    exact congrArg (fun P:Sylow 5 (Equiv.Perm (Fin 5)) => (P:Subgroup (Equiv.Perm (Fin 5))))
      (congrArg Subtype.val hab)
  have hh := Nat.card_le_card_of_injective F hF
  rwa [StarCenterGeometry.inverted_sylow_count v hv heven] at hh

/-- Once two distinct invariant fives are known, they exhaust the family. -/
theorem invariant_five_eq_or_eq (f:K→*Equiv.Perm (Fin 5)) (hc:f.ker≤center K)
    (hcop:(Nat.card f.ker).Coprime 5) (a:MulAut K) (v:Equiv.Perm (Fin 5))
    (hv:orderOf v=2) (heven:v∈alternatingGroup (Fin 5))
    (heq:∀x:K,f (a x)=v*f x*v⁻¹) (A B C:Subgroup K)
    (hA:Nat.card A=5) (hB:Nat.card B=5) (hC:Nat.card C=5)
    (ha:A.map a.toMonoidHom=A) (hb:B.map a.toMonoidHom=B) (hc':C.map a.toMonoidHom=C)
    (hne:A≠B) : C=A ∨ C=B := by
  classical
  by_contra! hn
  let X := {D:Subgroup K // Nat.card D=5 ∧ D.map a.toMonoidHom=D}
  let : Fintype X := Fintype.ofFinite X
  let x:X := ⟨A,hA,ha⟩
  let y:X := ⟨B,hB,hb⟩
  let z:X := ⟨C,hC,hc'⟩
  have hxy : x≠y := fun h => hne (congrArg Subtype.val h)
  have hzx : z≠x := fun h => hn.1 (congrArg Subtype.val h)
  have hzy : z≠y := fun h => hn.2 (congrArg Subtype.val h)
  have hcard : ({x,y,z}:Finset X).card≤2 := (Finset.card_le_univ _).trans
    ((Fintype.card_eq_nat_card).trans_le
      (invariant_five_card_le_two f hc hcop a v hv heven heq))
  simp [hxy,hzx.symm,hzy.symm] at hcard

end Theory.SpecificGroups.SymmetricFive.CentralLiftPentagons
