module

public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Theory.GroupAction.PrimeGroupFixedImage

/-!
# A normal Sylow-centric subgroup and the prime-complement quotient

If a normal p-subgroup contains its centralizer in a Sylow p-subgroup,
its full centralizer has a central Sylow p-subgroup. Burnside transfer
gives a normal p-complement in that centralizer. Its p'-core lies in
the ambient p'-core, so its image in the quotient is a normal p-group.
Coprime centralizer lifting then makes the quotient's p-core
self-centralizing.
-/

public section
open Subgroup

/-- A normal subgroup self-centralizing in a Sylow subgroup forces
characteristic p after quotienting the ambient p'-core. -/
theorem Sylow.centralizer_pCore_quotient_pPrimeCore_le_of_normal_centric
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (S : Sylow p A) (U : Subgroup A) [U.Normal]
    (hUS : U ≤ (S : Subgroup A))
    (hc : (S : Subgroup A) ⊓ centralizer (U : Set A) ≤ U) :
    centralizer (pCore p (A ⧸ pPrimeCore p A) : Set (A ⧸ pPrimeCore p A)) ≤
      pCore p (A ⧸ pPrimeCore p A) := by
  let C := centralizer (U : Set A)
  have hUp : IsPGroup p U := S.isPGroup'.of_injective (inclusion hUS) (inclusion_injective hUS)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal C
  have hRcentral : (R : Subgroup C) ≤ center C := by
    intro x hx
    have hxS : (x : A) ∈ (S : Subgroup A) := by
      have hxSC : (x : C) ∈ (S : Subgroup A).subgroupOf C := by
        rw [← hR]
        exact hx
      exact Subgroup.mem_subgroupOf.mp hxSC
    have hxU : (x : A) ∈ U := hc ⟨hxS,x.property⟩
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact (mem_centralizer_iff.mp y.property _ hxU).symm
  have hcomp : HasNormalPComplement p C := by
    apply exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p R
    intro x hx
    refine ⟨le_normalizer hx, ?_⟩
    intro y hy
    exact mem_center_iff.mp (hRcentral hx) y
  have hquot : IsPGroup p (C ⧸ pPrimeCore p C) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement p C hcomp
  let O := pPrimeCore p A
  let q := QuotientGroup.mk' O
  let f : C →* C.map q := (q.comp C.subtype).codRestrict (C.map q)
    (fun x => mem_map_of_mem q x.property)
  have hf : Function.Surjective f := by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨⟨x,hx⟩,rfl⟩
  have hkill : pPrimeCore p C ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr
      (pPrimeCore_map_subtype_le_pPrimeCore_of_normal p C (mem_map_of_mem C.subtype hx))
  let fbar := QuotientGroup.lift (pPrimeCore p C) f hkill
  have hfp : IsPGroup p (C.map q) := hquot.of_surjective fbar
    (QuotientGroup.lift_surjective_of_surjective _ f hf hkill)
  have hCcore : C.map q ≤ pCore p (A ⧸ O) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective O),hfp⟩
  have hUcore : U.map q ≤ pCore p (A ⧸ O) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective O),hUp.map q⟩
  have hker : ¬p ∣ Nat.card q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  have hCimage := centralizer_map_of_prime_free_kernel q
    (QuotientGroup.mk'_surjective O) hker U hUp
  exact (centralizer_le hUcore).trans (hCimage ▸ hCcore)
