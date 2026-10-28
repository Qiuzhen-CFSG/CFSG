module
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PResidual.CentralSylowCharacter
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Cyclic residual images with a centralized kernel

Let N be the normal closure of a two-subgroup R in a finite group. If R
centralizes the kernel of a homomorphism and the image of O²(N) is cyclic,
that homomorphism is faithful on O²(N).

The kernel centralizes N. A cyclic central quotient makes O²(N) abelian,
and two-perfectness makes it odd. Normal generation makes N p-perfect for
every odd prime p. Its Sylow p-subgroups lie in the abelian residual, so
transfer kills the central kernel at every such prime.

Source application: the cyclic-image paragraph of Aschbacher--Smith
15.2.3(1), printed p.1105, on the literal quotient M/O₂(M).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A normal closure of a two-subgroup has no nontrivial odd-prime-group quotient. -/
theorem isPPerfect_normalClosure_of_twoGroup (R : Subgroup G) (hR : IsPGroup 2 R)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    IsPPerfect p (normalClosure (R : Set G)) := by
  let N := normalClosure (R : Set G)
  let K := (pResidual p N).map N.subtype
  have hKn : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    exact (show (⊤ : Subgroup G) ≤ normalizer (N : Set G) from le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image N (pResidual p N))
  let : K.Normal := hKn
  have hRK : R ≤ K := by
    intro r hr
    let a : N := ⟨r, le_normalClosure hr⟩
    have hcop : Nat.Coprime p (orderOf a) := by
      have hh := hR.orderOf_coprime ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm)
        (⟨r,hr⟩ : R)
      rw [← Subgroup.orderOf_coe] at hh
      rw [← Subgroup.orderOf_coe]
      exact hh.symm
    exact ⟨a, mem_pResidual_of_orderOf_coprime hcop, rfl⟩
  have hNK : N ≤ K := normalClosure_le_normal hRK
  apply (pResidual_eq_top_iff p N).mp
  apply top_unique
  intro n _
  obtain ⟨a,ha,he⟩ := hNK n.property
  exact (Subtype.ext he : a = n) ▸ ha

private theorem normalClosure_center_residual_disjoint
    (R : Subgroup G) (hR : IsPGroup 2 R)
    [IsMulCommutative (pResidual 2 (normalClosure (R : Set G)))] :
    Disjoint (center (normalClosure (R : Set G)))
      (pResidual 2 (normalClosure (R : Set G))) := by
  let N := normalClosure (R : Set G)
  let E := pResidual 2 N
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hodd : Nat.Coprime 2 (Nat.card E) :=
    coprime_card_of_isPPerfect_commGroup (isPPerfect_pResidual 2)
  let K := center N ⊓ E
  have hcard : Nat.card K = 1 := by
    by_contra hne
    obtain ⟨p,hp,hpK⟩ := Nat.exists_prime_and_dvd hne
    let : Fact p.Prime := ⟨hp⟩
    have hpE : p ∣ Nat.card E := hpK.trans (card_dvd_of_le (show K ≤ E from inf_le_right))
    have hp2 : p ≠ 2 := by
      intro he
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hodd) (he ▸ hpE)
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' p hpK
    let Z := zpowers (z : N)
    have hZp : IsPGroup p Z := by
      apply IsPGroup.of_card (n := 1)
      simpa only [Z,Nat.card_zpowers,orderOf_coe,pow_one] using hz
    obtain ⟨P,hZP⟩ := hZp.exists_le_sylow
    have hPE : (P : Subgroup N) ≤ E := by
      intro a ha
      apply mem_pResidual_of_orderOf_coprime
      have hh := P.isPGroup'.orderOf_coprime
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) (⟨a,ha⟩ : P)
      rw [← orderOf_coe] at hh
      exact hh.symm
    let : IsMulCommutative P := .of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (hPE ha) (hPE hb)
    let : CommGroup P := IsMulCommutative.instCommGroup
    let x : P := ⟨(z : N),hZP (mem_zpowers _)⟩
    have hres : (x : N) ∈ pResidual p N := by
      rw [(pResidual_eq_top_iff p N).mpr (isPPerfect_normalClosure_of_twoGroup R hR hp2)]
      trivial
    have hx := P.character_eq_one_of_central_mem_pResidual (MonoidHom.id P)
      P.isPGroup' x z.property.1 hres
    have hz1 : z = 1 := Subtype.ext (congrArg (fun a : P => (a : N)) hx)
    have hh : p = 1 := hz.symm.trans (by rw [hz1,orderOf_one])
    exact hp.ne_one hh
  exact disjoint_iff.mpr (card_eq_one.mp hcard)

/-- A cyclic residual image is faithful when the two-subgroup generators centralize the kernel. -/
theorem disjoint_twoResidual_normalClosure_ker_of_cyclic_image
    {D : Type*} [Group D] (f : G →* D) (R : Subgroup G) (hR : IsPGroup 2 R)
    (hc : R ≤ centralizer (f.ker : Set G))
    [IsCyclic (((pResidual 2 (normalClosure (R : Set G))).map
      (normalClosure (R : Set G)).subtype).map f)] :
    Disjoint ((pResidual 2 (normalClosure (R : Set G))).map
      (normalClosure (R : Set G)).subtype) f.ker := by
  let N := normalClosure (R : Set G)
  let E := pResidual 2 N
  let g := f.comp N.subtype
  have hNC : N ≤ centralizer (f.ker : Set G) := normalClosure_le_normal hc
  have hcenter (x : N) (hx : g x = 1) : x ∈ center N := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hNC y.property _ hx).symm
  let e := g.subgroupMap E
  let : IsCyclic (E.map g) := by
    change IsCyclic (E.map (f.comp N.subtype))
    rw [← map_map]
    infer_instance
  have hec : e.ker ≤ center E := by
    intro x hx
    have hxg : g (x : N) = 1 := congrArg Subtype.val (show e x = 1 from hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hcenter x hxg) y)
  let : IsMulCommutative E := e.isMulCommutative_of_isCyclic_of_ker_le_center hec
  have hd := normalClosure_center_residual_disjoint R hR
  apply disjoint_def.mpr
  rintro z ⟨x,hx,rfl⟩ hz
  have he : x = 1 := disjoint_def.mp hd (hcenter x hz) hx
  exact congrArg Subtype.val he
end Subgroup
