module
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.GroupTheory.OddCentralInvolutionLifting.Centralizers
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Odd central lifts of an inverted plane

A partial inverter of one generator forces the full preimage of an odd
prime plane to be abelian. Commutation with any lift of a total inverter
then defines a homomorphism on that preimage. It kills the central kernel
and induces inverse squaring on the plane. Inverting this automorphism
gives a section of the original quotient map.

If the plane centralizes a nonidentity involution, its section lies in the
centralizer of the unique square-one lift. A central kernel element of the
plane's prime order supplies an independent third direction there.

This is the central-extension calculation for the initial defining-center
reduction in Aschbacher–Smith, Lemma A.2.17, printed pp.39–40. The concrete
F₄ root plane and torus elements are supplied by the source consumer.
-/

public noncomputable section
namespace OddCentralInvertedPlane
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {G Q : Type*} [Group G] [Group Q]

/-- Partial inversion makes the full plane preimage abelian; a total
inverter then splits off the prescribed plane from the odd central kernel. -/
theorem exists_section [Finite G] [Finite Q] (f : G →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hko : Odd (Nat.card f.ker))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (E : Subgroup Q) (hEp : ∀ a : E, a ^ p = 1) (hEc : Nat.card E = p ^ 2)
    (x y a t : Q) (hE : closure ({x,y} : Set Q) = E)
    (hxy : Commute x y) (hax : a * x * a⁻¹ = x⁻¹) (hay : Commute a y)
    (ht : t ^ 2 = 1) (htE : ∀ v ∈ E, t * v * t⁻¹ = v⁻¹) :
    ∃ s : E →* G, f.comp s = E.subtype := by
  have hxE : x ∈ E := hE ▸ subset_closure (by simp)
  have hx : x ^ p = 1 := congrArg Subtype.val (hEp ⟨x,hxE⟩)
  obtain ⟨u, hu⟩ := hf x
  obtain ⟨v, hv⟩ := hf y
  have huv := CentralExtension.commute_lifts_of_partial_inversion
    f hf hk x y a hp.coprime_two_right hx hxy hax hay u v hu hv
  let U := E.comap f
  have hUc : IsMulCommutative U :=
    CentralExtension.isMulCommutative_comap_of_pair_lifts f hk E u v huv (by simpa [hu,hv] using hE)
  let q : U →* E := f.subgroupComap E
  have hqs : Function.Surjective q := f.subgroupComap_surjective_of_surjective E hf
  let : CommGroup U := IsMulCommutative.instCommGroup
  have : IsMulCommutative E := ⟨⟨fun x y => by
    obtain ⟨u, rfl⟩ := hqs x
    obtain ⟨v, rfl⟩ := hqs y
    rw [← map_mul, mul_comm, map_mul]⟩⟩
  let : CommGroup E := IsMulCommutative.instCommGroup
  obtain ⟨r, hfr, _⟩ := OddCentralLifting.exists_involution_lift f hko hf t ht
  let α : U →* U := ((MulAut.conj r).toMonoidHom.comp U.subtype).codRestrict U (by
    intro w
    change f (r * (w : G) * r⁻¹) ∈ E
    rw [map_mul, map_mul, map_inv, hfr, htE _ w.property]
    exact E.inv_mem w.property)
  let δ : U →* U := α * invMonoidHom
  have hkill : q.ker ≤ δ.ker := by
    intro w hw
    have hwk : (w : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
    apply Subtype.ext
    change r * (w : G) * r⁻¹ * (w : G)⁻¹ = 1
    rw [mem_center_iff.mp (hk hwk) r, mul_inv_cancel_right, mul_inv_cancel]
  let d : E →* U := q.liftOfSurjective hqs ⟨δ, hkill⟩
  have hd (w : U) : d (q w) = δ w := q.liftOfRightInverse_comp_apply _ _ _ w
  let b : E →* E := (powMonoidHom 2).comp invMonoidHom
  have hdb (w : E) : q (d w) = b w := by
    obtain ⟨w, rfl⟩ := hqs w
    rw [hd]
    apply Subtype.ext
    change f (r * (w : G) * r⁻¹ * (w : G)⁻¹) = (f w)⁻¹ ^ 2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hfr, htE _ w.property, pow_two]
  have hEo : Odd (Nat.card E) := by rw [hEc]; exact hp.pow
  have hb : Function.Bijective b :=
    (powCoprime hEo.coprime_two_right).bijective.comp inv_involutive.bijective
  let e : E ≃* E := MulEquiv.ofBijective b hb
  refine ⟨U.subtype.comp (d.comp e.symm.toMonoidHom), ?_⟩
  apply MonoidHom.ext
  intro w
  exact congrArg Subtype.val ((hdb (e.symm w)).trans (e.apply_symm_apply w))

/-- A defining-prime central element adds an independent third direction
inside the original lifted involution centralizer. -/
theorem rank_three_of_kernel_divisible [Finite G] [Finite Q] (f : G →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hko : Odd (Nat.card f.ker))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (E : Subgroup Q) (hEp : ∀ a : E, a ^ p = 1) (hEc : Nat.card E = p ^ 2)
    (x y a t z : Q) (hE : closure ({x,y} : Set Q) = E)
    (hxy : Commute x y) (hax : a * x * a⁻¹ = x⁻¹) (hay : Commute a y)
    (ht : t ^ 2 = 1) (htE : ∀ v ∈ E, t * v * t⁻¹ = v⁻¹)
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1) (hEz : E ≤ centralizer ({z} : Set Q))
    (hdiv : p ∣ Nat.card f.ker) :
    ∃ z' : G, z' ≠ 1 ∧ z' ^ 2 = 1 ∧ 3 ≤ primeRank p (centralizer ({z'} : Set G)) := by
  obtain ⟨s,hs⟩ := exists_section f hf hk hko hp E hEp hEc x y a t hE hxy hax hay ht htE
  have hsf (v : E) : f (s v) = v.val := DFunLike.congr_fun hs v
  obtain ⟨z',hzf,hz'2⟩ := OddCentralLifting.exists_involution_lift f hko hf z hz2
  have hz' : z' ≠ 1 := by intro h; apply hz; rw [← hzf,h,map_one]
  let Z := centralizer ({z'} : Set G)
  have hsZ (v : E) : s v ∈ Z := by
    apply mem_centralizer_singleton_iff.mpr
    apply OddCentralLifting.centralizes_of_image f hko hk hz'2
    simpa only [hsf,hzf] using (mem_centralizer_singleton_iff.mp (hEz v.property))
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' p hdiv
  let C := zpowers (w : G)
  have hCK : C ≤ f.ker := zpowers_le.mpr w.property
  have hCc : C ≤ center G := hCK.trans hk
  have hCcard : Nat.card C = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw]
  have hCZ : C ≤ Z := hCc.trans (center_le_centralizer _)
  have hEcomm : IsMulCommutative E := by
    have : IsMulCommutative (closure ({x,y} : Set Q)) := by
      apply isMulCommutative_closure
      intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hxy.eq
      · exact hxy.eq.symm
      · rfl
    exact hE ▸ this
  let : IsMulCommutative E := hEcomm
  let : CommGroup E := IsMulCommutative.instCommGroup
  let : CommGroup C := IsMulCommutative.instCommGroup
  let g : E × C →* Z :=
    (s.noncommCoprod C.subtype (fun u v => (mem_center_iff.mp (hCc v.property) (s u)))).codRestrict _
      (fun v => Z.mul_mem (hsZ v.1) (hCZ v.2.property))
  have hgi : Function.Injective g := by
    rintro ⟨u,v⟩ ⟨u',v'⟩ h
    have hh : s u * (v : G) = s u' * (v' : G) := congrArg Subtype.val h
    have he : u = u' := by
      apply Subtype.ext
      have he := congrArg f hh
      simpa only [map_mul, hsf, MonoidHom.mem_ker.mp (hCK v.property),
        MonoidHom.mem_ker.mp (hCK v'.property), mul_one] using he
    subst u'
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel hh))
  have hgpow : ∀ v : E × C, v ^ p = 1 := by
    intro v
    apply Prod.ext
    · change v.1 ^ p = 1
      exact hEp v.1
    · change v.2 ^ p = 1
      simpa only [hCcard] using (pow_card_eq_one' (x := v.2))
  have hgcard : Nat.card (E × C) = p ^ 3 := by
    rw [Nat.card_prod,hEc,hCcard]
    ring
  exact ⟨z',hz',hz'2,primeRank_ge_of_elementary_embedding hgpow hgcard g hgi⟩

end OddCentralInvertedPlane
