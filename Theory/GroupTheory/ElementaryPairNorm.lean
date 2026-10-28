module
public import Theory.GroupTheory.ElementaryPairFixedPoints
public import Mathlib.GroupTheory.Index
/-!
# Central norms and conjugacy for an elementary pair

For an involution exchanging two elementary factors and fixing their center,
the diagonal commutator is a homomorphism. Its kernel is the intersection;
the square-order relation makes it surjective onto the center. Norm elements
then conjugate the involution to every central translate, and comparison of
the two factors extends conjugacy to all involutions of the outside coset.

Source application: Aschbacher–Smith, Lemma 2.4.14(1), printed p.533.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem elementary_pair_norm_surjective
    (R U V Z : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hUR : U ≤ R) (hVR : V ≤ R) (hZ : U ⊓ V = Z)
    (hder : ⁅R,R⁆ ≤ Z) (hcent : Z ≤ centralizer (R : Set G))
    (a : MulAut G) (ha : ∀ x, a (a x) = x)
    (hUV : U.map a.toMonoidHom = V)
    (hfix : ∀ z ∈ Z, a z = z)
    (hinv : ∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V)
    (hcard : Nat.card U = Nat.card Z ^ 2) :
    ∀ z ∈ Z, ∃ u ∈ U, ⁅u,a u⁆=z := by
  have hZU : Z ≤ U := hZ ▸ inf_le_left
  have hau {u : G} (hu : u ∈ U) : a u ∈ V := hUV ▸ mem_map_of_mem a.toMonoidHom hu
  have hcross {x y : G} (hx : x ∈ R) (hy : y ∈ R) : ⁅x,y⁆ ∈ Z :=
    hder (commutator_mem_commutator hx hy)
  have hcomm {x y r : G} (hx : x ∈ R) (hy : y ∈ R) (hr : r ∈ R) :
      Commute r ⁅x,y⁆ := mem_centralizer_iff.mp (hcent (hcross hx hy)) r hr
  have hleft {x y z : G} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
      ⁅x*y,z⁆=⁅x,z⁆*⁅y,z⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, (hcomm hy hz hx).eq, mul_inv_cancel_right]
    exact (hcomm hy hz (commutator_mem_commutator hx hz |> commutator_le_self R)).symm.eq
  have hright {x y z : G} (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
      ⁅x,y*z⁆=⁅x,y⁆*⁅x,z⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅x,y⁆*(y*⁅x,z⁆)*y⁻¹ := by group
      _ = ⁅x,y⁆*⁅x,z⁆ := by rw [(hcomm hx hz hy).eq];group
  have hswap (u v : U) : ⁅(v:G),a u⁆=⁅(u:G),a v⁆⁻¹ := by
    have hf := hfix _ (hcross (hUR u.property) (hVR (hau v.property)))
    rw [map_commutatorElement,ha] at hf
    rw [←hf,commutatorElement_inv]
  let q : U →* G := {
    toFun u := ⁅(u:G),a u⁆
    map_one' := by simp
    map_mul' u v := by
      change ⁅(u:G)*(v:G),a ((u:G)*(v:G))⁆=_
      rw [map_mul,hleft (hUR u.property) (hUR v.property)
        (R.mul_mem (hVR (hau u.property)) (hVR (hau v.property))),
        hright (hUR u.property) (hVR (hau u.property)) (hVR (hau v.property)),
        hright (hUR v.property) (hVR (hau u.property)) (hVR (hau v.property)),hswap u v]
      group }
  have hk : q.ker = Z.subgroupOf U := by
    ext u
    change ⁅(u:G),a u⁆=1 ↔ (u:G) ∈ Z
    constructor
    · intro huq
      have hc := commutatorElement_eq_one_iff_commute.mp huq
      have hu2 : (u:G)^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (u:G) u.property
      have hau2 : (a u)^2=1 := by rw [←map_pow,hu2,map_one]
      have hn2 : ((u:G)*a u)^2=1 := by rw [hc.mul_pow,hu2,hau2,one_mul]
      have huV : (u:G) ∈ V := by
        rcases hinv _ (R.mul_mem (hUR u.property) (hVR (hau u.property))) hn2 with hnu | hnv
        · have hauU : a u ∈ U := (U.mul_mem_cancel_left u.property).mp hnu
          have hha : a (a u) ∈ V := hau hauU
          rwa [ha] at hha
        · exact (V.mul_mem_cancel_right (hau u.property)).mp hnv
      exact hZ ▸ (show (u:G) ∈ U ⊓ V from ⟨u.property,huV⟩)
    · intro huz
      rw [hfix u huz]
      exact commutatorElement_self _
  have hr : q.range ≤ Z := by
    rintro z ⟨u,rfl⟩
    exact hcross (hUR u.property) (hVR (hau u.property))
  have hkcard : Nat.card q.ker = Nat.card Z := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv
  have hcount := q.ker.card_mul_index
  rw [index_ker,hkcard,hcard] at hcount
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have he : q.range = Z := eq_of_le_of_card_ge hr (by nlinarith)
  intro z hz
  obtain ⟨u,hu⟩ := he.symm ▸ hz
  exact ⟨u,u.property,hu⟩

/-- Norm surjectivity realizes every central translate of a swapping
involution by a conjugator in its displacement subgroup. -/
theorem elementary_pair_conjugate_central_translate
    (R U Z : Subgroup G) [IsElementaryAbelian 2 U] (t : G) (ht : t^2=1)
    (hUR : U ≤ R) (hVR : U.map (MulAut.conj t).toMonoidHom ≤ R)
    (hZ : U ⊓ U.map (MulAut.conj t).toMonoidHom = Z)
    (hder : ⁅R,R⁆ ≤ Z) (hcent : Z ≤ centralizer (R : Set G))
    (htZ : t ∈ centralizer (Z : Set G))
    (hinv : ∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ U.map (MulAut.conj t).toMonoidHom)
    (hcard : Nat.card U = Nat.card Z ^ 2) :
    ∀ z ∈ Z, ∃ k ∈ ⁅R,zpowers t⁆, k*t*k⁻¹=t*z := by
  let a := MulAut.conj t
  have htt : t*t=1 := by simpa only [pow_two] using ht
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left htt
  have ha (x : G) : a (a x)=x := by
    change t*(t*x*t⁻¹)*t⁻¹=x
    rw [hti]
    calc t*(t*x*t)*t=(t*t)*x*(t*t) := by group
         _ = x := by rw [htt,one_mul,mul_one]
  have hfix (z : G) (hz : z ∈ Z) : a z=z := by
    change t*z*t⁻¹=z
    rw [←mem_centralizer_iff.mp htZ z hz,mul_inv_cancel_right]
  let : IsElementaryAbelian 2 (U.map a.toMonoidHom) := IsElementaryAbelian.map a.toMonoidHom
  intro z hz
  obtain ⟨u,hu,huq⟩ := elementary_pair_norm_surjective R U (U.map a.toMonoidHom) Z
    hUR hVR hZ hder hcent a ha rfl hfix hinv hcard z hz
  have hu2 : u*u=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) u hu
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left hu2
  have haui : (a u)⁻¹=a u := by rw [←map_inv,hui]
  let k := u*a u
  have hk : k ∈ ⁅R,zpowers t⁆ := by
    have he : k=⁅u,t⁆ := by
      change u*(t*u*t⁻¹)=u*t*u⁻¹*t⁻¹
      rw [hui]
      group
    rw [he]
    exact commutator_mem_commutator (hUR hu) (mem_zpowers t)
  refine ⟨k,hk,?_⟩
  have he : ⁅k,t⁆=z := by
    calc
      ⁅k,t⁆ = k*a k⁻¹ := by change k*t*k⁻¹*t⁻¹=k*(t*k⁻¹*t⁻¹);group
      _ = (u*a u)*(u*a u) := by simp only [k,mul_inv_rev,map_mul,ha,hui,haui]
      _ = ⁅u,a u⁆ := by rw [commutatorElement_def,hui,haui];group
      _ = z := huq
  have hconj : k*t*k⁻¹=z*t := by
    calc k*t*k⁻¹ = ⁅k,t⁆*t := by rw [commutatorElement_def];group
         _ = z*t := by rw [he]
  exact hconj.trans (mem_centralizer_iff.mp htZ z hz)

omit [Finite G] in
/-- Once central translates fuse, factor comparison fuses every involution
in the outside coset. -/
theorem elementary_pair_conjugate_involution_coset
    (R U V Z : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (t : G) (ht : t^2=1) (htR : t ∈ normalizer (R : Set G))
    (hgen : U ⊔ V = R) (hRU : R ≤ normalizer (U : Set G))
    (hUV : U.map (MulAut.conj t).toMonoidHom = V)
    (hZ : U ⊓ V = Z) (hcent : Z ≤ centralizer (R : Set G))
    (hcentral : ∀ z ∈ Z, ∃ k ∈ ⁅R,zpowers t⁆, k*t*k⁻¹=t*z) :
    ∀ r ∈ R, (t*r)^2=1 → ∃ k ∈ R, k*t*k⁻¹=t*r := by
  let a := MulAut.conj t
  have htt : t*t=1 := by simpa only [pow_two] using ht
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left htt
  have hau {u : G} (hu : u ∈ U) : a u ∈ V := hUV ▸ mem_map_of_mem a.toMonoidHom hu
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hKR : ⁅R,zpowers t⁆ ≤ R :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr htR)
  intro r hr htr
  have hp : r ∈ (U : Set G)*(V : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U V (hVR.trans hRU),hgen]
    exact hr
  obtain ⟨u,hu,v,hv,rfl⟩ := hp
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) u hu)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv)
  have haui : (a u)⁻¹=a u := by rw [←map_inv,hui]
  have havU : a v ∈ U := by
    obtain ⟨w,hw,he⟩ := (show v ∈ U.map (MulAut.conj t).toMonoidHom from hUV.symm ▸ hv)
    have he' : t*w*t⁻¹=v := he
    have hav : a v=w := by
      change t*v*t⁻¹=w
      rw [←he',hti]
      calc t*(t*w*t)*t=(t*t)*w*(t*t) := by group
           _ = w := by rw [htt,one_mul,mul_one]
    exact hav.symm ▸ hw
  have haf : a u*a v=v*u := by
    have hprod : (t*(u*v))*(t*(u*v))=1 := by simpa only [pow_two] using htr
    have he : t*(u*v)*t=(u*v)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa only [mul_assoc] using hprod
    rw [←map_mul]
    change t*(u*v)*t⁻¹=v*u
    simpa only [hti,mul_inv_rev,hui,hvi] using he
  let z := a u*v
  have hzV : z ∈ V := V.mul_mem (hau hu) hv
  have hzU : z ∈ U := by
    have he : z=a v*u := by
      apply mul_left_cancel (a:=a u)
      change a u*(a u*v)=a u*(a v*u)
      have hau2 : a u*a u=1 := by simpa only [haui] using inv_mul_cancel (a u)
      have hu2 : u*u=1 := by simpa only [hui] using inv_mul_cancel u
      calc
        a u*(a u*v)=(a u*a u)*v := by group
        _=v := by rw [hau2,one_mul]
        _=(v*u)*u := by rw [mul_assoc,hu2,mul_one]
        _=(a u*a v)*u := by rw [haf]
        _=a u*(a v*u) := by group
    rw [he]
    exact U.mul_mem havU hu
  have hz : z ∈ Z := hZ ▸ (show z ∈ U ⊓ V from ⟨hzU,hzV⟩)
  obtain ⟨w,hwK,hw⟩ := hcentral z hz
  have hwR := hKR hwK
  have hzc : Commute z (a u) := (mem_centralizer_iff.mp (hcent hz) (a u) (hVR (hau hu))).symm
  refine ⟨a u*w,R.mul_mem (hVR (hau hu)) hwR,?_⟩
  calc
    (a u*w)*t*(a u*w)⁻¹ = a u*(w*t*w⁻¹)*(a u)⁻¹ := by group
    _ = a u*(t*z)*(a u)⁻¹ := by rw [hw]
    _ = t*(u*v) := by
      have hmove : a u*t=t*u := by
        change (t*u*t⁻¹)*t=t*u
        group
      have hau2 : a u*a u=1 := by simpa only [haui] using inv_mul_cancel (a u)
      calc
        a u*(t*z)*(a u)⁻¹ = (a u*t)*(z*a u) := by rw [haui];group
        _ = (t*u)*(a u*z) := by rw [hmove,hzc.eq]
        _ = t*(u*((a u*a u)*v)) := by dsimp [z];group
        _ = t*(u*v) := by rw [hau2,one_mul]
end Subgroup
