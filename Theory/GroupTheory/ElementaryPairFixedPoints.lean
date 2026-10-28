module
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
public import Theory.GroupTheory.DerivedCenterAbelianPair
/-!
# Fixed points and displacements of an elementary pair

An involution exchanges two normal elementary factors whose intersection is
central. If it fixes that intersection pointwise, comparison of the two
factorizations of a fixed element forces its square to be one. When all
involutions lie in the factors, every fixed element lies in their intersection.
Independently, a conjugate abelian generating pair puts the whole derived
group inside its displacement subgroup.

Source application: Aschbacher–Smith, Lemma 2.4.14(1), printed p.533.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem elementary_pair_fixed_le_intersection
    (R U V : Subgroup G) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hgen : U ⊔ V = R) (hRU : R ≤ normalizer (U : Set G))
    (hRV : R ≤ normalizer (V : Set G))
    (hcent : U ⊓ V ≤ centralizer (R : Set G))
    (a : MulAut G) (ha : ∀ x, a (a x) = x)
    (hUV : U.map a.toMonoidHom = V) (hVU : V.map a.toMonoidHom = U)
    (hZ : ∀ z ∈ U ⊓ V, a z = z)
    (hinv : ∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V) :
    ∀ r ∈ R, a r = r → r ∈ U ⊓ V := by
  intro r hr hrf
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hp : r ∈ (U : Set G) * (V : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U V (hVR.trans hRU), hgen]
    exact hr
  obtain ⟨u,hu,v,hv,rfl⟩ := hp
  have hau : a u ∈ V := hUV ▸ mem_map_of_mem a.toMonoidHom hu
  have hav : a v ∈ U := hVU ▸ mem_map_of_mem a.toMonoidHom hv
  have hu2 : u*u=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) u hu
  have hv2 : v*v=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv
  have hau2 : a u*a u=1 := by rw [←map_mul,hu2,map_one]
  have hav2 : a v*a v=1 := by rw [←map_mul,hv2,map_one]
  have hrf' : a u * a v = u*v := by simpa only [map_mul] using hrf
  let z := u * a v
  have hzU : z ∈ U := U.mul_mem hu hav
  have hzV : z ∈ V := by
    have hn := (mem_normalizer_iff.mp (hRV (hUR hu)) (a u)).mp hau
    have hi : u⁻¹=u := inv_eq_of_mul_eq_one_left hu2
    have he : z = (u * a u * u⁻¹) * v := by
      dsimp [z]
      rw [hi]
      calc
        u*a v = u*(a u*(a u*a v)) := by rw [←mul_assoc (a u),hau2,one_mul]
        _ = (u*a u*u)*v := by rw [hrf']; group
    rw [he]
    exact V.mul_mem hn hv
  have hzf : a z = z := hZ z ⟨hzU,hzV⟩
  have hzcomm : ∀ w ∈ R, Commute z w := by
    intro w hw
    exact ((mem_centralizer_iff.mp (hcent ⟨hzU,hzV⟩)) w hw).symm
  have hz2 : z*z=1 := by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) z hzU
  have hvform : v = a u*z := by
    have he : a u*v=z := by simpa only [z,map_mul,ha] using hzf
    calc v = a u*(a u*v) := by rw [←mul_assoc,hau2,one_mul]
         _ = a u*z := by rw [he]
  have hrform : u*v=(u*a u)*z := by rw [hvform,mul_assoc]
  have hauu : Commute u (a u) := by
    apply mul_right_cancel (b:=z)
    calc (u*a u)*z = u*v := hrform.symm
         _ = a (u*v) := hrf.symm
         _ = (a u*u)*z := by rw [hrform,map_mul,map_mul,ha,hzf]
  have hr2 : (u*v)^2=1 := by
    rw [hrform, (hzcomm (u*a u) (R.mul_mem (hUR hu) (hVR hau))).symm.mul_pow]
    rw [hauu.mul_pow]
    simp only [pow_two,hu2,hau2,hz2,mul_one]
  rcases hinv (u*v) hr hr2 with hU | hV
  · refine ⟨hU,?_⟩
    have hh : a (u*v) ∈ V := hUV ▸ mem_map_of_mem a.toMonoidHom hU
    rwa [hrf] at hh
  · refine ⟨?_,hV⟩
    have hh : a (u*v) ∈ U := hVU ▸ mem_map_of_mem a.toMonoidHom hV
    rwa [hrf] at hh

/-- Exchanging an abelian generating pair forces the derived group into
its displacement subgroup. -/
theorem derived_le_commutator_of_conjugate_abelian_pair
    (R U : Subgroup G) [IsMulCommutative U] (t : G)
    (hgen : U ⊔ U.map (MulAut.conj t).toMonoidHom = R) :
    ⁅R,R⁆ ≤ ⁅R,zpowers t⁆ := by
  let K := ⁅R,zpowers t⁆
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hRK : R ≤ normalizer (K : Set G) := normalizer_commutator_ge_left R (zpowers t)
  have hVR : U.map (MulAut.conj t).toMonoidHom ≤ K ⊔ U := by
    rintro v ⟨u,hu,rfl⟩
    have hc : ⁅t,u⁆ ∈ K := by
      change ⁅t,u⁆ ∈ ⁅R,zpowers t⁆
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_zpowers t) (hUR hu)
    have he : (MulAut.conj t) u = ⁅t,u⁆*u := by
      simp only [MulAut.conj_apply,commutatorElement_def]
      group
    change (MulAut.conj t) u ∈ K ⊔ U
    rw [he]
    exact mul_mem_sup hc hu
  have hcover : R ≤ K ⊔ U := by
    rw [←hgen]
    exact sup_le le_sup_right hVR
  exact (commutator_mono hcover hcover).trans
    (commutator_sup_le_of_normalized_derived K U (hUR.trans hRK)
      (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le))

/-- The center is strictly smaller than the displacement subgroup when
it lies in the derived group and the two abelian factors are distinct. -/
theorem center_lt_commutator_of_conjugate_abelian_pair
    (R U Z : Subgroup G) [IsMulCommutative U] (t : G)
    (hgen : U ⊔ U.map (MulAut.conj t).toMonoidHom = R)
    (hZ : Z ≤ ⁅R,R⁆) (hZU : Z ≤ U)
    (hne : ¬U.map (MulAut.conj t).toMonoidHom ≤ U) :
    Z < ⁅R,zpowers t⁆ := by
  refine lt_iff_le_not_ge.mpr ⟨hZ.trans
    (derived_le_commutator_of_conjugate_abelian_pair R U t hgen), ?_⟩
  intro hle
  apply hne
  rintro v ⟨u,hu,rfl⟩
  have hc : ⁅t,u⁆ ∈ ⁅R,zpowers t⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_zpowers t) ((le_sup_left.trans_eq hgen) hu)
  have he : (MulAut.conj t) u = ⁅t,u⁆*u := by
    simp only [MulAut.conj_apply,commutatorElement_def]
    group
  change (MulAut.conj t) u ∈ U
  rw [he]
  exact U.mul_mem (hZU (hle hc)) hu
end Subgroup
