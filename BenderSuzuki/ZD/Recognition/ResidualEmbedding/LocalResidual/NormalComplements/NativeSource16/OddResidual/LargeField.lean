module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Nonunitary
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Torus.NinthRoots
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.NoBorel.CarrierTransport
/-!
# Exclusion of paired fields larger than the smallest field

The actual paired square-field tori supply a noncyclic odd residual in the
circle of tuv. The corrected change of distinguished base recognizes this
circle as a unitary model. If the square-root field order plus one has a
prime divisor other than three, the unitary torus-normalizer quotient makes
the residual cyclic. Otherwise it is divisible by nine; two equivariantly
transported torus witnesses of order nine lie in the same cyclic commutator
torus, contradicting their opposite actions. All model and no-Borel inputs
are discharged on the original circle and the original chosen Sylow.

Source: GLS IV, Chapter 2, Proposition 16.5. This replaces the invalid
original-z containment in the last paragraph on printed page 86.
-/

noncomputable section
namespace BenderSuzuki.ZD.Source16OddResidual
open Subgroup Theory.GroupTheory PFAppendixIII OddInvolutionFrattini NativeSource16
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
public theorem paired_tori_false_of_large_field
    {t u v : G} (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M) (ht : t∈Z) (htM : t∉M)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W=4)
    (hWD : W≤residualPairStabilizer M t) (hWt : W≤centralizer ({t}:Set G))
    (hu : u∈W) (hv : v∈W) (hWgen : W=zpowers u⊔zpowers v)
    (hui : PFAppendixIII.IsInvolution u) (Tu Tv : Subgroup G) {m : ℕ} (hm : 1<m)
    (hTuc : IsCyclic Tu) (hTvc : IsCyclic Tv)
    (hTuo : Nat.card Tu=2^(2*m)-1) (hTvo : Nat.card Tv=2^(2*m)-1)
    (hTuD : Tu≤residualPairStabilizer M t) (hTvD : Tv≤residualPairStabilizer M t)
    (hTuu : Tu≤centralizer ({u}:Set G)) (hTvv : Tv≤centralizer ({v}:Set G))
    (hTuv : ∀x∈Tu,v*x*v⁻¹=x^(2^m)) (hTvu : ∀x∈Tv,u*x*u⁻¹=x^(2^m))
    (hTut : ∀x∈Tu,t*x*t⁻¹=x⁻¹) (hTvt : ∀x∈Tv,t*x*t⁻¹=x⁻¹)
    (eu : localCircle Z (centralizer ({u}:Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup (2*m))
    (ev : localCircle Z (centralizer ({v}:Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup (2*m))
    (au : MulAut (localCircle Z (centralizer ({u}:Set G))))
    (av : MulAut (localCircle Z (centralizer ({v}:Set G))))
    (hau : au^2=1) (hav : av^2=1)
    (hou : ¬∃g,au=MulAut.conj g) (hov : ¬∃g,av=MulAut.conj g)
    (hactu : ∀x,localCircleHom Z (centralizer ({u}:Set G)) (au x)=
      v*localCircleHom Z (centralizer ({u}:Set G)) x*v⁻¹)
    (hactv : ∀x,localCircleHom Z (centralizer ({v}:Set G)) (av x)=
      u*localCircleHom Z (centralizer ({v}:Set G)) x*u⁻¹) : False := by
  let A := W⊔zpowers t
  let := residualFourActor_elementary (h.disconnected.involutions t ht) W hWt
  have htA : t∈A := mem_sup_right (mem_zpowers t)
  have huA : u∈A := mem_sup_left hu
  have hvA : v∈A := mem_sup_left hv
  have hwA : t*u*v∈A := A.mul_mem (A.mul_mem htA huA) hvA
  have htw : Commute t (t*u*v) := Subtype.ext_iff.mp
    (mul_comm (⟨t,htA⟩:A) ⟨t*u*v,hwA⟩)
  have huw : Commute u (t*u*v) := Subtype.ext_iff.mp
    (mul_comm (⟨u,huA⟩:A) ⟨t*u*v,hwA⟩)
  have hwM : t*u*v∉M := by
    intro hh
    have huvM : u*v∈M := M.mul_mem (hWD hu).1 (hWD hv).1
    have hh' := M.mul_mem hh (M.inv_mem huvM)
    apply htM
    simpa only [mul_inv_rev,←mul_assoc,mul_inv_cancel_right] using hh'
  have hwi : PFAppendixIII.IsInvolution (t*u*v) :=
    ⟨fun hh => hwM (hh ▸ M.one_mem),elemPow_eq_one_of_isElementaryAbelian _ hwA⟩
  have hto : orderOf t=2 := orderOf_eq_prime (h.disconnected.involutions t ht).sq_eq_one
    (h.disconnected.involutions t ht).ne_one
  let B := centralizer ({t*u*v}:Set G)
  let F := localCircleIn Z B
  have htF : t∈F := by
    change t∈localCircleIn Z B
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨ht,mem_centralizer_singleton_iff.mpr htw.eq⟩
  have huF : u∈normalizer F := source16_localCircleIn_normalizer h.disconnected B
    (mem_centralizer_singleton_iff.mpr huw.eq)
  let eF : localCircle Z B ≃* F :=
    (localCircle Z B).equivMapOfInjective B.subtype B.subtype_injective
  have finish (p : ℕ) (hp : p.Prime) (hpdiv : p∣2^m+1)
      (hcase : p≠3 ∨ (p=3 ∧ 9∣2^m+1)) : False := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨hpo,_,P,hAP,hRD,hRp,hrep,hnon,_,hRC,hRL⟩ :=
      residual_profile_from_paired_tori h.disconnected ht htM W hW hWD hWt hu hv hWgen
        Tu Tv (by omega) hp hpdiv hTuc hTvc hTuo hTvo hTuD hTvD hTuu hTvv
        hTuv hTvu hTut hTvt eu ev au av hau hav hou hov hactu hactv
    let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
    let R := OddInvolutionFrattini.R P₁ t
    have htR : t∈normalizer R := OddInvolutionFrattini.normalizes_R P₁ A hAP htA htA
    obtain ⟨n,hn,E,hfield,hfinite,J,hJ,hcard,hfixed,he⟩ :=
      source16_final_circle_unitary h r ha ht htM hui (hWD hu) hwi htw R hpo hRp
        hRD hRC htR hrep hnon
    have hp2 : p≠2 := fun hh => (by decide : ¬Odd (2:ℕ)) (hh ▸ hpo)
    rcases hcase with hp3 | ⟨hp3,h9⟩
    · rcases he with hep | ⟨_,⟨es⟩⟩
      · obtain ⟨ep⟩ := hep
        exact hnon (projective_ambient_full_commutator_isCyclic J hn hcard hfixed hJ
          F R hRL (eF.symm.trans ep) hp2 hp3 hRp t htF hto htR hrep)
      · exact hnon (special_ambient_full_commutator_isCyclic J hn hcard hfixed hJ
          F R hRL (eF.symm.trans es) hp2 hp3 hRp t htF hto htR hrep)
    · subst p
      obtain ⟨x,hxu,hxo,hux,_,htx⟩ := torus_order_nine_in_chosen_residual h.disconnected
        ht htM W hWD hWt hu hv hWgen Tu (by omega) h9 hTuc hTuo hTuD hTuu hTuv hTut P hAP
      obtain ⟨y,hyv,hyo,_,huy,hty⟩ := torus_order_nine_in_chosen_residual h.disconnected
        ht htM W hWD hWt hv hu (hWgen.trans (sup_comm _ _)) Tv (by omega) h9
        hTvc hTvo hTvD hTvv hTvu hTvt P hAP
      have hxR : x∈R := OddInvolutionFrattini.rw_le P₁ t u hxu
      have hyR : y∈R := OddInvolutionFrattini.rw_le P₁ t v hyv
      have hodd : Odd (Nat.card R) := by
        obtain ⟨k,hk⟩ := hRp.exists_card_eq
        rw [hk]
        exact hpo.pow
      have hux' : u*x*u⁻¹=x := by rw [hux.eq,mul_inv_cancel_right]
      rcases he with hep | ⟨_,⟨es⟩⟩
      · obtain ⟨ep⟩ := hep
        exact projective_ambient_full_commutator_false_of_opposite_order_nine
          J hn hcard hfixed hJ F R hRL (eF.symm.trans ep) hodd hnon t htF hto htR hrep
          u huF x y hxR hyR hxo hyo htx hty hux' huy
      · exact special_ambient_full_commutator_false_of_opposite_order_nine
          J hn hcard hfixed hJ F R hRL (eF.symm.trans es) hodd hnon t htF hto htR hrep
          u huF x y hxR hyR hxo hyo htx hty hux' huy
  rcases prime_ne_three_or_nine_dvd_binary_succ hm with ⟨p,hp,hp3,hpdiv⟩ | h9
  · exact finish p hp hpdiv (Or.inl hp3)
  · exact finish 3 Nat.prime_three ((by norm_num : 3∣9).trans h9) (Or.inr ⟨rfl,h9⟩)
end BenderSuzuki.ZD.Source16OddResidual
