module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Torus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.TwistedCircles
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.FrattiniAction

/-!
# The noncyclic odd residual in the circle of tuv

The paired square-field tori construct the same invariant Sylow subgroup of
the actual odd core. Their opposite actions prove that R=[R₁,t] is noncyclic.
The paired linear circles and the outer-field coboundary give cyclicity of
R_u, R_v, R_tu and R_tv. The Frattini plane argument then forces tuv to
centralize R, placing R in the literal circle of its centralizer.

The output preserves the invariant Sylow, its ambient image, the commutator
identity, the original two-point stabilizer and the literal Frattini quotient.
The remaining source assembly establishes cyclicity in this last circle using
the correctly changed distinguished base point.

Source: GLS IV, Chapter 2, Proposition 16.5, odd-primary argument.
-/

noncomputable section
namespace BenderSuzuki.ZD.Source16OddResidual
open Subgroup Theory.GroupTheory OddInvolutionFrattini NativeSource16
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The complete odd-primary construction from the preceding literal torus
and circle models, ready for the terminal changed-base cyclicity argument. -/
public theorem residual_profile_from_paired_tori
    {t u v : G} (h : IsProductDisconnected Z M) (ht : t∈Z) (htM : t∉M)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W=4)
    (hWD : W≤residualPairStabilizer M t) (hWt : W≤centralizer ({t}:Set G))
    (hu : u∈W) (hv : v∈W) (hWgen : W=zpowers u⊔zpowers v)
    (Tu Tv : Subgroup G) {m p : ℕ} (hm : 0<m) (hp : p.Prime) (hpdiv : p∣2^m+1)
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
      u*localCircleHom Z (centralizer ({v}:Set G)) x*u⁻¹) :
    let A := W⊔zpowers t
    Odd p ∧ Nat.card A=8 ∧ ∃ P : Sylow p (residualOddCore M t),
      let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
      let R := OddInvolutionFrattini.R P₁ t
      A≤normalizer P₁ ∧
        R≤residualPairStabilizer M t ∧ IsPGroup p R ∧ ⁅R,zpowers t⁆=R ∧
          ¬IsCyclic R ∧ Nat.card ((↥R) ⧸ frattini (↥R))=p^2 ∧
          R≤centralizer ({t*u*v}:Set G) ∧
          R≤localCircleIn Z (centralizer ({t*u*v}:Set G)) := by
  let A := W⊔zpowers t
  let : Fact p.Prime := ⟨hp⟩
  let := residualFourActor_elementary (h.involutions t ht) W hWt
  have hpo : Odd p := prime_dividing_binary_succ_odd hm hp hpdiv
  have hpn : p≠2 := by
    intro he
    subst p
    exact (by decide : ¬ Odd (2 : ℕ)) hpo
  have huA : u∈A := mem_sup_left hu
  have hvA : v∈A := mem_sup_left hv
  have htA : t∈A := mem_sup_right (mem_zpowers t)
  have htu : Commute t u := (mem_centralizer_singleton_iff.mp (hWt hu)).symm
  have htv : Commute t v := (mem_centralizer_singleton_iff.mp (hWt hv)).symm
  obtain ⟨etu⟩ := twisted_circle_model h ht htv htu eu ev av hav hov hactv
  obtain ⟨etv⟩ := twisted_circle_model h ht htu htv ev eu au hau hou hactu
  obtain ⟨hcard,P,hAP,hn,hmoveu,hmovev,hinvu,hinvv⟩ := residualFourActor_noncyclic_of_torus_actions
    h ht htM W hW hWD hWt u v hu hv hWgen Tu Tv hm hp hpdiv hTuc hTvc hTuo hTvo
    hTuD hTvD hTuu hTvv hTuv hTvu hTut hTvt
  let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
  have hPp : IsPGroup p P₁ := P.isPGroup'.map _
  have hcu := rw_cyclic_of_linear_circle h P₁ A hPp hpn hAP htA huA ht eu
  have hcv := rw_cyclic_of_linear_circle h P₁ A hPp hpn hAP htA hvA ht ev
  have hctu := rw_cyclic_of_linear_circle h P₁ A hPp hpn hAP htA (A.mul_mem htA huA) ht etu
  have hctv := rw_cyclic_of_linear_circle h P₁ A hPp hpn hAP htA (A.mul_mem htA hvA) ht etv
  obtain ⟨hcq,hcentral⟩ := product_centralizes_of_cyclic_fixed_commutators
    P₁ A hPp hpo hAP htA huA hvA (h.involutions t ht) hcu hcv hctu hctv hn (hinvv hcv)
  have hRP : R P₁ t≤P₁ := r_le P₁ (hAP htA)
  have hRp : IsPGroup p (R P₁ t) := hPp.of_injective (inclusion hRP) (inclusion_injective hRP)
  have hrep := repeated_commutator_of_isPGroup P₁ hPp hpo (hAP htA) (h.involutions t ht)
  have htw : Commute t (t*u*v) := Subtype.ext_iff.mp
    (mul_comm (⟨t,htA⟩:A) ⟨t*u*v,A.mul_mem (A.mul_mem htA huA) hvA⟩)
  refine ⟨hpo,hcard,P,hAP,?_,hRp,hrep,hn,hcq,hcentral,?_⟩
  · exact hRP.trans ((map_subtype_le _).trans residualOddCore_le_pair)
  · exact full_commutator_le_circle h _ ht htw hcentral hrep

end BenderSuzuki.ZD.Source16OddResidual
