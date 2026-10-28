module
public import BenderSuzuki.SE.Models
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.Converse.PSU3
public import BenderSuzuki.Converse.Sz
public import BenderSuzuki.PFchapter1section2.proposition_1_c
/-!
# Commuting Sylow involutions in the three simple Bender models

The concrete PSL₂, Suzuki, and Hermitian PSU₃ constructions satisfy
Peterfalvi's Hypothesis (A). Its root group contains a Sylow two-subgroup,
and its involutions are central. Sylow conjugacy therefore shows that
square-one elements in every two-subgroup commute. The unitary branch
retains the actual Hermitian involution and both field cardinalities.

The model restrictions are exactly n ≥ 2 for PSL₂ and PSU₃ and m ≥ 1 for
Suzuki; the rank-one cases are not replaced by a solvability assertion.
Source: Bender–Suzuki/Peterfalvi I.1.1(c), I.2.1(c), and the verified
three-family converse constructions.
-/
public section
open Subgroup
namespace BenderSuzuki
open PFchapter1section1 PFAppendixIII
private theorem squares_commute_of_hypothesisA
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t)
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (a b : G) (ha : a∈P) (hb : b∈P) (ha2 : a^2=1) (_hb2 : b^2=1) : Commute a b := by
  by_cases ha1 : a=1
  · simp [ha1]
  by_cases hb1 : b=1
  · simp [hb1]
  obtain ⟨S,hS⟩:=PFchapter1section1.proposition_1_c H D Q t hA.A1
  obtain ⟨T,hT⟩:=hP.exists_le_sylow
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G T S
  let f: G≃*G:=MulAut.conj g
  have hmap : (T:Subgroup G).map f.toMonoidHom=(S:Subgroup G) := by
    change (g • T : Sylow 2 G).toSubgroup=(S:Subgroup G)
    exact congrArg (fun U:Sylow 2 G=>(U:Subgroup G)) hg
  have haQ : f a∈Q := hS (hmap ▸ mem_map_of_mem f.toMonoidHom (hT ha))
  have hbQ : f b∈Q := hS (hmap ▸ mem_map_of_mem f.toMonoidHom (hT hb))
  have hac:=PFchapter1section2.proposition_1_c_involutions_center_of_hA H D Q t hA
    ⟨f a,haQ⟩ (hA.A1.Q_le_H haQ) (IsInvolution.map_of_injective ⟨ha1,ha2⟩ f.toMonoidHom f.injective)
  apply f.injective
  rw [map_mul,map_mul]
  exact congrArg Subtype.val ((mem_center_iff.mp hac) ⟨f b,hbQ⟩).symm

private theorem squares_commute_of_model_equiv
    {G K : Type*} [Group G] [Finite G] [Group K] [Finite K] (e:G≃*K)
    (hh : ∀ (P:Subgroup K), IsPGroup 2 P → ∀ a b:K,
      a∈P → b∈P → a^2=1 → b^2=1 → Commute a b)
    (P:Subgroup G) (hP:IsPGroup 2 P) (a b:G)
    (ha:a∈P) (hb:b∈P) (ha2:a^2=1) (hb2:b^2=1) : Commute a b := by
  apply e.injective
  rw [map_mul,map_mul]
  exact (hh (P.map e.toMonoidHom) (hP.map _) (e a) (e b)
    (mem_map_of_mem _ ha) (mem_map_of_mem _ hb)
    (by rw [←map_pow,ha2,map_one]) (by rw [←map_pow,hb2,map_one])).eq

theorem IsSimpleBenderGroup.squares_commute_in_twoSubgroup
    {G:Type*} [Group G] [Finite G] (hG:IsSimpleBenderGroup G)
    (P:Subgroup G) (hP:IsPGroup 2 P) (a b:G)
    (ha:a∈P) (hb:b∈P) (ha2:a^2=1) (hb2:b^2=1) : Commute a b := by
  rcases hG with ⟨⟨n,hn,e⟩⟩ | ⟨⟨n,hn,e⟩⟩ |
    ⟨⟨n,hn,E,hEfield,hEfinite,J,hJ,hEcard,hfixedCard,e⟩⟩
  · apply squares_commute_of_model_equiv e.some _ P hP a b ha hb ha2 hb2
    exact squares_commute_of_hypothesisA _ _ _ _ (Converse.hypothesisA_PSL2_binary n hn)
  · let : NeZero n:=⟨by omega⟩
    apply squares_commute_of_model_equiv e.some _ P hP a b ha hb ha2 hb2
    exact squares_commute_of_hypothesisA _ _ _ _ (Converse.hypothesisA_Sz n)
  · let : Field E:=hEfield
    let : Finite E:=hEfinite
    apply squares_commute_of_model_equiv e.some _ P hP a b ha hb ha2 hb2
    obtain ⟨_,rho,_,_,happly,_⟩:=External.huppert_II_10_12 J (2^n) hEcard hfixedCard hJ
    obtain ⟨H,D,Q,t,_,hA⟩:=Converse.hypothesisA_psu3_general J hJ (2^n) hEcard hfixedCard
      (by
        calc (2:ℕ)<2^2:=by decide
             _≤2^n:=Nat.pow_le_pow_right (by decide) hn)
      ⟨n,rfl⟩ rho happly
    let : MulAction (MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) (Converse.psuOmega J):=
      MulAction.compHom _ rho
    exact squares_commute_of_hypothesisA H D Q t hA

end BenderSuzuki
