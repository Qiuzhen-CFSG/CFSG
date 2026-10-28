module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.SourceMarking
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.InnerSource
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.Quasithin.NormalTwoRank

/-!
# The marked containing component and its actual Sylow subgroup

Odd rank two makes the original component K normal in H. The full Sylow
subgroup of N(E) intersects the containing ordinary component C in a full
Sylow subgroup of C, which therefore normalizes K. All images, inclusions,
and center two-kernels are retained literally for the target exclusions.
The final field-model caller supplies the odd-rank witness from K/Z(K).
Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
variable {M H K S T E : Subgroup G} {z : G}

theorem exists_normalizing_containing_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G)≤M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G)≤N → N=M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H=K⊔S)
    (hZ : IsPGroup 2 (center K)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hr : 2≤primeRank p K)
    (hE : E≠⊥) (hEC : E≤S⊓centralizer (K:Set G)) (hSE : S≤normalizer (E:Set G)) :
    ∃ (P : Sylow 2 (normalizer (E:Set G))) (C : Subgroup G),
      (P:Subgroup (normalizer (E:Set G))).map (normalizer (E:Set G)).subtype=S ∧
      IsComponentIn C (normalizer (E:Set G)) ∧ K≤C ∧
      IsPGroup 2 (center C) ∧
      Nonempty (MathieuSourceSetup (normalizer (E:Set G)) C M P z) ∧
      ∃ Q : Sylow 2 C, (Q:Subgroup C)≤normalizer (K.subgroupOf C : Set C) := by
  have hHgam : H∈gamma (Chapter1.He G) M :=
    d.gamma_zero.elim (fun h=>h.1.1) (fun h=>h.1)
  let eK : K.subgroupOf H ≃* K := subgroupOfEquivOfLe hK.1
  have hZ' : IsPGroup 2 (center (K.subgroupOf H)) := hZ.of_equiv (centerCongr eK.symm)
  have hcop : Nat.Coprime p (Nat.card (center (K.subgroupOf H))) := by
    obtain ⟨m,hm⟩ := hZ'.exists_card_eq
    rw [hm]
    exact (Nat.coprime_two_right.mpr ho).pow_right m
  have hr' : 2≤primeRank p (K.subgroupOf H) := by rwa [primeRank_equiv p eK]
  have hcore : pCore 2 H≠⊥ := by
    intro he
    exact hHgam.1 (by simp only [twoCore,he,Subgroup.map_bot])
  have hbound := Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup
    hG.quasithin H (pCore 2 H) hcore pCore_isPGroup p Fact.out ho
  have hnormal : (K.subgroupOf H).Normal :=
    hK.2.normal_of_coprime_center_primeRank p hcop (by omega)
  have hSK : S≤normalizer (K:Set G) :=
    (hgen ▸ (le_sup_right : S≤K⊔S)).trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnormal)
  obtain ⟨C,hC,hKC⟩ := exists_containing_component hG T₀ hM hT₀M hunique d hK hgen hE hEC hSE
  obtain ⟨hJ,⟨P,hP⟩,_⟩ := centralizer_subgroup_normalizer d hgen hE hEC hSE
  obtain ⟨c⟩ := exists_setup_of_same_sylow T₀ hM hT₀M hunique d hJ P hP hC
  have hZC : IsPGroup 2 (center C) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  obtain ⟨R,hR⟩ := P.exists_subgroupOf_eq_of_subnormal (C.subgroupOf (normalizer (E:Set G))) hC.2.1
  let eC : C.subgroupOf (normalizer (E:Set G)) ≃* C := subgroupOfEquivOfLe hC.1
  let Q : Sylow 2 C := R.mapSurjective (f:=eC.toMonoidHom) eC.surjective
  have hQS : (Q:Subgroup C).map C.subtype≤S := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨r,hr,rfl⟩ := hx
    have hrP : (r : normalizer (E:Set G))∈P := by
      change r∈(P:Subgroup (normalizer (E:Set G))).subgroupOf (C.subgroupOf (normalizer (E:Set G)))
      rwa [←hR]
    exact hP ▸ mem_map_of_mem (normalizer (E:Set G)).subtype hrP
  refine ⟨P,C,hP,hC,hKC,hZC,⟨c⟩,Q,?_⟩
  rw [←subgroupOf_normalizer_eq hKC]
  intro x hx
  exact hSK (hQS (mem_map_of_mem C.subtype hx))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
