module
public import Theory.Representation.G2BinaryOffenderGeneration
public import Theory.Representation.G2BinaryModelOffenders
public import Theory.Representation.G2BinaryPlaneKernel
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
/-!
# The unique offender in the binary G₂ point radical

The natural offender classification puts every offender in the first
five-root subgroup. Inside the second radical, the central A and B roots
then belong to the offender by the sharp elementary-rank bound. Its fixed
three-space is the standard seed, and the remaining D parameter vanishes.
Thus the offender is exactly the A–B–C eight. Independently, fixing the seed
pointwise forces an actor into the Borel and removes the D, E and F parameters.

These are the model inputs in C.1.37 and the unitary Baumann argument
13.3.10(2), printed pp.141–143 and 887–888 of Aschbacher–Smith.
The root coordinates retain the attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinaryPointOffenders
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.LieParabolicSetup NaturalOffenders
local notation "𝔽" => ZMod 2
local notation "H" => Atlas.G2.Model 𝔽
local notation "ρ" => Atlas.G2.Restricted.NaturalCoordinates.action 𝔽

private theorem offender_card (A : Subgroup H) (hA : IsOffender ρ A) : Nat.card A = 8 := by
  obtain ⟨g,rfl⟩ := offender_conjugate_elementary
    (F := 𝔽) (n := 1) (by norm_num) (by decide) A hA
  rw [card_map_of_injective (MulAut.conj g).injective,EvenTwoRank.elementary_card,Nat.card_zmod]
  norm_num

private theorem root_mem (A : Subgroup H) (hA : IsOffender ρ A)
    (z : H) (hz : orderOf z = 2) (hc : A ≤ centralizer ({z} : Set H)) : z ∈ A := by
  by_contra hn
  let := hA.1.2
  have hr := IsElementaryAbelian.primeRank_ge_of_fixed_join A z hz hn hc
    (show Nat.card A = 2^3 from offender_card A hA)
  have hu := EvenTwoRank.two_rank 𝔽 (n := 1) (by norm_num)
  norm_num at hu
  omega

private theorem rootB_commutes (t : Fin 6 → 𝔽) (ht : t 5 = 0) (ht4 : t 4 = 0) :
    Commute (unipotentProduct t) (rootB 1) := by
  have hb : rootB (1 : 𝔽) = unipotentProduct ![0,1,0,0,0,0] := by
    simp [unipotentProduct]
  rw [hb]
  change _ * _ = _ * _
  rw [unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters,ht,ht4,add_comm]

/-- The point-radical natural offender is uniquely the marked root eight. -/
theorem offender_eq_elementary (A : Subgroup H) (hA : IsOffender ρ A)
    (hA2 : A ≤ radical₂) : A = BinaryCore.elementary := by
  have hU := hA2.trans (fiveRootSubgroup_le_unipotent 4 (Or.inl rfl))
  have hA1 := BinaryOffenderGeneration.offender_le_radical A hA hU
  have ha : rootA (1 : 𝔽) ∈ A := by
    apply root_mem A hA
    · apply orderOf_eq_prime
      · rw [pow_two,rootA_add,show (1 : 𝔽)+1=0 by decide,rootA_zero]
      · intro hz
        exact one_ne_zero (rootA_injective (hz.trans rootA_zero.symm))
    · intro a ha
      have hu := hU ha
      rw [unipotent_eq_range] at hu
      obtain ⟨t,rfl⟩ := hu
      exact mem_centralizer_singleton_iff.mpr (unipotentProduct_commute_rootA t 1).eq
  have hb : rootB (1 : 𝔽) ∈ A := by
    apply root_mem A hA
    · apply orderOf_eq_prime
      · rw [pow_two,rootB_add,show (1 : 𝔽)+1=0 by decide,rootB_zero]
      · intro hz
        exact one_ne_zero (rootB_injective (hz.trans rootB_zero.symm))
    · rintro a ha
      obtain ⟨t,ht,rfl⟩ := hA1 ha
      have ht4 : t 4 = 0 := by
        obtain ⟨s,hs,he⟩ := hA2 ha
        exact (congrFun (unipotentProduct_injective he.symm) 4).trans hs
      exact mem_centralizer_singleton_iff.mpr (rootB_commutes t ht ht4).eq
  have hfixed : fixedSpace ρ A = upper (F := 𝔽) := by
    have hle : fixedSpace ρ A ≤ upper := fun v hv =>
      mem_upper_of_fixed_longRoots (hv ⟨_,ha⟩) (hv ⟨_,hb⟩)
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hd : fixedCodim ρ A = 3 := by
      obtain ⟨g,rfl⟩ := offender_conjugate_elementary
        (F := 𝔽) (n := 1) (by norm_num) (by decide) A hA
      rw [fixedCodim_map_conj]
      exact fixedCodim_elementary (n := 1) (by norm_num)
    have hs := fixedCodim_add_finrank ρ A
    rw [upper_finrank]
    have ht : Module.finrank 𝔽 (Fin 6 → 𝔽) = 6 := by simp
    rw [hd,ht] at hs
    omega
  have hle : A ≤ BinaryCore.elementary := by
    intro a ha'
    obtain ⟨t,ht4,rfl⟩ := hA2 ha'
    have ht5 : t 5 = 0 := by
      obtain ⟨s,hs,he⟩ := hA1 ha'
      exact (congrFun (unipotentProduct_injective he.symm) 5).trans hs
    have hf : ρ (unipotentProduct t) (Pi.single 2 1) = Pi.single 2 1 := by
      have hv : (Pi.single 2 1 : Fin 6 → 𝔽) ∈ fixedSpace ρ A := by
        rw [hfixed]
        simp
      exact hv ⟨_,ha'⟩
    have ht3 : t 3 = 0 := by
      have hh := congrFun hf 0
      simpa [unipotentProduct,map_mul,Module.End.mul_apply,
        action_rootA,action_rootB,action_rootC,action_rootD,action_rootE,action_rootF,ht4,ht5] using hh
    refine ⟨⟨t 0,t 1,t 2,0,0⟩,⟨rfl,rfl⟩,?_⟩
    change unipotentProduct (BinaryCore.parameters ⟨t 0,t 1,t 2,0,0⟩) = unipotentProduct t
    congr 1
    ext i
    fin_cases i <;> simp [BinaryCore.parameters,ht3,ht4,ht5]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [offender_card A hA,BinaryCore.card_elementary])

/-- The pointwise stabilizer of the marked three-space is exactly the root eight. -/
theorem fixes_seed_iff (g : H) :
    (∀ v ∈ BinaryPointFlag.seed, ρ g v = v) ↔ g ∈ BinaryCore.elementary := by
  constructor
  · intro hg
    have hu : g ∈ unipotent := BinaryPointFlag.plane_pointwise_le_unipotent g
      (fun v hv => hg v (BinaryPointFlag.plane_le_seed hv))
    rw [unipotent_eq_range] at hu
    obtain ⟨t,rfl⟩ := hu
    have hf (i : Fin 3) : ρ (unipotentProduct t) (Pi.single (i.castLE (by decide)) 1) =
        Pi.single (i.castLE (by decide)) 1 := hg _ (by
      rw [BinaryPointFlag.mem_seed]; fin_cases i <;> simp)
    have h5 : t 5 = 0 := by
      have hh := congrFun (hf 1) 0
      simpa [unipotentProduct,map_mul,Module.End.mul_apply,
        action_rootA,action_rootB,action_rootC,action_rootD,action_rootE,action_rootF] using hh
    have h4 : t 4 = 0 := by
      have hh := congrFun (hf 2) 1
      simpa [unipotentProduct,map_mul,Module.End.mul_apply,
        action_rootA,action_rootB,action_rootC,action_rootD,action_rootE,action_rootF] using hh
    have h3 : t 3 = 0 := by
      have hh := congrFun (hf 2) 0
      simpa [unipotentProduct,map_mul,Module.End.mul_apply,
        action_rootA,action_rootB,action_rootC,action_rootD,action_rootE,action_rootF] using hh
    refine ⟨⟨t 0,t 1,t 2,0,0⟩,⟨rfl,rfl⟩,?_⟩
    change unipotentProduct (BinaryCore.parameters ⟨t 0,t 1,t 2,0,0⟩) = unipotentProduct t
    congr 1
    ext i
    fin_cases i <;> simp [BinaryCore.parameters,h3,h4,h5]
  · intro hg v hv
    rw [BinaryModelOffenders.elementary_eq] at hg
    exact elementary_fix_upper hg ((BinaryPointFlag.mem_seed v).mp hv)
end Atlas.G2.Natural.BinaryPointOffenders
