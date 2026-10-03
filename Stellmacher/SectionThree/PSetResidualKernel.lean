module

public import Stellmacher.SectionThree.NormalSubgroupCoreControl
public import Stellmacher.SectionThree.LemmaThreeSeven

open scoped Pointwise

namespace Stellmacher.SectionThree

public theorem pSet_two_subgroup_normal_kernel_le_core
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P K A : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (hKP : K ≤ P)
    (hKN : (K.subgroupOf P).Normal)
    (hres : ¬ twoResidualAmbient P ≤ K)
    (hAK : A ≤ K) (hA : IsPGroup 2 A) :
    A ≤ twoCoreAmbient P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SP, hSP⟩ := hP.1.2.1
  have hSleP : S ≤ P := by
    rw [← hSP]
    exact Subgroup.map_subtype_le _
  have hnot : ¬ P ≤ K ⊔ S := by
    intro hgen
    have heq : K ⊔ S = P := le_antisymm (sup_le hKP hSleP) hgen
    have hnormal : (K.subgroupOf (K ⊔ S)).Normal := by
      rw [heq]
      exact hKN
    exact hres (twoResidualAmbient_le_left_of_le_sup K S P hnormal
      h.nontrivial_two_subgroup.2 hgen)
  have hcontrol := normal_inf_sylow_le_twoCore S h P K hP hsolv hKP hKN hnot
  have hAP : A ≤ P := hAK.trans hKP
  have hAp : IsPGroup 2 (A.subgroupOf P) := hA.comap_subtype
  obtain ⟨U, hAU⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P U SP
  intro a ha
  let aP : P := ⟨a, hAP ha⟩
  have haU : aP ∈ (U : Subgroup P) := hAU ha
  have hgaSP : g * aP * g⁻¹ ∈ (SP : Subgroup P) := by
    rw [← hg]
    change g * aP * g⁻¹ ∈ (U : Subgroup P).map (MulAut.conj g).toMonoidHom
    exact ⟨aP, haU, rfl⟩
  have hgaS : ((g * aP * g⁻¹ : P) : G) ∈ S := by
    rw [← hSP]
    exact ⟨g * aP * g⁻¹, hgaSP, rfl⟩
  have hgaK : ((g * aP * g⁻¹ : P) : G) ∈ K :=
    hKN.conj_mem aP (hAK ha) g
  obtain ⟨t, ht, heq⟩ := hcontrol ⟨hgaK, hgaS⟩
  have hteq : t = g * aP * g⁻¹ := P.subtype_injective heq
  have hgaCore : g * aP * g⁻¹ ∈ pCore 2 P := by
    simpa [hteq] using ht
  have haCore : aP ∈ pCore 2 P := by
    have hback := (pCore_normal (p := 2) (G := P)).conj_mem
      (g * aP * g⁻¹) hgaCore g⁻¹
    simpa [mul_assoc] using hback
  exact ⟨aP, haCore, rfl⟩

public theorem pSet_actor_core_index_le_image_card
    {G X : Type*} [Group G] [Finite G] [Group X]
    (S : Subgroup G) (h : Hypotheses G S)
    (P A : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (hAP : A ≤ P)
    (hA : IsPGroup 2 A) (f : P →* X)
    (hres : ¬ twoResidualSubgroup P ≤ f.ker) :
    (A ⊓ twoCoreAmbient P).relIndex A ≤ Nat.card ((A.subgroupOf P).map f) := by
  classical
  let K := f.ker.map P.subtype
  have hKP : K ≤ P := Subgroup.map_subtype_le _
  have hKsub : K.subgroupOf P = f.ker := subgroupOf_map_subtype_eq _
  have hKN : (K.subgroupOf P).Normal := by
    rw [hKsub]
    infer_instance
  have hRnot : ¬ twoResidualAmbient P ≤ K := by
    intro hle
    exact hres ((Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp hle)
  have hcore : A ⊓ K ≤ twoCoreAmbient P :=
    pSet_two_subgroup_normal_kernel_le_core S h P K (A ⊓ K) hP hsolv hKP hKN
      hRnot inf_le_right (hA.to_le inf_le_left)
  have hindex : (A ⊓ twoCoreAmbient P).relIndex A ≤ (A ⊓ K).relIndex A :=
    Subgroup.relIndex_le_of_le_left (le_inf inf_le_left hcore)
      (Subgroup.FiniteIndex.index_ne_zero (H := (A ⊓ K).subgroupOf A))
  have hindex' : (A ⊓ twoCoreAmbient P).relIndex A ≤ K.relIndex A := by
    simpa only [Subgroup.inf_relIndex_left] using hindex
  have heq : K.relIndex A = Nat.card ((A.subgroupOf P).map f) := by
    rw [← Subgroup.relIndex_subgroupOf (H := K) hAP, hKsub, Subgroup.relIndex_ker]
  rw [heq] at hindex'
  exact hindex'

end Stellmacher.SectionThree

