module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.WeakClosure
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Placement
public import Theory.GroupAction.FiveOrbitStabilizer

/-!
# The actual normalizer orbit

Burnside fusion identifies the literal normalizer orbit with the ambient z-class in B. Under C_G(z)=T its stabilizer has order128 and its permutation kernel is the pointwise centralizer. The five-point obstruction then applies to the actual action.

Source: Aschbacher–Smith 13.9.5, printed pp.970–971 (PDF pp.987–988).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G : Type*} [Group G] {d : Configuration G} (m : Marking d)

theorem z_mem_B : m.z∈m.B := by
  apply mem_map_of_mem m.embedding
  change SymmetricFourWreath.z∈(elementaryInP false false).map sylowEmbedding
  rw [←sylowEmbedding_centralInP]
  apply mem_map_of_mem
  exact ⟨(DihedralGroup.r 2,DihedralGroup.r 2),⟨Or.inr (Or.inl rfl),Or.inr (Or.inl rfl)⟩,rfl⟩

theorem sylow_le_normalizer_B : (d.T:Subgroup G)≤normalizer (m.B:Set G) := by
  rw [←m.image_standardSylow]
  exact m.image_le_normalizer_image (standardSylow_le_normalizer_diagonal false)

def normalizerPoint : m.B := ⟨m.z,m.z_mem_B⟩

def normalizerOrbit : Set m.B := MulAction.orbit (normalizer (m.B:Set G)) m.normalizerPoint

theorem mem_normalizerOrbit_iff (x : m.B) : x∈m.normalizerOrbit ↔
    ∃g∈normalizer (m.B:Set G),g*m.z*g⁻¹=(x:G) := by
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g,g.property,congrArg Subtype.val hg⟩
  · rintro ⟨g,hg,he⟩
    exact ⟨⟨g,hg⟩,Subtype.ext he⟩

variable [Finite G]

theorem mem_normalizerOrbit_iff_isConj (x : m.B) :
    x∈m.normalizerOrbit ↔ IsConj m.z (x:G) := by
  rw [m.mem_normalizerOrbit_iff]
  constructor
  · rintro ⟨g,_,hg⟩
    exact isConj_iff.mpr ⟨g,hg⟩
  · exact m.diagonal_controls_fusion false m.z_mem_B x.property

omit [Finite G] in
theorem normalizerPoint_stabilizer_of_centralizer_eq
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    MulAction.stabilizer (normalizer (m.B:Set G)) m.normalizerPoint=
      (d.T:Subgroup G).subgroupOf (normalizer (m.B:Set G)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change (⟨(g:G)*m.z*(g:G)⁻¹,_⟩:m.B)=m.normalizerPoint ↔ (g:G)∈(d.T:Subgroup G)
  rw [Subtype.ext_iff,←hC,mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul

theorem normalizerPoint_stabilizer_card_of_centralizer_eq
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    Nat.card (MulAction.stabilizer (normalizer (m.B:Set G)) m.normalizerPoint)=128 := by
  rw [m.normalizerPoint_stabilizer_of_centralizer_eq hC,
    Nat.card_congr (subgroupOfEquivOfLe m.sylow_le_normalizer_B).toEquiv,d.card_sylow]

theorem normalizer_card_of_centralizer_eq
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    Nat.card (normalizer (m.B:Set G))=128*m.normalizerOrbit.ncard := by
  have he := (MulAction.stabilizer (normalizer (m.B:Set G)) m.normalizerPoint).card_mul_index
  rw [m.normalizerPoint_stabilizer_card_of_centralizer_eq hC,MulAction.index_stabilizer] at he
  exact he.symm

theorem normalizerOrbit_nontrivial_of_centralizer_eq
    {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    ∃x∈m.normalizerOrbit,x≠m.normalizerPoint := by
  obtain ⟨x,hx,hconj,hne⟩ := m.exists_conjugate_z_in_B_of_centralizer_eq hG hC
  exact ⟨⟨x,hx⟩,(m.mem_normalizerOrbit_iff_isConj _).mpr hconj,
    fun he=>hne (congrArg Subtype.val he)⟩

def normalizerOrbitAction : normalizer (m.B:Set G) →* Equiv.Perm m.normalizerOrbit :=
  MulAction.toPermHom (normalizer (m.B:Set G))
    (MulAction.orbit (normalizer (m.B:Set G)) m.normalizerPoint)

theorem normalizerOrbitAction_ker :
    m.normalizerOrbitAction.ker=
      (centralizer {x:G | x∈m.B ∧ IsConj m.z x}).subgroupOf (normalizer (m.B:Set G)) := by
  ext g
  rw [MonoidHom.mem_ker,mem_subgroupOf,mem_centralizer_iff]
  constructor
  · intro he x hx
    have hxO := (m.mem_normalizerOrbit_iff_isConj (⟨x,hx.1⟩:m.B)).mpr hx.2
    have hf := congrArg (fun e:Equiv.Perm m.normalizerOrbit =>
      (((e ⟨⟨x,hx.1⟩,hxO⟩:m.normalizerOrbit):m.B):G)) he
    change (g:G)*x*(g:G)⁻¹=x at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf).symm
  · intro he
    apply Equiv.ext
    rintro ⟨x,hx⟩
    apply Subtype.ext
    apply Subtype.ext
    change (g:G)*(x:G)*(g:G)⁻¹=(x:G)
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (he x ⟨x.property,(m.mem_normalizerOrbit_iff_isConj x).mp hx⟩).symm

theorem normalizerOrbit_card_ne_five_of_centralizer
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G))
    (hfix : (d.T:Subgroup G)⊓centralizer {x:G | x∈m.B ∧ IsConj m.z x}=m.B) :
    m.normalizerOrbit.ncard≠5 := by
  have hle : centralizer {x:G | x∈m.B ∧ IsConj m.z x}≤(d.T:Subgroup G) := by
    rw [←hC]
    intro g hg
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hg m.z ⟨m.z_mem_B,IsConj.refl _⟩).symm)
  have hc : centralizer {x:G | x∈m.B ∧ IsConj m.z x}=m.B := by
    simpa only [inf_eq_right.mpr hle] using hfix
  have hk : Nat.card m.normalizerOrbitAction.ker=16 := by
    rw [m.normalizerOrbitAction_ker,hc,
      Nat.card_congr (subgroupOfEquivOfLe m.B.le_normalizer).toEquiv]
    exact m.card_elementaryGroup false false
  apply MulAction.orbit_card_ne_five_of_stabilizer_kernel_ratio m.normalizerPoint
  rw [m.normalizerPoint_stabilizer_card_of_centralizer_eq hC]
  change 128=8*Nat.card m.normalizerOrbitAction.ker
  rw [hk]
end CFSG.Quasithin.Chapter13.Section09.Marking
