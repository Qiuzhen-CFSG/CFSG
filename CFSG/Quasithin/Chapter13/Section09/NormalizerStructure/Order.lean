module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.CoreFusion
public import CFSG.Quasithin.Chapter13.Section09.SourceCentralizer
public import Theory.LinearAlgebra.BinaryFourFixedSpace

/-!
# The five-point normalizer orbit from original source inputs

The full source centralizer growth gives |C_G(z)|=384 and the two ambient
involution classes. The actual B-centralizer is B. Thus the normalizer
action has a binary four-dimensional faithful quotient. Local class
flags permit z-orbit sizes 1, 5, 9; the GL4(2) order excludes 9, while
size 1 would make the six-point t-centralizer orbit contain fourteen
points. Hence the actual normalizer has order 1920 and z-orbit size 5.

Source: Aschbacher–Smith 13.9.9, printed pp.972–973.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

theorem original_two_involution_classes {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∀x:G,orderOf x=2→IsConj m.z x ∨ IsConj m.t x :=
  m.two_involution_classes hG (m.centralizer_growth hG).1

omit [Finite G] in
theorem t_mem_B : m.t∈m.B := mem_map_of_mem m.embedding (representative_mem_B 1 (by decide))

theorem centralizer_B (hE:IsEvenCharacteristicAt d.T) : centralizer (m.B:Set G)=m.B := by
  apply le_antisymm
  · intro g hg
    have hzt:g∈centralizer ({m.z}:Set G)⊓centralizer ({m.t}:Set G):=by
      constructor
      · exact mem_centralizer_singleton_iff.mpr ((hg m.z m.z_mem_B).symm)
      · exact mem_centralizer_singleton_iff.mpr ((hg m.t m.t_mem_B).symm)
    rw [m.marked_common_centralizer hE,m.elementary_thompson] at hzt
    apply (m.B_local_class_pointwise_centralizer 3 (Or.inl rfl)).le
    exact ⟨m.dihedralBase_le_sylow hzt,centralizer_le (fun _ h=>h.1) hg⟩
  · intro g hg x hx
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=m.B)).is_comm.comm
        (⟨x,hx⟩:m.B) ⟨g,hg⟩)

omit [Finite G] in
theorem normalizerPoint_stabilizer :
    MulAction.stabilizer (normalizer (m.B:Set G)) m.normalizerPoint=
      (centralizer ({m.z}:Set G)).subgroupOf (normalizer (m.B:Set G)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change (⟨(g:G)*m.z*(g:G)⁻¹,_⟩:m.B)=m.normalizerPoint ↔ (g:G)∈centralizer ({m.z}:Set G)
  rw [Subtype.ext_iff,mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul

theorem normalizer_card (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    Nat.card (normalizer (m.B:Set G))=384*m.normalizerOrbit.ncard := by
  have he:=(MulAction.stabilizer (normalizer (m.B:Set G)) m.normalizerPoint).card_mul_index
  rw [m.normalizerPoint_stabilizer,
    Nat.card_congr (subgroupOfEquivOfLe (m.B_normal hE hgrowth).2).toEquiv,
    m.centralizer_z_card hE hgrowth] at he
  rw [←m.normalizerPoint_stabilizer,MulAction.index_stabilizer] at he
  exact he.symm

theorem normalizerLinearAction_ker_eq (hE:IsEvenCharacteristicAt d.T) :
    m.normalizerLinearAction.ker=m.B.subgroupOf (normalizer (m.B:Set G)) := by
  rw [m.normalizerLinearAction_ker,normalizerMonoidHom_ker,m.centralizer_B hE]

theorem normalizerLinearAction_range_card (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    Nat.card m.normalizerLinearAction.range=24*m.normalizerOrbit.ncard := by
  have hk:Nat.card m.normalizerLinearAction.ker=16 := by
    rw [m.normalizerLinearAction_ker_eq hE,
      Nat.card_congr (subgroupOfEquivOfLe m.B.le_normalizer).toEquiv]
    exact m.card_elementaryGroup false false
  have he:=m.normalizerLinearAction.ker.card_mul_index
  rw [index_ker,hk,m.normalizer_card hE hgrowth] at he
  omega

theorem normalizerOrbit_card_ne_nine (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) : m.normalizerOrbit.ncard≠9 := by
  intro he
  have hc:Module.finrank (ZMod 2) BinaryFourPlus.V=4 := by
    simp [BinaryFourPlus.V,BinaryFourPlus.Plane,Module.finrank_prod]
  have hd:=m.normalizerLinearAction.range.card_subgroup_dvd_card
  rw [m.normalizerLinearAction_range_card hE hgrowth,he,BinaryFourFixedSpace.card_GL_four hc] at hd
  norm_num at hd

theorem normalizerOrbit_card_alternatives (hE:IsEvenCharacteristicAt d.T)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) :
    m.normalizerOrbit.ncard=1 ∨ m.normalizerOrbit.ncard=5 ∨ m.normalizerOrbit.ncard=9 := by
  have h0:m.fusionFlags 0=true := by
    simp only [fusionFlags,decide_eq_true_eq]
    exact IsConj.refl _
  have h1:m.fusionFlags 1=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    exact fun h=>m.not_isConj_t_z h.symm
  have h3:m.fusionFlags 3=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    intro h
    exact m.not_isConj_t_z ((m.double_transposition_fused_t hE hgrowth).trans h.symm)
  rw [m.normalizerOrbit_card_flags,classFlagCard_eq,h0,h1,h3]
  cases m.fusionFlags 2 <;> cases m.fusionFlags 4 <;> simp


theorem normalizerOrbit_card_ne_one {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hgrowth:(d.T:Subgroup G)<centralizer ({m.z}:Set G)) : m.normalizerOrbit.ncard≠1 := by
  intro hn
  have hE:=hG.evenCharacteristic d.T
  have hKC:normalizer (m.B:Set G)=centralizer ({m.z}:Set G) := by
    symm
    apply eq_of_le_of_card_ge (m.B_normal hE hgrowth).2
    rw [m.normalizer_card hE hgrowth,hn,m.centralizer_z_card hE hgrowth]
  have hs:Subsingleton m.normalizerOrbit := Finite.card_le_one_iff_subsingleton.mp (by
    change m.normalizerOrbit.ncard≤1
    omega)
  have hweak (x:G) (hx:x∈m.B) (hc:IsConj m.z x):x=m.z := by
    have hy:(⟨x,hx⟩:m.B)∈m.normalizerOrbit := (m.mem_normalizerOrbit_iff_isConj _).mpr hc
    have hz:m.normalizerPoint∈m.normalizerOrbit:=MulAction.mem_orbit_self _
    exact congrArg (fun a:m.normalizerOrbit=>(a.1:G)) (@Subsingleton.elim _ hs ⟨⟨x,hx⟩,hy⟩ ⟨m.normalizerPoint,hz⟩)
  have hsub:(m.B:Set G)\{1,m.z}⊆(centralizer ({m.z}:Set G)).elementOrbit m.t := by
    rintro x ⟨hx,hne⟩
    have hn1:x≠1:=fun he=>hne (Or.inl he)
    have hnz:x≠m.z:=fun he=>hne (Or.inr he)
    have ho:orderOf x=2:=orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p:=2) x hx) hn1
    rcases m.two_involution_classes hG hgrowth x ho with hc|hc
    · exact False.elim (hnz (hweak x hx hc))
    · obtain ⟨g,hg,he⟩:=m.diagonal_controls_fusion false m.t_mem_B hx hc
      exact ⟨g,hKC ▸ hg,he⟩
  have hpair:({1,m.z}:Set G)⊆m.B := by
    rintro x (rfl|rfl)
    · exact m.B.one_mem
    · exact m.z_mem_B
  have h1z:(1:G)≠m.z := by intro h;have hz:=m.z_order;rw [←h,orderOf_one] at hz;omega
  have hcard:((m.B:Set G)\{1,m.z}).ncard=14 := by
    rw [Set.ncard_sdiff hpair,Set.ncard_pair h1z]
    change Nat.card m.B-2=14
    rw [m.card_elementaryGroup false false]
  have hh:=Set.ncard_le_ncard hsub
  rw [hcard,m.centralizer_z_t_orbit_card hE hgrowth] at hh
  omega

theorem normalizerOrbit_card_five {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.normalizerOrbit.ncard=5 := by
  have hgrowth:=(m.centralizer_growth hG).1
  rcases m.normalizerOrbit_card_alternatives (hG.evenCharacteristic d.T) hgrowth with h|h|h
  · exact False.elim (m.normalizerOrbit_card_ne_one hG hgrowth h)
  · exact h
  · exact False.elim (m.normalizerOrbit_card_ne_nine (hG.evenCharacteristic d.T) hgrowth h)

theorem normalizer_card_1920 {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    Nat.card (normalizer (m.B:Set G))=1920 := by
  rw [m.normalizer_card (hG.evenCharacteristic d.T) (m.centralizer_growth hG).1,
    m.normalizerOrbit_card_five hG]

end CFSG.Quasithin.Chapter13.Section09.Marking
