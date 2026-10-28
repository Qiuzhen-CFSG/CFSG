module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterFusion
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallNormality
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlignedPairs
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.ResidualSource
public import Theory.SpecificGroups.PSL3Three.EightGeometry.CentralProduct
public import Theory.SpecificGroups.PSL3Three.EightGeometry.AmbientCentralizer
public import Theory.GroupTheory.CentralizerNormalizerOrbit
public import Theory.GroupTheory.CentralInvolutionFusionCard
/-!
# Excluding the original PSL₃(3) component source

The original largest local pair supplies an inner four E. Its centralizer
Q in H is an elementary sixteen. The source fusion complement identifies
the class of the central involution t in Q with the eight elements outside
the complement. All elementary sixteens in H are conjugate in H = C_G(t),
so this class is one orbit of N_G(Q). The largest-pair normalizer theorem
provides a Sylow two-subgroup of N_G(Q) contained in C_G(t), making the
orbit cardinality odd, a contradiction.

The final theorem derives component normality and selects the largest pair
from the original source hypotheses. Source: Aschbacher--Smith, Lemma
2.5.15, printed p.559; the orbit argument is the cited A.1.7 application.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

/-- The last source contradiction, retaining the largest pair and the aligned fusion complement. -/
theorem linear_three_false_of_fusion_complement
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (t : G) (ht : orderOf t = 2) (hCt : centralizer ({t} : Set G) = H)
    (hnf : ¬ IsConj t z) (A : Subgroup G) (hKA : K ≤ A)
    (d : A ≃* MulAut Matrix.PSL3Three.PSL)
    (hinner : K.subgroupOf A = (MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap d.toMonoidHom)
    (hH : H = zpowers t ⊔ A) (hd : Disjoint (zpowers t) A)
    (hcomm : zpowers t ≤ centralizer (A : Set G))
    (hinside : ∀ a ∈ A, orderOf a = 2 → IsConj z a)
    (houtside : ∀ a ∈ H, a ∉ A → orderOf a = 2 → IsConj t a) : False := by
  obtain ⟨E,hES,hE,hL,_⟩ := largest_pair_four_structure_of_source c hG hempty hgen hb hp hUS
  let : IsKleinFour E := hE
  let : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  have hEK : E ≤ K := hES.trans inf_le_right
  let Q := H ⊓ centralizer (E : Set G)
  obtain ⟨hsplit,hQ,hQc⟩ := Matrix.PSL3Three.EightGeometry.inner_four_central_product_centralizer
    d hKA hinner t ht hH hd hcomm hEK (inferInstance : IsElementaryAbelian 2 E)
    IsKleinFour.card_four
  change Q = _ at hsplit
  change IsElementaryAbelian 2 Q at hQ
  change Nat.card Q = 16 at hQc
  let : IsElementaryAbelian 2 Q := hQ
  have htQ : t ∈ Q := hsplit.symm ▸ mem_sup_left (mem_zpowers t)
  have hAH : A ≤ H := by rw [hH]; exact le_sup_right
  have hQA : Q ⊓ A = A ⊓ centralizer (E : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans hAH) inf_le_right) inf_le_left
  have hQAc : Nat.card (Q ⊓ A : Subgroup G) = 8 := by
    rw [hQA]
    exact (Matrix.PSL3Three.EightGeometry.inner_four_ambient_centralizer
      d hKA hinner hEK (inferInstance : IsElementaryAbelian 2 E) IsKleinFour.card_four).2
  have hfamily : ∀ g : G, t ∈ Q.map (MulAut.conj g).toMonoidHom →
      ∃ a ∈ centralizer ({t} : Set G),
        Q.map (MulAut.conj g).toMonoidHom = Q.map (MulAut.conj a).toMonoidHom := by
    intro g htg
    let B := Q.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    have hBc : Nat.card B = 16 :=
      (card_map_of_injective (MulAut.conj g).injective).trans hQc
    have hBH : B ≤ H := by
      rw [← hCt]
      intro b hb
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨b,hb⟩ : B) ⟨t,htg⟩)
    obtain ⟨a,ha⟩ := Matrix.PSL3Three.EightGeometry.sixteen_conjugate
      H A Q B t ht hH hd hcomm d inf_le_left hQ hQc hBH inferInstance hBc
    exact ⟨a,hCt.symm ▸ hAH a.property,ha.symm⟩
  have hzQ : z ∈ Q := by
    refine ⟨map_subtype_le _ (c.center_le c.mem_center), ?_⟩
    intro a ha
    obtain ⟨zz,hzz,hze⟩ := c.mem_center
    rw [← hze]
    exact congrArg Subtype.val (mem_center_iff.mp hzz
      ⟨a,c.sylow_lt.le ((hES.trans inf_le_left) ha)⟩)
  have hLN : L ≤ normalizer (Q : Set G) := by
    rw [hL]
    exact (le_inf (inf_le_left.trans H.le_normalizer)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer E))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨_,P,hP⟩ := largest_pair_normal_two_normalizer_of_source c hG hp
    (IsElementaryAbelian.isPGroup 2 Q) hzQ hLN
  apply false_of_eight_fusion_and_sylow_centralizes Q t htQ P
    (by rw [hP,hCt]; exact hUS.trans (map_subtype_le _)) hfamily
  exact central_involution_fusion_card H A Q t z ht hQ inf_le_left hQc hQAc hnf hinside houtside

/-- The original PSL₃(3) source branch is impossible. -/
theorem linear_three_component_false_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (eK : K ≃* Matrix.PSL3Three.PSL) : False := by
  obtain ⟨_,t,ht,hCt,hnf,A,hKA,d,hinner,hH,hd,hcomm,hinside,houtside⟩ :=
    linear_three_source_fusion c hG hempty hgen hb hp hUS eK
  exact linear_three_false_of_fusion_complement c hG hempty hgen hb hp hUS
    t ht hCt hnf A hKA d hinner hH hd hcomm hinside houtside

/-- The original source tuple, without extra normality or chosen-largest-pair assumptions. -/
theorem MathieuSourceSetup.linear_three_three_source_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* Matrix.PSL3Three.PSL) : False := by
  let : (K.subgroupOf H).Normal := small_component_normal hG.quasithin c.gamma
    (K.subgroupOf H) c.component
    (Or.inl ⟨(subgroupOfEquivOfLe c.component_le).trans eK⟩)
  obtain ⟨U,L,hpair,hUS,_,hbig,_⟩ :=
    exists_saturated_pair_aligned c.gamma S (c.sylow_lt.le.trans c.sylow_le)
  exact linear_three_component_false_of_source c hG hempty hgen hb
    ⟨hpair,hbig hstar⟩ hUS eK

end CFSG.Quasithin.Chapter2.Section05
