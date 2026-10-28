module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeXi
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeComponentRank
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeComponentModels
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The original M22-code Xi residual lies in the A₆-containing component

The original involution centralizer contains a normal C-component above
the actual projective A₆ residual. Its three-rank is at least two and its
full two-core quotient has center of order at most three. The original
inside-core parabolic has a solvable two-residual with elementary-nine
quotient, so the normal alternative of adequate 1.3.4 is impossible.

The component detected by Xi is the same A₆-containing component: otherwise
its conjugate orbit would centralize that normal component modulo the
two-core and violate the ambient three-rank bound. This places the original
O²(H) inside it and excludes the swapped-component alternative. The original
A₆ section also excludes the linear-three models by their orders.

The symplectic, exceptional and Held alternatives remain explicit, as does
hcore. This does not yet prove 8.2.2(1), the later M22-code exclusion, or
same-orbit M24-cocode selection. The covering center is retained throughout.
Source: Aschbacher--Smith 8.2.2(1), printed p.715, refs/quasithin.pdf;
adequate 1.3.4 retains the genuine Sylow input and the Held correction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.MathieuShadowRows Chapter1 Chapter1.XiEmbedding
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original A₆-containing component has rank at least two and a quasisimple full two-core quotient with small center. -/
theorem sourceOrbit_m22_code_containing_component_three_rank
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    2 ≤ primeRank 3 (localResidual L z) ∧
      ∃ K : Subgroup G, K ≤ centralizer ({(z : G)} : Set G) ∧
        (K.subgroupOf (centralizer ({(z : G)} : Set G))).IsCComponent ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        2 ≤ primeRank 3 K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        Nat.card (center (K ⧸ pCore 2 K)) ≤ 3 := by
  obtain ⟨_,⟨e⟩⟩ := D.sourceOrbit_m22_code_centralizer_projective h d z hz hne
  have hr := projective_six_three_rank e
  obtain ⟨K,hKC,hK,hRK,hNK⟩ :=
    D.sourceOrbit_m22_code_centralizer_containing_component h d z hz hne
  have h2 : (z : G)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ z.property
  have ho : orderOf (z : G)=2 := orderOf_eq_prime h2 (fun he => hne (Subtype.ext he))
  let C := centralizer ({(z : G)} : Set G)
  let a := subgroupOfEquivOfLe hKC
  have hrK : 2 ≤ primeRank 3 K := hr.trans (primeRank_mono 3 hRK)
  have hrKC : 2 ≤ primeRank 3 (K.subgroupOf C) := by
    rw [primeRank_equiv 3 a]; exact hrK
  obtain ⟨hq,hc⟩ := rank_two_component_center_bound
    (h.simpleQTKE.involution_centralizer_sqtk ho) hK hrKC
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let := hq
  refine ⟨hr,K,hKC,hK,hRK,hNK,hrK,IsQuasisimple.of_mulEquiv b,?_⟩
  rwa [←Nat.card_congr (centerCongr b).toEquiv]

/-- The literal original two-residual is not normal in this same involution centralizer. -/
theorem sourceOrbit_m22_code_inside_core_not_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hHC : H ≤ centralizer ({(z : G)} : Set G)) :
    ¬ (((pResidual 2 H).map H.subtype).subgroupOf
      (centralizer ({(z : G)} : Set G))).Normal := by
  intro hn
  let X := (pResidual 2 H).map H.subtype
  let C := centralizer ({(z : G)} : Set G)
  have hXC : X ≤ C := (map_subtype_le _).trans hHC
  obtain ⟨hX,⟨e⟩,_⟩ := D.sourceOrbit_m22_code_inside_core_Xi h hmany hV hnon d hH hcore
  let : Group.IsSolvable X := hX.isSolvable
  let : (X.subgroupOf C).Normal := hn
  let : Group.IsSolvable (X.subgroupOf C) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hXC).toMonoidHom) (subgroupOfEquivOfLe hXC).injective
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  have hR : 2 ≤ primeRank 3 X := by
    apply three_rank_lower_of_surjective (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    rw [←IsElementaryAbelian.log_card_eq_primeRank]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨_,K,hKC,hK,_,_,hrK,_,_⟩ :=
    D.sourceOrbit_m22_code_containing_component_three_rank h.toHypothesis1221 d z hz hne
  have h2 : (z : G)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ z.property
  have ho : orderOf (z : G)=2 := orderOf_eq_prime h2 (fun he => hne (Subtype.ext he))
  have hrKC : 2 ≤ primeRank 3 (K.subgroupOf C) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hKC)]; exact hrK
  have hb := solvable_normal_three_rank_le_one
    (h.simpleQTKE.involution_centralizer_sqtk ho) hK hrKC (X.subgroupOf C)
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hXC)] at hb
  omega

private theorem sourceOrbit_m22_code_inside_core_detected_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        IsQuasisimple (XiQuotient K) ∧ X ≤ componentOrbit K (T : Subgroup G) ∧
        (Alternatives 3 (T : Subgroup G) P K ∨ HeldAlternative 3 (T : Subgroup G) P K) := by
  obtain ⟨z,hne,ho,hHC,P,hin,ha⟩ :=
    D.sourceOrbit_m22_code_inside_core_embedding h hmany hV hnon d hH hcore
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hHC (hH.1.1.2 ht))
  obtain ⟨K,hK,hq,hX,hm⟩ := ha.resolve_left
    (D.sourceOrbit_m22_code_inside_core_not_normal h hmany hV hnon d hH hcore z hz hne hHC)
  exact ⟨z,hne,ho,hHC,P,K,hin,hK,hq,hX,hm⟩

/-- The original Xi residual lies in the same normal component as the original point residual; all surviving intrinsic models remain explicit. -/
theorem sourceOrbit_m22_code_inside_core_same_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (XiQuotient K) ∧ Nat.card (center (XiQuotient K)) ≤ 3 ∧
        X ≤ K ∧ Nonempty (P ≃* Plane 3) ∧
        ((SymplecticModel 3 (XiQuotient K) ∧ IsCyclic (automizer (T : Subgroup G) P)) ∨
          ExceptionalModel (XiQuotient K) ∨ Nonempty (XiQuotient K ≃* Held.He)) := by
  obtain ⟨z,hne,ho,hHC,P,K,hin,hK,hq,hX,ha⟩ :=
    D.sourceOrbit_m22_code_inside_core_detected_component h hmany hV hnon d hH hcore
  let X := (pResidual 2 H).map H.subtype
  let C := centralizer ({(z : G)} : Set G)
  have hTC : (T : Subgroup G) ≤ C := hH.1.1.2.trans hHC
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hTC ht)
  obtain ⟨_,B,hBC,hB,hRB,hnB,hrB,hqB,hzB⟩ :=
    D.sourceOrbit_m22_code_containing_component_three_rank h.toHypothesis1221 d z hz hne
  have hXC : X ≤ C := (map_subtype_le _).trans hHC
  have hKC : K ≤ C := hK.1
  let : (B.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hnB
  have hrBC : 2 ≤ primeRank 3 (B.subgroupOf C) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hBC)]; exact hrB
  obtain ⟨_,⟨e⟩,_⟩ := D.sourceOrbit_m22_code_inside_core_Xi h hmany hV hnon d hH hcore
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  have hrX : 2 ≤ primeRank 3 X := by
    apply three_rank_lower_of_surjective (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    rw [←IsElementaryAbelian.log_card_eq_primeRank]
    norm_num [Nat.card_eq_fintype_card]
  have hrXC : 2 ≤ primeRank 3 (X.subgroupOf C) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hXC)]; exact hrX
  have hx : X.subgroupOf C ≤ componentOrbit (K.subgroupOf C) ((T : Subgroup G).subgroupOf C) := by
    apply (map_le_map_iff_of_injective C.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hXC,map_componentOrbit,
      map_subgroupOf_eq_of_le hKC,map_subgroupOf_eq_of_le hTC]
    exact hX
  have he := rank_two_component_eq_of_orbit_contains_rank_two
    (h.simpleQTKE.involution_centralizer_sqtk ho) hB hrBC hK.2 hx hrXC
  have heq : K = B := by
    have hm := congrArg (Subgroup.map C.subtype) he
    rwa [map_subgroupOf_eq_of_le hKC,map_subgroupOf_eq_of_le hBC] at hm
  have hRK : localResidual L z ≤ K := heq.symm ▸ hRB
  have hnK : C ≤ normalizer (K : Set G) := heq.symm ▸ hnB
  have hzK : Nat.card (center (XiQuotient K)) ≤ 3 := heq.symm ▸ hzB
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := hTC.trans hnK
  have hXK : X ≤ K := hX.trans
    (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) K le_rfl hTK)
  obtain ⟨_,⟨eR⟩⟩ := D.sourceOrbit_m22_code_centralizer_projective h.toHypothesis1221 d z hz hne
  have hnLin := not_linear_three_of_projective_six_injective eR (inclusion hRK)
    (inclusion_injective hRK)
  refine ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,?_⟩
  rcases ha with ha | ha
  · refine ⟨ha.1,?_⟩
    rcases ha.2 with hh | ⟨_,hm⟩
    · exact (hh.1.1 hTK).elim
    · rcases hm with hm | hm | ⟨_,hm⟩
      · exact (hnLin hm).elim
      · exact Or.inl hm
      · exact Or.inr (Or.inl hm)
  · exact ⟨ha.2.1,Or.inr (Or.inr ha.2.2.2)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
