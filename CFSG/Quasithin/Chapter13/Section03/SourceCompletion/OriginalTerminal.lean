module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalRank
public import CFSG.Quasithin.ChapterE.Section01.QuotientLifting.Generation

/-!
# The conditional original unitary terminal contradiction

The original module, flag and preceding geometry give weak closure and a
minimal outside subgroup of generation parameter greater than two. Its Sylow
two-subgroup cannot be normal, since two-closed groups are solvable and have
generation parameter at most one. Thus the full E.2.2 Hall-actor construction
applies without an extra N_G(T) containment assumption. Its actual odd-prime
actor contradicts the explicit earlier 4.4.3 normalizer-control obligation.
The two geometric obligations and 13.3.14 noncentrality remain explicit.

Source: Aschbacher--Smith, 12.2.11(c), pp.798--799, and 13.3.16--20,
pp.893--896, in the combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]

/-- A minimal outside member with n(H)>2 cannot have a normal Sylow
2-subgroup: a two-closed finite group is solvable and has n(H)≤1.
This supplies the minimal-parabolic input without any N_G(T) assumption. -/
theorem unitary_hstar_minimalParabolic_of_large_generation
    (T : Sylow 2 G) (M H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 2 < generationParameter H) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  apply ChapterE.Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype T H
  apply Chapter3.HStar.minimalParabolic T hTM hH
  right
  intro hnormal
  have hclosed : IsTwoClosed H := ⟨T.subtype hH.1.1.2, hnormal⟩
  let : Group.IsSolvable H := hclosed.isSolvable
  have hsmall := generationParameter_le_one_of_solvable (G := H)
  omega

/-- The literal terminal Hall actor, with the strict rank bound and both
13.3.17 normalizer/intersection conclusions now derived from earlier geometry.
The genuine 13.3.14 movement and earlier geometry remain explicit. -/
theorem unitary_escaping_prime_actor_of_earlier_geometry
    (D:ChapterF.Section09.Setup G)
    [IsElementaryAbelian 2 D.V]
    (e:inducedAutomizer D.V D.L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive D.V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer D.V D.L) v,E0 (automizerRepresentation D.V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hTZ:(D.T:Subgroup G)≤normalizer (D.V₁:Set G))
    (hTU:(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hZ:Nat.card D.V₁=2) (hU:Nat.card D.Vplus=8)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=normalizer (D.L:Set G))
    (hout:¬D.H≤normalizer (D.L:Set G))
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTI:∀g∈normalizer (D.L:Set G),D.V⊓D.V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom=D.V)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G))) :
    ∃ H ∈ Chapter3.HStar (D.T:Subgroup G) (normalizer (D.L:Set G)),
      H≤D.H ∧ 2<generationParameter H ∧
      ∃ (p:ℕ) (A:Subgroup G),p.Prime ∧ 3<p ∧ Nat.card A=p ∧
        IsElementaryAbelian p A ∧ A≤H⊓normalizer (D.L:Set G) ∧
        A≤centralizer (D.V:Set G) ∧ ⁅A,D.L⁆≤D.L.pCoreIn 2 ∧
        ¬H⊓normalizer (A:Set G)≤normalizer (D.L:Set G) := by
  have hr := unitary_rank_gt_three_of_earlier_geometry D e E0 he0 hUV hZV hTZ hTU
    hZ hU hres hTL hVLT hred hsyl hNL hfaith hu B hBV hTB hB hHfull hm hG hTI
    hplanes hact
  have hcontrol := (unitary_original_parabolic_control D e E0 he0 hUV hZV hTZ hTU
    hZ hU hres hTL hVLT hred hNL hfaith B hBV hTB hB hHfull hm hTI).2
  have hcomm := unitary_intersection_commutator_eq_bot_of_source D hG e E0 he0
    hUV hZV hTZ hTU hZ hU hTL hVLT hred hsyl hcontrol hNL hu B hBV hTB hB hHfull hTI
  obtain ⟨H,hH,hHD,hn⟩ := exists_large_generation_hstar_of_original_module D
    (normalizer (D.L : Set G)) e E0 he0 hUV hZV hTZ hTU hZ hU hres hTL hcharL
    hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout (fun g _ hc => hcomm g hc)
    B hBV hTB hB hr hHfull hm hG
  have hP := unitary_hstar_minimalParabolic_of_large_generation D.T
    (normalizer (D.L : Set G)) H hTL hH hn
  obtain ⟨n,_,hbound,d,hescape⟩ :=
    ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.source_intrinsic_escape_of_parameter_gt_two
      (Chapter3.sqtk_of_mem_H hG hH.1.1.1) (D.T.subtype hH.1.1.2) hP hn
  have hLTN : D.LT ≤ normalizer (D.V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨p,A,hp,hp3,hAc,hAe,_,hAH,hAV,hAL,hAN⟩ := unitary_torus_prime_actor
    D.T D.L H D.V₁ hH.1.1.2 d (hn.trans_le hbound)
    (hstar_maximal_eq_overlap D.T _ H hH hP) hescape (le_sup_left.trans hLTN)
    hNL (le_sup_right.trans hLTN) hTI hZn hZV (hHD.trans hHfull.le)
    hres hfaith e E0 he0
  exact ⟨H,hH,hHD,hn,p,A,hp,hp3,hAc,hAe,hAH,hAV,hAL,hAN⟩

/-- The prime-order specialization of the earlier 4.4.3 normalizer theorem
used by 12.2.11(c). This statement has no Hall-escape or unitary-exclusion
conclusion among its assumptions. Its proof remains an earlier source input. -/
@[expose] def UnitaryPrimeNormalizerControl (L V : Subgroup G) : Prop :=
  ∀ (p : ℕ) (A : Subgroup G), p.Prime → 3 < p → Nat.card A = p →
    A ≤ normalizer (L : Set G) → A ≤ centralizer (V : Set G) →
    ⁅A,L⁆ ≤ L.pCoreIn 2 → normalizer (A : Set G) ≤ normalizer (L : Set G)

/-- The source terminal contradiction, conditional on the three independent
source inputs still needed here: plane geometry, maximal-escape action, and
odd-local normalizer control, as well as original 13.3.14 movement.
This is not an unconditional proof of Theorem 13.3.16. -/
theorem unitary_false_of_earlier_sources
    (D:ChapterF.Section09.Setup G)
    [IsElementaryAbelian 2 D.V]
    (e:inducedAutomizer D.V D.L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive D.V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer D.V D.L) v,E0 (automizerRepresentation D.V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hTZ:(D.T:Subgroup G)≤normalizer (D.V₁:Set G))
    (hTU:(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hZ:Nat.card D.V₁=2) (hU:Nat.card D.Vplus=8)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=normalizer (D.L:Set G))
    (hout:¬D.H≤normalizer (D.L:Set G))
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTI:∀g∈normalizer (D.L:Set G),D.V⊓D.V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom=D.V)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G)))
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  obtain ⟨H,_,_,_,p,A,hp,hp3,hAc,_,hAH,hAV,hAL,hAN⟩ :=
    unitary_escaping_prime_actor_of_earlier_geometry D e E0 he0 hUV hZV hTZ hTU
      hZ hU hres hTL hcharL hVLT hred hsyl hcharH hNL hfaith hu hout
      B hBV hTB hB hHfull hm hG hTI hplanes hact
  exact hAN (inf_le_right.trans (hodd p A hp hp3 hAc (hAH.trans inf_le_right) hAV hAL))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
