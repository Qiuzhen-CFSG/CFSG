module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThreeCubic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryParameters
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeOuter

/-!
# Ambient paired-plane containment and r greater than two

The original local join L T induces the full Aut(SL₃(2)) on the marked
natural–dual orbit W. Its kernel is a two-group: its intersection with L
lies in O₂(L), and L T/L is a two-group. Consequently that kernel lies in
Q = O₂(L T) and acts by inner automorphisms on the literal Q/W.

If the paired-plane centralizer escapes M, the earlier source construction
supplies a moving cubic with fixed index four on Q/W. Frattini descent kills
the full actor kernel, while preserving cubic movement. The outer-action
obstruction gives a contradiction and hence C_G(V₀) ≤ M. Paired-plane
conjugacy and the genuine E.6.11 moving-element theorem then give r ≥ 3;
the checked table values give s = m = 2 on the same orbit.

No equality between W and the chosen irreducible V, or between the whole
two-core and its commutator, is assumed. Binary weak closure and the
Baer–Suzuki endgame, the other doubled rows and final non-FF assembly remain.
Source: Aschbacher–Smith, 7.7.1 and 7.7.3, printed pp.703–704,709,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega DoubledBinaryThreeOuter
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original marked paired plane has its entire ambient centralizer in M.
The final cubic contradiction uses the literal Q/W and its Frattini quotient. -/
theorem sourceOrbit_binary_pairedPlane_centralizer_contained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          HasMarking D.sourceOrbit L E ∧
          centralizer (ambientPlane D.sourceOrbit E v f : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_cubic_quotient h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,?_⟩
  by_contra hout
  obtain ⟨H,C,A,hH,hHC,hHjoin,hwhole,hA,hAR,hAC,hcore,hrad,horbit,hWQ,
    hAQ,hAW,hWN,hsection,hquot,hindex⟩ := hescape hout
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let W₀ := D.sourceOrbit
  let X := Q ⧸ W₀.subgroupOf Q
  let := hWN
  let := quotientConjugationAction A Q W₀ hAQ hAW
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  have hJW : J ≤ normalizer (W₀ : Set G) :=
    sup_le hLN D.sourceOrbit_weakClosure_setup.normalizes
  let q : J →* MulAut BinaryLinearThree.Group := a.toMonoidHom.comp
    (W₀.normalizerMonoidHom.rangeRestrict.comp (inclusion hJW))
  have hqL (l : L) : q (inclusion (show L ≤ J from le_sup_left) l) = MulAut.conj (k l) := ha l
  have hVW : V ≤ W₀ := by
    change V ≤ D.sourceOrbit
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit _ _
  have houter : q ⟨t,(show (T : Subgroup G) ≤ J from le_sup_right) ht⟩ ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
    intro hi
    exact hnt ((doubledBinary_inner_iff_seed_normalizer V W₀ hVW E hV a.toMonoidHom
      hcov ⟨t,hJW ((show (T : Subgroup G) ≤ J from le_sup_right) ht)⟩).mp hi)
  have hqs : Function.Surjective q := doubledBinary_onto_of_outer q
    (inclusion (show L ≤ J from le_sup_left)) k hks hqL ⟨t,(show (T : Subgroup G) ≤ J from le_sup_right) ht⟩ houter
  have hkernel (j : J) : q j = 1 ↔ (j : G) ∈ centralizer (W₀ : Set G) := by
    change a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hJW j)) = 1 ↔ _
    rw [←a.map_one,a.injective.eq_iff]
    rw [Subtype.ext_iff]
    change inclusion hJW j ∈ W₀.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  obtain ⟨seed⟩ := hmodel
  let model := seed.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv
  have hseed : (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
    D.seedComparison.centralizer_eq_twoCore
      (D.seedComparison.projection_injective_of_linearThree h.quasisimple model)
  let K := L.subgroupOf J
  let S := (T : Subgroup G).subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : K ⊔ S = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hK : IsPGroup 2 (q.ker.subgroupOf K) := by
    let r : q.ker.subgroupOf K →* pCore 2 L := {
      toFun x := ⟨⟨x.val.val.val,x.val.property⟩,by
        rw [←hseed]
        exact centralizer_le hVW ((hkernel x.val.val).mp x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    apply pCore_isPGroup.of_injective r
    intro x y he
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : pCore 2 L => z.val.val) he)))
  have hkp : IsPGroup 2 q.ker := kernel_two_of_normal_supplement q K S
    T.isPGroup'.comap_subtype hgen hK
  have hkQ : ∀ j : J, q j = 1 → (j : G) ∈ Q := by
    intro j hj
    exact mem_map_of_mem J.subtype ((show q.ker ≤ pCore 2 J from le_sSup ⟨inferInstance,hkp⟩) hj)
  have hJQ : J ≤ normalizer (Q : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  let aX : J →* MulAut X :=
    @MulDistribMulAction.toMulAut J X _ _ (quotientConjugationAction J Q W₀ hJQ hJW)
  have hX : IsPGroup 2 X := (isPGroup_pCoreIn 2 J).to_quotient _
  have hkfr : q.ker ≤ ((frattini X).quotientAut.comp aX).ker := by
    intro j hj
    let x : Q := ⟨j.val,hkQ j hj⟩
    have he : aX j = MulAut.conj (QuotientGroup.mk' (W₀.subgroupOf Q) x) := by
      ext y
      induction y using QuotientGroup.induction_on with
      | H y => rfl
    change (frattini X).quotientAut (aX j) = 1
    rw [he]
    exact FrattiniAction.quotientAut_conj_eq_one hX _
  have hAL : A ≤ L := hAR.trans ((map_subtype_le _).trans inf_le_left)
  have hAJ : A ≤ J := hAL.trans le_sup_left
  let i : A →* J := inclusion hAJ
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨z,hz⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).mp inferInstance
  have hoz : orderOf z = 3 := (orderOf_eq_card_of_zpowers_eq_top hz).trans hA
  have ho : orderOf (i z) = 3 := (orderOf_injective i (inclusion_injective hAJ) z).trans hoz
  have hacts (r : A) : MulDistribMulAction.toMulAut A X r = aX (i r) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => rfl
  have hmove : aX (i z) ≠ 1 := by
    intro hz1
    have hhom : MulDistribMulAction.toMulAut A X = 1 := by
      apply MonoidHom.ext
      intro r
      have hzker : z ∈ (MulDistribMulAction.toMulAut A X).ker := by
        change MulDistribMulAction.toMulAut A X z = 1
        rw [hacts,hz1]
      have hle := (zpowers_le.mpr hzker)
      rw [hz] at hle
      exact hle (mem_top r)
    have ht : FixedPoints.subgroup A X = ⊤ := by
      apply top_unique
      intro x _ r
      have he := congrArg (fun b : A →* MulAut X => b r x) hhom
      exact he
    rw [ht,index_top] at hindex
    omega
  let g := k (inclusion hAL z)
  have hqg : q (i z) = MulAut.conj g := hqL (inclusion hAL z)
  have hg : orderOf g = 3 := by
    have hdiv : orderOf g ∣ 3 := by
      have hh := orderOf_map_dvd (k.comp (inclusion hAL)) z
      simpa only [g,MonoidHom.comp_apply,hoz] using hh
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with he | he
    · have hqz : q (i z) = 1 := by rw [hqg,orderOf_eq_one_iff.mp he,map_one]
      have hf := hkfr hqz
      exact (FrattiniAction.quotientAut_cubic_ne_one hX aX (i z) ho hmove hf).elim
    · exact he
  exact no_cubic_four_action hX aX q hqs hkfr (i z) ho hmove g hg hqg
    i z hz rfl hacts hindex.le

/-- Original 7.7.1: every subspace of corank at most two has controlled centralizer. -/
theorem sourceOrbit_binary_three_le_globalR
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : 3 ≤ globalR D.sourceOrbit := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hC⟩ :=
    D.sourceOrbit_binary_pairedPlane_centralizer_contained h hd hnon F hF hmodel
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  have hN := D.sourceOrbit_normalizer_eq_of_markedDoubled h hd
  have hp := all_plane_centralizers D.sourceOrbit L hLN E k hE hks v f hfv (hN.symm ▸ hC)
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  rw [←hN] at h61
  exact three_le_globalR_of_planes D.sourceOrbit E a hcov h61
    (fun _ hU hmax hn => Section06.maximal_escape_action_knownSimple h61 hU hmax hn) hp


/-- Both numerical conclusions of 7.7.1 hold on the original chosen orbit. -/
theorem sourceOrbit_binary_r_s_m
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    2 < globalR D.sourceOrbit ∧ globalS D.sourceOrbit = 2 ∧ localM D.sourceOrbit = 2 := by
  have hr := D.sourceOrbit_binary_three_le_globalR h hd hnon F hF hmodel
  obtain ⟨hm,ha,hs,hw⟩ := D.sourceOrbit_binary_small_parameters h hd F hF hmodel hnon
    ((by decide : (2 : ℕ∞) ≤ 3).trans hr)
  exact ⟨lt_of_lt_of_le (by decide : (2 : ℕ∞) < 3) hr,hs,hm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
