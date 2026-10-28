module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuFiveBounds
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.Source
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.FixedModel.Cocode
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension
public import CFSG.Quasithin.Chapter7.Section01To05.FixedSpaceSpan

/-!
# Pair avoidance in the large Mathieu cocode rows

The exceptional odd-prime fixed space is the actual five-dimensional
six-point core. Pair avoidance bounds its subspaces, giving rank at most
four in M23 and at most three in M24. In M23 every near-offender has rank
four and contains a conjugate of the marked common four-group. Its fixed
space is the heptad fixed space, where the proved avoidance bound is four.

Transport through the original group and linear markings controls the
literal induced Cartan parameter and higher Thompson subgroup. The
companion NonFFSourceMathieuCocodeBounds application uses these estimates
in E.6.27. Ambient distinguished-vector containment remains a separate
source obligation; it is not assumed as part of any marking.

Source: Aschbacher--Smith, H.14.2(1), H.15.2(3), H.15.7(3), and 8.1.2,
printed pp.397--402,713 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuAvoidance
open ChapterE ChapterH.Section13To16 Sporadic.Mathieu MathieuCode
open Sporadic.Mathieu.M24LocalGeometry

private theorem pair_orbit_eq : cocodeO2 = weightTwoOrbit := by
  ext v
  constructor
  · rintro ⟨B,hB,rfl⟩
    exact ⟨⟨B,hB⟩,rfl⟩
  · rintro ⟨B,rfl⟩
    exact ⟨B.val,B.property,rfl⟩

private theorem point_pair_orbit_eq : m23CocodeO2 = m23WeightTwoOrbit := by
  ext v
  constructor
  · rintro ⟨B,hB,h0,rfl⟩
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hB
    have h0' : (0 : Fin 24) = i ∨ (0 : Fin 24) = j := by simpa using h0
    rcases h0' with rfl | rfl
    · obtain ⟨k,hk⟩ := m23PointEquiv.surjective ⟨j,Ne.symm hij⟩
      have hk' : m23PointEmbedding k = j := congrArg Subtype.val hk
      refine ⟨k,?_⟩
      change pairVector (pointPair k) = pairVector ⟨{0,j},hB⟩
      apply congrArg pairVector
      apply Subtype.ext
      exact congrArg (fun x : Fin 24 => ({0,x} : Finset (Fin 24))) hk'
    · obtain ⟨k,hk⟩ := m23PointEquiv.surjective ⟨i,hij⟩
      have hk' : m23PointEmbedding k = i := congrArg Subtype.val hk
      refine ⟨k,?_⟩
      change pairVector (pointPair k) = pairVector ⟨{i,0},hB⟩
      apply congrArg pairVector
      apply Subtype.ext
      exact (congrArg (fun x : Fin 24 => ({0,x} : Finset (Fin 24))) hk').trans
        (Finset.pair_comm 0 i)
  · rintro ⟨i,rfl⟩
    exact ⟨(pointPair i).val,(pointPair i).property,by simp [pointPair],rfl⟩

/-- The odd-prime part of 8.1.2 in the native M24 cocode. The exceptional
five-dimensional fixed space uses the actual six-point map. -/
theorem m24_odd_avoiding_rank (A : Subgroup M24) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hA : Nat.card A = p)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace cocodeRepresentation A)
    (ha : Disjoint (I : Set Cocode) weightTwoOrbit) : Module.finrank (ZMod 2) I ≤ 3 := by
  by_cases hs : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation A) ≤ 3
  · exact (Submodule.finrank_mono hI).trans hs
  obtain ⟨_,hd,hf⟩ := large_cocode_fixed A hp ho hA (by omega)
  have hm := SixPoint.toFixedCocode_bijective A hf hd
  exact (SixPoint.finrank_le_two_of_bijective_fixedPoint_map A hf hm I hI
    (pair_orbit_eq.symm ▸ ha)).trans (by decide)

/-- The odd-prime part of 8.1.2 in M23, retaining the point-zero orbit. -/
theorem m23_odd_avoiding_rank (A : Subgroup M23) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hA : Nat.card A = p)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace m23CocodeRepresentation A)
    (ha : Disjoint (I : Set Cocode) m23WeightTwoOrbit) : Module.finrank (ZMod 2) I ≤ 4 := by
  by_cases hs : Module.finrank (ZMod 2) (fixedSpace m23CocodeRepresentation A) ≤ 4
  · exact (Submodule.finrank_mono hI).trans hs
  obtain ⟨_,hd,hf⟩ := m23_large_cocode_fixed A hp ho hA (by omega)
  rw [m23_cocode_fixedSpace_eq_map] at hI hd
  apply SixPoint.finrank_le_four_of_fixed_finrank (A.map pointEmbedding) hf _ hd I hI
    (point_pair_orbit_eq.symm ▸ ha)
  rintro ⟨a,b,hb,rfl⟩
  exact pointEmbedding_fixed b

private theorem common_not_cyclic : ¬ IsCyclic m23CommonKernel := by
  intro hc
  let := hc
  let := standardM23_commonKernel_structure.1
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := m23CommonKernel)
  have hdiv : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 m23CommonKernel) g)
  rw [hg,m23CommonKernel_card] at hdiv
  norm_num at hdiv

/-- The actual M23 near-offender estimate needed by 8.1.2. -/
theorem m23_nearOffender_avoiding_rank (A : Subgroup M23)
    (hA : IsElementaryTwo A) (hn : fixedCodim m23CocodeRepresentation A ≤ rank A + 1)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace m23CocodeRepresentation A)
    (ha : Disjoint (I : Set Cocode) m23WeightTwoOrbit) : Module.finrank (ZMod 2) I ≤ 4 := by
  let := hA.2
  have hlow := largeMathieu_nearOffender_fixedCodim_ge_five m23CocodeRepresentation
    (Or.inr (Or.inl ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩)) A hA hn
  have hr := (offender_rank_le_primeRank A).trans m23_twoRank_le_four
  have hcard : Nat.card A = 16 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hlog : rank A = n := by rw [rank,hn,Nat.log_pow Nat.one_lt_two]
    have he : n = 4 := by omega
    rw [hn,he]
    rfl
  obtain ⟨g,hg⟩ := standardM23_card16_contains_common_conjugate A hA.2 hcard
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (m23CocodeRepresentation.asGroupHom g)
  let J := I.comap e.toLinearMap
  have hJ : J ≤ fixedSpace m23CocodeRepresentation m23CommonKernel := by
    intro v hv a
    apply e.injective
    have hc := hI hv ⟨g * a.val * g⁻¹,hg (mem_map_of_mem (MulAut.conj g).toMonoidHom a.property)⟩
    change m23CocodeRepresentation g (m23CocodeRepresentation a.val v) =
      m23CocodeRepresentation g v
    change m23CocodeRepresentation (g * a.val * g⁻¹)
      (m23CocodeRepresentation g v) = m23CocodeRepresentation g v at hc
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right] using hc
  have haJ : Disjoint (J : Set Cocode) m23WeightTwoOrbit := by
    apply Set.disjoint_left.mpr
    intro v hv hp
    apply Set.disjoint_left.mp ha hv
    obtain ⟨i,rfl⟩ := hp
    exact ⟨g • i,(m23PairVector_equivariant g i).symm⟩
  rw [CocodeLocal.heptad_noncyclic_fixedSpace standardOctad
    standardOctad_contains_distinguished_point m23CommonKernel
    m23CommonKernel_le_octad common_not_cyclic] at hJ
  have hbound := CocodeLocal.heptad_fixedSpace_avoiding_finrank_le standardOctad
    standardOctad_contains_distinguished_point J hJ haJ
  exact (e.ofSubmodule' I).finrank_eq ▸ hbound


variable {G X : Type*} [Group G] [Finite G] [Group X]
    (W : Subgroup G) [IsElementaryAbelian 2 W]

/-- The marked image of an actual ambient subgroup, with no new action. -/
def markedSpace (U : Subgroup G) (E : Additive W ≃ₗ[ZMod 2] Cocode) :
    Submodule (ZMod 2) Cocode :=
  ((Chapter7.moduleSubgroup W).symm (U.subgroupOf W)).map E.toLinearMap

theorem markedSpace_finrank (U : Subgroup G) (hUW : U ≤ W)
    (E : Additive W ≃ₗ[ZMod 2] Cocode) :
    Module.finrank (ZMod 2) (markedSpace W U E) = rank U := by
  rw [markedSpace,E.finrank_map_eq,
    ←Chapter7.ambientSubmodule_log_card W,
    Chapter7.ambientSubmodule,(Chapter7.moduleSubgroup W).apply_symm_apply,
    map_subgroupOf_eq_of_le hUW]
  rfl

omit [Finite G] in
/-- Centralization of the original U becomes fixed vectors under the literal
marked image of every subgroup of the induced automizer. -/
theorem markedSpace_le_fixed (A U : Subgroup G)
    (hAN : A ≤ normalizer (W : Set G)) (hAU : A ≤ centralizer (U : Set G))
    (σ : Representation (ZMod 2) X Cocode) (f : Automizer W →* X)
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ a v, E (automizerRepresentation W a v) = σ (f a) (E v))
    (B : Subgroup (Automizer W)) (hB : B ≤ inducedAutomizer W A) :
    markedSpace W U E ≤ fixedSpace σ (B.map f) := by
  rw [←fixedSpace_map_equivariant (automizerRepresentation W) σ f E hE B]
  apply Submodule.map_mono
  intro v hv
  apply BinaryOffender.fixedSpace_antitone (automizerRepresentation W) hB
  apply (mem_fixedSpace_inducedAutomizer W A hAN v).mpr
  exact le_centralizer_iff.mp hAU hv

omit [Finite G] in
/-- Escaping centralizers avoid every vector whose centralizer is controlled. -/
theorem markedSpace_avoids (U M : Subgroup G)
    (E : Additive W ≃ₗ[ZMod 2] Cocode) (O : Set Cocode)
    (hcontrol : ∀ x : W, E (Additive.ofMul x) ∈ O →
      centralizer ({(x : G)} : Set G) ≤ M)
    (hescape : ¬ centralizer (U : Set G) ≤ M) :
    Disjoint (markedSpace W U E : Set Cocode) O := by
  apply Set.disjoint_left.mpr
  rintro v ⟨u,hu,rfl⟩ hv
  have huG : (u.toMul : G) ∈ U := hu
  exact hescape ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huG)).trans
    (hcontrol u.toMul hv))

/-- The native M23 estimates control both hypotheses of E.6.27 at a
large marked subspace avoiding the distinguished orbit. -/
theorem m23_local_action_bounds (A U : Subgroup G)
    (hWA : W ≤ A) (hAN : A ≤ normalizer (W : Set G))
    (hUW : U ≤ W) (hAU : A ≤ centralizer (U : Set G))
    (a : Automizer W ≃* M23) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) =
      m23CocodeRepresentation (a b) (E v))
    (ha : Disjoint (markedSpace W U E : Set Cocode) m23WeightTwoOrbit)
    (hr : 4 < rank U) :
    ChapterE.Section06.FixedPointBounds.nPrime (inducedAutomizer W A) ≤ 1 ∧
      ChapterB.thompsonJ A 1 ≤ centralizer (W : Set G) := by
  have hdim := markedSpace_finrank W U hUW E
  constructor
  · apply nPrime_le_one_of_no_odd_prime
    intro p hp ho b hb
    let B := zpowers (b.val : Automizer W)
    have hfix := markedSpace_le_fixed W A U hAN hAU m23CocodeRepresentation
      a.toMonoidHom E hE B (zpowers_le.mpr b.property)
    have hc : Nat.card (B.map a.toMonoidHom) = p := by
      rw [card_map_of_injective a.injective,Nat.card_zpowers]
      simpa using hb
    have hd := m23_odd_avoiding_rank (B.map a.toMonoidHom) hp ho hc _ hfix ha
    omega
  · apply sSup_le
    intro B hB
    by_contra hn
    let := hB.2.1
    have hBN := hB.1.trans hAN
    let I := inducedAutomizer W B
    have hI : IsElementaryTwo I :=
      ⟨fun hb => hn ((inducedAutomizer_eq_bot_iff hBN).mp hb),
        inducedAutomizer_elementary W B hBN⟩
    have hIm : IsElementaryTwo (I.map a.toMonoidHom) := by
      let := hI.2
      exact ⟨fun hb => hI.1 ((I.map_eq_bot_iff_of_injective a.injective).mp hb),
        IsElementaryAbelian.map a.toMonoidHom⟩
    have hnear := thompson_family_fixedCodim_le W A hWA hAN B hB
    rw [fixedCodim_map_equivariant (automizerRepresentation W) m23CocodeRepresentation
      a.toMonoidHom E hE,←rank_map_injective a.toMonoidHom a.injective] at hnear
    have hfix := markedSpace_le_fixed W B U hBN (hB.1.trans hAU)
      m23CocodeRepresentation a.toMonoidHom E hE I le_rfl
    have hd := m23_nearOffender_avoiding_rank _ hIm hnear _ hfix ha
    omega

/-- The same literal local action has no odd Cartan witness when an M24
cocode subspace of rank at least four avoids the distinguished orbit. -/
theorem m24_local_cartan_bound (A U : Subgroup G)
    (hAN : A ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (hAU : A ≤ centralizer (U : Set G))
    (a : Automizer W ≃* M24) (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation W b v) = cocodeRepresentation (a b) (E v))
    (ha : Disjoint (markedSpace W U E : Set Cocode) weightTwoOrbit)
    (hr : 3 < rank U) :
    ChapterE.Section06.FixedPointBounds.nPrime (inducedAutomizer W A) ≤ 1 := by
  have hdim := markedSpace_finrank W U hUW E
  apply nPrime_le_one_of_no_odd_prime
  intro p hp ho b hb
  let B := zpowers (b.val : Automizer W)
  have hfix := markedSpace_le_fixed W A U hAN hAU cocodeRepresentation
    a.toMonoidHom E hE B (zpowers_le.mpr b.property)
  have hc : Nat.card (B.map a.toMonoidHom) = p := by
    rw [card_map_of_injective a.injective,Nat.card_zpowers]
    simpa using hb
  have hd := m24_odd_avoiding_rank (B.map a.toMonoidHom) hp ho hc _ hfix ha
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuAvoidance
