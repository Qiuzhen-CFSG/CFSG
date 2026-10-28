module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Omega
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.OddQuotient
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Involution placement in the selected centralizer

When the two-point stabilizer has rank one, two distinct commuting
involutions of M generate a four-group with a unique fixed coset. Its
centralizer lies in M. On the recognized perfect circle this places the
fixed subgroup of the involutory action inside its Borel, forcing the
quotient action, and hence the original action, to be inner. Thus every
involution of C_M(u) lies in B° C_B(B°). The earlier Omega identity then
gives the literal Sylow Omega identity in Corollary 16.6(a).

Source: GLS IV, Chapter 2, Corollary 16.6(a), using Proposition 16.5 and
Chapter 4, Lemma 3.4(c).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- Distinct commuting involutions in M have their common centralizer
inside M when the original two-point stabilizer has rank one. -/
public theorem source16_common_involution_centralizer_le
    (ha : ResidualAction Z M) {t u v : G} (htM : t ∉ M)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (hu : PFAppendixIII.IsInvolution u) (hv : PFAppendixIII.IsInvolution v)
    (huM : u ∈ M) (hvM : v ∈ M) (huv : Commute u v) (hne : u ≠ v) :
    centralizer ({u} : Set G) ⊓ centralizer ({v} : Set G) ≤ M := by
  let E := closure ({u,v} : Set G)
  let : IsKleinFour E := isKleinFour_closure_pair u v
    (by simpa only [pow_two] using hu.sq_eq_one)
    (by simpa only [pow_two] using hv.sq_eq_one) hu.ne_one hv.ne_one hne huv
  let : _root_.IsElementaryAbelian 2 E :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hEM : E ≤ M := by
    rw [closure_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact huM
    · exact Set.mem_singleton_iff.mp hx ▸ hvM
  have hC := elementary_centralizer_le_of_pair_rank_one ha htM hrank E
    (by rw [IsKleinFour.card_four]) hEM
  intro x hx
  apply hC
  change x ∈ centralizer (closure ({u,v} : Set G) : Set G)
  rw [centralizer_closure]
  intro y hy
  rcases Set.mem_insert_iff.mp hy with rfl | hy
  · exact hx.1 _ rfl
  · exact hx.2 _ hy

/-- The source fixed-subgroup argument puts every involution of C_M(u)
in the literal circle-centralizer product. The rank premise is precisely
Proposition 16.5; recognition and the fixed-group theorem are discharged. -/
public theorem source16_involution_mem_circle_centralizer_join
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {t u v : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (hv : PFAppendixIII.IsInvolution v) (hvB : v ∈ centralizer ({u} : Set G)) (hvM : v ∈ M) :
    let B := centralizer ({u} : Set G)
    let L := localCircleIn Z B
    v ∈ L ⊔ (B ⊓ centralizer (L : Set G)) := by
  let B := centralizer ({u} : Set G)
  let L := localCircleIn Z B
  let C := localCircle Z B
  let f := localCircleHom Z B
  have hLB : L ≤ B := localCircleIn_le Z B
  by_cases huv : u = v
  · subst v
    apply mem_sup_right
    refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hLB hx)
  have hBM := residualInvolution_centralizer_not_le h.disconnected r ht htM hu huD
  obtain ⟨z,hz,hzM,hzu⟩ := exists_distinguished_commuting_in_M h.disconnected r hu huD.1
  have hne : ∃ z ∈ Z, z ∈ B ∧ z ∈ M :=
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzu.eq,hzM⟩
  have hns := source16_centralizer_nonsolvable h r ha ht htM hu huD
  obtain ⟨hcenter,hperfect,hmodel,hBorel⟩ := localCircle_nonsolvable_structure h r ha B
    (r.involution_centralizer_ne_top h.disconnected hu) hBM hne hns
  let : C.Normal := localCircle_normal h.disconnected B hBM hne
  let : Group.IsPerfect C := ⟨hperfect⟩
  let n : normalizer (C : Set B) := ⟨⟨v,hvB⟩, by rw [normalizer_eq_top]; trivial⟩
  let a : MulAut C := C.normalizerMonoidHom n
  have hn : n ^ 2 = 1 := Subtype.ext (Subtype.ext hv.sq_eq_one)
  have ha2 : a ^ 2 = 1 := by rw [← map_pow, hn, map_one]
  have hcommon := source16_common_involution_centralizer_le ha htM hrank hu hv huD.1 hvM
    (mem_centralizer_singleton_iff.mp hvB).symm huv
  have hfix : a.fixedSubgroup ≤ M.comap f := by
    intro x hx
    have hfx : a x = x := (MulAut.mem_fixedSubgroup a x).mp hx
    have he := congrArg f hfx
    change v * f x * v⁻¹ = f x at he
    exact hcommon ⟨x.val.property, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  have hodd : Odd (Nat.card (center C)) := by
    rw [← hcenter]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  have hinner := bender_inner_of_fixedSubgroup_le_borel hmodel hBorel
    ((center C).quotientAut a) (by rw [← map_pow, ha2, map_one]) (by
      rw [← MulAut.map_fixedSubgroup_characteristic_odd (center C) hodd a ha2]
      exact map_mono hfix)
  obtain ⟨c,hc⟩ := (MulAut.centralQuotientAction_inner_iff (MulEquiv.refl _) a).mp
    (by
      obtain ⟨b,hb⟩ := hinner
      refine ⟨b, ?_⟩
      change MulAut.congr (MulEquiv.refl _) ((center C).quotientAut a) = MulAut.conj b
      rw [hb]
      exact MulAut.congr_conj _ _)
  let w := (f c)⁻¹ * v
  have hwB : w ∈ B := B.mul_mem (B.inv_mem c.val.property) hvB
  have hwC : w ∈ centralizer (L : Set G) := by
    rintro x ⟨xB,hxC,rfl⟩
    let xC : C := ⟨xB,hxC⟩
    have he := congrArg f (DFunLike.congr_fun hc xC)
    change v * f xC * v⁻¹ = f c * f xC * (f c)⁻¹ at he
    change f xC * w = w * f xC
    symm
    calc
      w * f xC = (f c)⁻¹ * (v * f xC * v⁻¹) * v := by dsimp only [w]; group
      _ = (f c)⁻¹ * (f c * f xC * (f c)⁻¹) * v := by rw [he]
      _ = f xC * w := by dsimp only [w]; group
  have hvprod : f c * w = v := by dsimp only [w]; group
  rw [← hvprod]
  exact mul_mem_sup (mem_map_of_mem B.subtype c.property) ⟨hwB,hwC⟩

/-- Corollary 16.6(a), as an ambient Omega identity for the actual selected
T₁. Only the genuine preceding Proposition 16.5 remains explicit. -/
public theorem source16_omega_of_pair_rank_one
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hg : ResidualGeneration Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hzu : Commute z u) (htu : Commute t u)
    (hmax : ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (T₁ : Subgroup G) (hTB : T₁ ≤ centralizer ({u} : Set G)) (hTM : T₁ ≤ M)
    (huT : u ∈ T₁) :
    omegaOneAmbient T₁ =
      omegaOneAmbient (T₁ ⊓ localCircleIn Z (centralizer ({u} : Set G))) ⊔ zpowers u := by
  let B := centralizer ({u} : Set G)
  let L := localCircleIn Z B
  let J := B ⊓ centralizer (L : Set G)
  have heq : omegaOneAmbient T₁ = omegaOneAmbient (T₁ ⊓ (L ⊔ J)) := by
    apply le_antisymm ?_ (omegaOneAmbient_mono inf_le_left)
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro v hv hv2
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl v ?_ hv2
    refine ⟨hv, ?_⟩
    by_cases hv1 : v = 1
    · rw [hv1]; exact one_mem _
    · exact source16_involution_mem_circle_centralizer_join h r ha ht htM hu huD hrank
        ⟨hv1,hv2⟩ (hTB hv) (hTM hv)
  exact heq.trans (source16_omega_intersection_circle_centralizer h r ha hg hz hzM ht htM
    hu huD hzu htu hmax T₁ huT)

end BenderSuzuki.ZD
