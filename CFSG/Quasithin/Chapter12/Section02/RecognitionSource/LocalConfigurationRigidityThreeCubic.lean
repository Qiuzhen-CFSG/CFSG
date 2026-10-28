module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeResidual
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels
public import Theory.GroupAction.SixteenOddComplements.Five

/-!
# The four-group Sylow image and the original cubic prime

The elementary radical meets L in order sixteen, so it contains an
involution outside V. All involutions in the natural quotient SL(3,2)
are conjugate. Lifting those conjugacies, and using the dihedral Sylow
subgroup of SL(3,2), proves that the actual Sylow image in N_G(R)/R is
elementary abelian of order four.

The literal action of H on U has a normal P-image. If P had order five,
its faithful action on the sixteen-element U would prohibit this
four-group image. Thus P has order three. The final applications remove
cubic order from the hypotheses of the existing parabolic and Gaschütz
consumers. The remaining odd-core calculation and source assembly stay
with qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed pp.805--806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

private theorem component_sylow' (D : ChosenModule T L V) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let N := normalizer (L : Set G)
  obtain ⟨S,hS⟩ := (T.subtype D.sylow_normalizes_component).exists_subgroupOf_eq_of_normal
    (L.subgroupOf N)
  let e := subgroupOfEquivOfLe L.le_normalizer
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup (L.subgroupOf N)).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro hx
    exact ⟨⟨⟨x,L.le_normalizer x.property⟩,x.property⟩,hx,rfl⟩

/-- An elementary radical supplies involution lifts for the unique involution
class of the natural quotient. Consequently the actual Sylow image is a four-group. -/
theorem quotientSylow_elementary (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    IsElementaryAbelian 2 (quotientSylow C) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (radical T U) := B.elementary
  obtain ⟨e,_,_⟩ := A.natural
  let π : L →* Matrix.PSL3Two.PSL := Matrix.PSL3Two.equiv.toMonoidHom.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hπ : Function.Surjective π := Matrix.PSL3Two.equiv.surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker (x : L) : π x = 1 ↔ (x : G) ∈ V := by
    change Matrix.PSL3Two.equiv (e (QuotientGroup.mk' (pCore 2 L) x)) = 1 ↔ _
    rw [map_eq_one_iff Matrix.PSL3Two.equiv Matrix.PSL3Two.equiv.injective,
      map_eq_one_iff e e.injective, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    rw [← RigidityResidual.component_core_of_centralizers D B]
    change x ∈ pCore 2 L ↔ (x : G) ∈ (pCore 2 L).map L.subtype
    exact (mem_map_iff_mem L.subtype_injective).symm
  obtain ⟨u,hu,huV⟩ : ∃ u ∈ radical T U ⊓ L, u ∉ V := by
    by_contra! hn
    have hc := card_le_of_le (show radical T U ⊓ L ≤ V from hn)
    rw [radical_inf_component_card C B, RigidityKernel.chosen_card A] at hc
    norm_num at hc
  let uL : L := ⟨u,hu.2⟩
  have hu2 : uL ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (A := radical T U) u hu.1)
  have huπ : orderOf (π uL) = 2 := orderOf_eq_prime
    (by rw [← map_pow,hu2,map_one]) (fun hh => huV ((hker uL).mp hh))
  have hlift (a : Matrix.PSL3Two.PSL) (ha : a ^ 2 = 1) :
      ∃ x : L, π x = a ∧ x ^ 2 = 1 := by
    by_cases ha1 : a = 1
    · exact ⟨1,by simpa only [map_one] using ha1.symm,one_pow _⟩
    obtain ⟨g,hg⟩ := Matrix.PSL3Two.involutions_conjugate (π uL) a huπ
      (orderOf_eq_prime ha ha1)
    obtain ⟨l,rfl⟩ := hπ g
    refine ⟨MulAut.conj l uL, ?_, ?_⟩
    · simpa only [MulAut.conj_apply,map_mul,map_inv] using hg
    · rw [← map_pow,hu2,map_one]
  obtain ⟨S,hS⟩ := component_sylow' D
  let Q := S.mapSurjective hπ
  let q : S →* Q := {
    toFun x := ⟨π x,mem_map_of_mem π x.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' x y := Subtype.ext (map_mul π (x : L) (y : L)) }
  have hkerS (x : L) (hx : π x = 1) : x ∈ (S : Subgroup L) := by
    rw [hS]
    exact D.le_sylow ((hker x).mp hx)
  have hliftS (a : Q) (ha : a ^ 2 = 1) :
      ∃ x : S, q x = a ∧ x ^ 2 = 1 := by
    obtain ⟨x,hx,hx2⟩ := hlift a (congrArg Subtype.val ha)
    obtain ⟨y,hy,hyπ⟩ := a.property
    have hk : π (y⁻¹*x) = 1 := by rw [map_mul,map_inv,hx,hyπ,inv_mul_cancel]
    have hxS : x ∈ (S : Subgroup L) := by
      simpa only [mul_inv_cancel_left] using (S : Subgroup L).mul_mem hy (hkerS _ hk)
    exact ⟨⟨x,hxS⟩,Subtype.ext hx,Subtype.ext hx2⟩
  obtain ⟨j⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral Q
  have hgen (x : Q) : ∃ a b : Q, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ x = a*b := by
    have hm (z : DihedralGroup 4) : ∃ a b : DihedralGroup 4,
        a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ z = a*b := by
      cases z with
      | r i => exact ⟨.sr 0,.sr i,by simp [pow_two],by simp [pow_two],by simp⟩
      | sr i => exact ⟨1,.sr i,by simp,by simp [pow_two],by simp⟩
    obtain ⟨a,b,ha,hb,hx⟩ := hm (j x)
    exact ⟨j.symm a,j.symm b,by rw [← map_pow,ha,map_one],
      by rw [← map_pow,hb,map_one],j.injective (by simp only [map_mul,j.apply_symm_apply]; exact hx)⟩
  let E := quotientSylow C
  let : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
    (quotientSylow_card D A C B)
  let f : T →* E := {
    toFun t := ⟨quotient T U ⟨t,sylow_normalizes_radical C t.property⟩,
      ⟨⟨t,sylow_normalizes_radical C t.property⟩,t.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one (quotient T U))
    map_mul' x y := Subtype.ext (map_mul (quotient T U)
      ⟨x,sylow_normalizes_radical C x.property⟩ ⟨y,sylow_normalizes_radical C y.property⟩) }
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨t,ht,rfl⟩ := hx
    exact ⟨⟨t,ht⟩,rfl⟩
  let i : S →* T := {
    toFun s := ⟨s,hS.le s.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hsquare (s : S) : f (i s) ^ 2 = 1 := by
    obtain ⟨a,b,ha,hb,hab⟩ := hgen (q s)
    obtain ⟨x,hx,hx2⟩ := hliftS a ha
    obtain ⟨y,hy,hy2⟩ := hliftS b hb
    let k := (x*y)⁻¹*s
    have hk : π (k : L) = 1 := by
      have hh : q k = 1 := by
        dsimp [k]
        rw [map_mul,map_inv,map_mul,hx,hy,hab,inv_mul_cancel]
      exact congrArg Subtype.val hh
    have hk2 : k ^ 2 = 1 := Subtype.ext (Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (A := V) (k : G) ((hker _).mp hk)))
    have he : s = x*y*k := by dsimp [k]; group
    rw [he,map_mul,map_mul,map_mul,map_mul,mul_pow,mul_pow,← map_pow,← map_pow,
      ← map_pow,← map_pow,← map_pow,← map_pow,hx2,hy2,hk2]
    simp only [map_one,mul_one]
  have hZ : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤ radical T U :=
    le_sup_right.trans B.centralizer_split.symm.le
  have hnorm : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (B.component_centralizer_central.trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro e
  obtain ⟨t,rfl⟩ := hf e
  have ht := B.sylow_split.le t.property
  have hp : (t : G) ∈ (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) *
      (((T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    rwa [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
  obtain ⟨s,hs,z,hz,hprod⟩ := hp
  change s ∈ (T : Subgroup G) ⊓ L at hs
  change z ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) at hz
  let s' : S := ⟨⟨s,hs.2⟩,hS.ge hs.1⟩
  let z' : T := ⟨z,hz.1⟩
  have hz0 : f z' = 1 := by
    apply Subtype.ext
    change QuotientGroup.mk' ((radical T U).subgroupOf (normalizer (radical T U : Set G)))
      ⟨z,sylow_normalizes_radical C hz.1⟩ = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hZ hz)
  have ht' : t = i s' * z' := Subtype.ext hprod.symm
  rw [ht',map_mul,hz0,mul_one]
  exact hsquare s'

/-- The original prime subgroup is cubic: its faithful action on U cannot
have a normal five together with the actual elementary Sylow four-image. -/
theorem prime_card_three (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) : Nat.card P = 3 := by
  rcases odd_prime_three_or_five C with hp | hp
  · exact hp
  exfalso
  let := C.elementary
  have hPH : P ≤ H := by rw [C.overgroup]; exact le_sup_left
  have hUH : U ≤ H := C.core_le_sylow.trans C.sylow_le_overgroup
  let f : H →* MulAut U := U.normalizerMonoidHom.comp (inclusion C.overgroup_normalizes_core)
  let J := f.range
  let g : H →* J := f.rangeRestrict
  let P₀ := (P.subgroupOf H).map g
  let S₀ := ((T : Subgroup G).subgroupOf H).map g
  have hUker : U.subgroupOf H ≤ g.ker := by
    intro u hu
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (u : G) * (w : G) * (u : G)⁻¹ = w
    have hc : (w : G) * (u : G) = (u : G) * (w : G) :=
      le_centralizer U (show (u : G) ∈ U from hu) w w.property
    rw [← hc,mul_inv_cancel_right]
  have hres : ((P ⊔ U).subgroupOf H).map g = P₀ := by
    rw [subgroupOf_sup hPH hUH,Subgroup.map_sup,
      ((U.subgroupOf H).map_eq_bot_iff).mpr hUker,sup_bot_eq]
  have hnormal : P₀.Normal := by
    rw [← hres]
    let : ((P ⊔ U).subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer C.overgroup_normalizes_residual
    exact Subgroup.Normal.map inferInstance g f.rangeRestrict_surjective
  let := hnormal
  have hP : Nat.card P₀ = 5 := by
    let a : P →* J := g.comp (inclusion hPH)
    have ha : Function.Injective a := by
      apply (injective_iff_map_eq_one a).mpr
      intro p hp0
      apply Subtype.ext
      apply mem_bot.mp
      rw [← C.odd_centralizer_core_eq_bot (by decide)]
      refine ⟨p.property,?_⟩
      intro u hu
      have he := congrArg (fun k : J => ((k : MulAut U) ⟨u,hu⟩ : G)) hp0
      change (p : G) * u * (p : G)⁻¹ = u at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have he : a.range = P₀ := by
      rw [MonoidHom.range_comp,inclusion_range]
    rw [← he,← Nat.card_congr (MonoidHom.ofInjective ha).toEquiv,hp]
  have hk : g.ker = (centralizer (U : Set G)).subgroupOf H := by
    ext h
    change g h = 1 ↔ (h : G) ∈ centralizer (U : Set G)
    constructor
    · intro hh u hu
      have he := congrArg (fun k : J => ((k : MulAut U) ⟨u,hu⟩ : G)) hh
      change (h : G) * u * (h : G)⁻¹ = u at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hh
      apply Subtype.ext
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change (h : G) * (u : G) * (h : G)⁻¹ = u
      rw [← hh u u.property,mul_inv_cancel_right]
  have hS : Nat.card S₀ = 4 := by
    rw [show Nat.card S₀ = Nat.card (((T : Subgroup G).subgroupOf H).map g) from rfl,
      ← relIndex_ker,hk,relIndex_subgroupOf C.sylow_le_overgroup]
    have he := quotientSylow_card D A C B
    change Nat.card (image T U (T : Subgroup G)) = 4 at he
    rw [image_card _ (sylow_normalizes_radical C),← inf_relIndex_left,
      show (T : Subgroup G) ⊓ radical T U = radical T U from inf_eq_right.mpr inf_le_left] at he
    rw [← inf_relIndex_left]
    exact he
  let : IsElementaryAbelian 2 (quotientSylow C) := quotientSylow_elementary D A C B
  have hpow (t : H) (ht : (t : G) ∈ (T : Subgroup G)) : g t ^ 2 = 1 := by
    let tN : normalizer (radical T U : Set G) := ⟨t,sylow_normalizes_radical C ht⟩
    let tQ : quotientSylow C := ⟨quotient T U tN,⟨tN,ht,rfl⟩⟩
    have hq2 : (quotient T U tN) ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (quotientSylow C)) tQ)
    rw [← map_pow] at hq2
    have hr' : tN ^ 2 ∈ (radical T U).subgroupOf (normalizer (radical T U : Set G)) :=
      (QuotientGroup.eq_one_iff (tN ^ 2)).mp hq2
    have hr : (t : G) ^ 2 ∈ radical T U := hr'
    rw [← map_pow]
    rw [← MonoidHom.mem_ker,hk]
    exact hr.2
  let : IsElementaryAbelian 2 S₀ := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hS
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨s,hs⟩
      obtain ⟨t,ht,rfl⟩ := hs
      exact Subtype.ext (hpow t ht) }
  exact SixteenOddComplements.no_four_of_normal_five J.subtype J.subtype_injective
    (by simpa using C.dimension) P₀ hP S₀ hS

/-- The source cubic assertion, with the common calculation discharged. -/
theorem source_prime_card_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) : Nat.card P = 3 :=
  prime_card_three D A C (RigidityKernel.source_centralizers h D structural A C hnone)

/-- The remaining abelian-odd-core assertion now suffices for the complete
rigidity and parabolic conclusion; cubic order is no longer an input. -/
theorem source_parabolic_of_abelian_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hab : IsMulCommutative (pPrimeCore 2 (NormalizerQuotient T U))) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧ ParabolicSplitting T L V U :=
  source_parabolic_of_abelian_oddCore_and_cubic h D structural A C hnone hTI hab
    (source_prime_card_three h D structural A C hnone)

/-- Actual Gaschütz application after deriving the source cubic order.
The remaining odd-core calculation stays with qt-d-12213-local-rigidity. -/
theorem source_split_of_abelian_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hab : IsMulCommutative (pPrimeCore 2 (NormalizerQuotient T U))) :
    SplitLinearConfiguration L V 3 :=
  source_split_of_abelian_oddCore_and_cubic h D structural A C hnone hTI hab
    (source_prime_card_three h D structural A C hnone)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
