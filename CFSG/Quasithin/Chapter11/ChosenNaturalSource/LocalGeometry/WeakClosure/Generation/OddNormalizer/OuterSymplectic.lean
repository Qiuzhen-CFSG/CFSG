module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterField

/-!
# Excluding the symplectic field-four outer section

The original Sp₄(4) quotient has order divisible by 17 and 25. In all extra
B-models except PSU₅(4), the actual Sylow Frattini quotient has at most seven
binary generators, so its automorphism order is prime to 17. The two invariant
Sylow flag factors for PSU₅(4) give quotient actions avoiding 25 and a solvable
common kernel. A nonsolvable simple section cannot disappear in that kernel.
The previously proved C, alternating and binary PSU₄ exclusions handle the
remaining rows, preserving the original component cover throughout.

Source applies this to prove the original normalizer and Hall conclusions for
every nonbinary symplectic row. Final field-four linear assembly remains with
qt-d-1222-natural-odd-kernel-normalizer.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem no_section_of_quotient_pair
    {H R : Type*} [Group H] [Finite H] [Group R] [Finite R] [IsSimpleGroup R]
    {n : ℕ} (hn : n ∣ Nat.card R) (hR : ¬ Group.IsSolvable R)
    (hpair : HasSolvableQuotientPair n H)
    (U : Subgroup H) (f : U →* R) (hf : Function.Surjective f) : False := by
  obtain ⟨B,C,hB,hC,hsol,hBn,hCn⟩ := hpair
  let := hB
  let := hC
  let := hsol
  rcases simple_section_normal_or_quotient B U f hf with ⟨W,g,hg⟩ | ⟨W,g,hg⟩
  · let j : C.subgroupOf B →* (B ⊓ C : Subgroup H) :=
      { toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let : Group.IsSolvable (C.subgroupOf B) :=
      Group.isSolvable_of_isSolvable_injective (f := j)
        (fun x y he => Subtype.ext (Subtype.ext
          (congrArg (fun z : (B ⊓ C : Subgroup H) => (z : H)) he)))
    obtain ⟨Z,k,hk⟩ := simple_section_quotient_of_solvable_kernel hR (C.subgroupOf B) W g hg
    have hd : n ∣ (C.subgroupOf B).index :=
      hn.trans ((card_dvd_of_surjective k hk).trans Z.card_subgroup_dvd_card)
    exact hCn (hd.trans (C.relIndex_dvd_index_of_normal B))
  · exact hBn (hn.trans ((card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card))

private theorem no_outer_section_of_quotient_pair
    {Q R : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group R] [Finite R] [IsSimpleGroup R]
    {n : ℕ} (hn : n ∣ Nat.card R) (hR : ¬ Group.IsSolvable R)
    (P : Sylow 2 Q) (hpair : HasSolvableQuotientPair n (MulAut P))
    (U : Subgroup (MulAut.Outer Q)) (f : U →* R) (hf : Function.Surjective f) : False := by
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  let H := MulAction.stabilizer (MulAut Q) (P : Subgroup Q)
  let F := fixingSubgroup (MulAut Q) (P : Set Q)
  let r : H →* MulAut P :=
    { toFun := fun a => (a.val.subgroupMap (P : Subgroup Q)).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let i : r.ker →* F :=
    (H.subtype.comp r.ker.subtype).codRestrict F (by
      intro a
      apply (mem_fixingSubgroup_iff (MulAut Q)).mpr
      intro x hx
      change (a.val.val : MulAut Q) x = x
      exact congrArg (fun b : MulAut P => ((b ⟨x,hx⟩ : P) : Q)) a.property)
  have hi : Function.Injective i := by
    intro a b hab
    have hab' : (a.val.val : MulAut Q) = b.val.val :=
      congrArg (fun z : F => (z : MulAut Q)) hab
    exact Subtype.ext (Subtype.ext hab')
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective hi
  let q := (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Q) x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Q (a • P) P
    have hm : MulAut.conj g * a ∈ H := by
      change (MulAut.conj g * a) • (P : Subgroup Q) = (P : Subgroup Q)
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * a,hm⟩,?_⟩
    change QuotientGroup.mk' (MulAut.innerSubgroup Q) (MulAut.conj g * a) = _
    have hi : QuotientGroup.mk' (MulAut.innerSubgroup Q) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [map_mul,hi,one_mul]
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel hR r.ker
    (U.comap q) (f.comp (q.subgroupComap U))
    (hf.comp (q.subgroupComap_surjective_of_surjective U hq))
  let e := QuotientGroup.quotientKerEquivRange r
  let j := r.range.subtype.comp e.toMonoidHom
  let a := W.equivMapOfInjective j (r.range.subtype_injective.comp e.injective)
  exact no_section_of_quotient_pair hn hR hpair (W.map j)
    (g.comp a.symm.toMonoidHom) (hg.comp a.symm.surjective)

private theorem no_seventeen_small_sylow_outer_section
    {Q R : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group R] [Finite R] [IsSimpleGroup R]
    (h17 : 17 ∣ Nat.card R) (hR : ¬ Group.IsSolvable R)
    (P : Sylow 2 Q) (hP : Nat.card (P ⧸ frattini P) ≤ 128)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* R) (hf : Function.Surjective f) : False := by
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := h17.trans (MulAut.simple_outer_section_card_dvd_frattini_aut P hR U f hf)
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  obtain ⟨n,hn⟩ := (P.isPGroup'.to_quotient (frattini P)).exists_card_eq
  have hn7 : n ≤ 7 := by
    by_contra! h
    have hpow : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
    rw [←hn] at hpow
    norm_num at hpow
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn] at hd
  interval_cases n <;> norm_num [Fin.prod_univ_succ] at hd

private theorem odd_model_frattini_small
    {Q : Type*} [Group Q] [Finite Q]
    (hm : ChapterA.Section02.IsTheoremBOddModel Q) :
    ∃ P : Sylow 2 Q, Nat.card (P ⧸ frattini P) ≤ 128 := by
  let P : Sylow 2 Q := Classical.choice inferInstance
  refine ⟨P,?_⟩
  have lin {n q : ℕ} (hn : n ≤ 4) (ho : Odd q)
      (h : ClassicalGroup.IsPSL Q n q) : Nat.card (P ⧸ frattini P) ≤ 128 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Theory.SpecificGroups.OddClassicalSylowFrattini.psl_card_le_128 hn
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho
        (by simpa using hF)) (P.mapSurjective e.surjective)
  have uni {n q : ℕ} (hn : n ≤ 4) (ho : Odd q)
      (h : ClassicalGroup.IsPSU Q n q) : Nat.card (P ⧸ frattini P) ≤ 128 := by
    obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := h
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Theory.SpecificGroups.OddClassicalSylowFrattini.psu_card_le_128 J hn
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF)
      (P.mapSurjective e.surjective)
  cases hm with
  | linear_two q ho hm => exact lin (by decide) ho hm
  | linear_three p a _ ho _ hm => exact lin (by decide) ho.pow hm
  | unitary_three p a _ ho _ hm => exact uni (by decide) ho.pow hm
  | symplectic p _ ho hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Theory.SpecificGroups.OddClassicalSylowFrattini.psp_four_card_le_128
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho
        (by simpa using hF)) (P.mapSurjective e.surjective)
  | g2 p hp ho hm =>
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
    exact Atlas.G2.OddSylowFrattini.frattini_card_le ho hF (P.mapSurjective e.surjective)
  | linear_four p _ hf hm =>
    obtain ⟨k,rfl⟩ := hf
    exact lin le_rfl ((even_two.pow_of_ne_zero (by positivity)).add_one) hm
  | unitary_four p hp hm hm' =>
    obtain ⟨b,hb⟩ := hm
    have hb0 : b ≠ 0 := by
      intro h
      simp only [h,pow_zero] at hb
      have := hp.two_le
      omega
    have he : Even (p + 1) := hb.symm ▸ even_two.pow_of_ne_zero hb0
    exact uni le_rfl (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)) hm'

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S in
/-- The full field-four symplectic quotient cannot be an actual outer section. -/
theorem moved_outer_not_field_four_symplectic {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    (hf : S.field.degree = 2)
    (e : (L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier) : False := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient L) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (L ⧸ pCore 2 L))) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hc : Nat.card (coreCentralQuotient L) = 979200 := by
    have hcard := card_eq_card_quotient_mul_card_subgroup (center (L ⧸ pCore 2 L))
    have hz : Nat.card (center (L ⧸ pCore 2 L)) = 1 := by
      rw [Nat.card_congr (centerCongr e).toEquiv,
        Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,card_bot]
    rw [hz,mul_one,Nat.card_congr e.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hcard
    rw [←hcard]
    norm_num [S.field.card_eq,hf]
  obtain ⟨hC,hAlt,_⟩ := moved_outer_section_exclusions D S K hK ho
  have hU4 {n : ℕ} (hn : 1 ≤ n) (h : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) :
      False := moved_outer_not_binary_unitary_four D S K hK ho hn h
  obtain ⟨U,f,hfs⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  let g := f.comp a.symm.toMonoidHom
  have hg : Function.Surjective g := hfs.comp a.symm.surjective
  have h17 : 17 ∣ Nat.card (coreCentralQuotient L) := by rw [hc]; decide
  have h25 : 25 ∣ Nat.card (coreCentralQuotient L) := by rw [hc]; decide
  have hR := Group.IsPerfect.not_isSolvable (coreCentralQuotient L)
  have hsmall (P : Sylow 2 (K ⧸ center K))
      (hP : Nat.card (P ⧸ frattini P) ≤ 128) : False :=
    no_seventeen_small_sylow_outer_section h17 hR P hP (U.map j) g hg
  cases hm with
  | alternating n _ he => exact hAlt n he
  | odd h => obtain ⟨P,hP⟩ := odd_model_frattini_small h; exact hsmall P hP
  | bender h => exact hC (.bender h)
  | linear_binary n hn h => exact hC (.linear_binary n hn h)
  | symplectic_binary h =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
    exact hsmall P (Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini.frattini_card_le_of_equiv
      hF e P)
  | rank_two n h =>
    cases h with
    | linear hn h => exact hC (.rank_two n (.linear hn h))
    | unitary_four hn h => exact hU4 hn h
    | unitary_five hn h =>
      subst n
      obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := h
      let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
      obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
      let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
      have hpair := Theory.SpecificGroups.UnitaryFive.Flag.sylow_solvableQuotientPair_four
        (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)
        hcard hconj rfl (e.trans a) P
      exact no_outer_section_of_quotient_pair h25 hR P hpair (U.map j) g hg
    | symplectic hn h => exact hC (.rank_two n (.symplectic hn h))
    | g2 hn h => exact hC (.rank_two n (.g2 hn h))
    | triality hn h => exact hC (.rank_two n (.triality hn h))
    | ree_f4 m hm hn h => exact hC (.rank_two n (.ree_f4 m hm hn h))
    | symplectic_derived hn h => exact hC (.rank_two n (.symplectic_derived hn h))
    | g2_derived hn h => exact hC (.rank_two n (.g2_derived hn h))
    | tits hn h => exact hC (.rank_two n (.tits hn h))
  | sporadic h =>
    rcases h with ⟨name,he⟩ | he | he
    · by_cases hj : name = .j3
      · subst name
        let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
        exact hsmall P ((Theory.SpecificGroups.FiniteModelSylowFrattini.j3_card_le_thirtytwo
          he.some P).trans (by decide))
      · exact hC (.sporadic (.inl ⟨name,hj,he⟩))
    · exact hC (.sporadic (.inr he))
    · let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
      exact hsmall P (Theory.SpecificGroups.FiniteModelSylowFrattini.mcl_card_le_128 he.some P)

include D S in
/-- Every actual outer section has the full linear field-four quotient. -/
theorem moved_outer_linear_field_four {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) :
    S.field.degree = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) := by
  obtain ⟨hf,he⟩ := moved_outer_field_four D S K hK hm ho
  rcases he with hl | hs
  · exact ⟨hf,hl⟩
  · obtain ⟨e⟩ := hs
    exact (moved_outer_not_field_four_symplectic D S K hK hm ho hf e).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
