module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicComponents
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel
public import Theory.GroupTheory.SimpleSectionOrder
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Identifying the cubic containing component modulo its two-core

The M₂₂ seed survives the containing component's solvable two-core and
central quotient kernels. Conversely, that simple quotient survives the
central kernel of the inclusion into the original full J₄ cover. Its order
is therefore divisible by |M₂₂| and divides |J₄|. Among the actual A.3.6
three-cover models these constraints exclude both alternating rows and
all classical rows: their field cubes bound the possible parameters, whose
projective orders fail M₂₂ divisibility. The remaining quotient is 3.M₂₂.

The same simple-section divisibility makes the seed surject onto this
component's central quotient. Perfect central nongeneration then proves
that the original seed together with the component's two-core is the
whole component. The literal Hall obstruction supplies these conclusions
on the same covering component and centralizer inclusion maps.

This does not identify the full cubic centralizer residual or establish
ambient pushing-up uniqueness. The original residual placement and the
separate involution/fixed-line comparison remain to be constructed.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612, and A.3.6;
the Hall consumer is 4.4.14, printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter1.Section02.LocalModels Chapter4.Section02.RankOneReciprocalEscape
private theorem prime_cube {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hd : p ^ 3 ∣ 86775571046077562880) : p = 3 ∨ p = 11 := by
  have hd1 : p ∣ 86775571046077562880 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rw [show 86775571046077562880 =
    2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 by norm_num] at hd1
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 21 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0), Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43)] at hd1
  simp only [or_assoc] at hd1
  rcases hd1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at hd
  all_goals norm_num at ho
  all_goals norm_num

private theorem binary_cube {n : ℕ} (hd : (2 ^ n) ^ 3 ∣ 86775571046077562880) : n ≤ 7 := by
  by_contra hn
  have hh : 2 ^ 24 ∣ 86775571046077562880 :=
    (Nat.pow_dvd_pow 2 (by omega : 24 ≤ n * 3)).trans (by simpa only [pow_mul] using hd)
  norm_num at hh

private theorem classical_order_impossible (b : Bool) (q : ℕ)
    (hq : (∃ n, 1 ≤ n ∧ q = 2 ^ n) ∨ (q.Prime ∧ Odd q))
    (hd : q ^ 3 ∣ 86775571046077562880)
    (hm : 443520 ∣ if b then (q^3+1)*q^3*(q^2-1) / Nat.gcd 3 (q+1)
      else q^3*(q^3-1)*(q^2-1) / Nat.gcd 3 (q-1)) : False := by
  rcases hq with ⟨n,hn,rfl⟩ | ⟨hp,ho⟩
  · have hn7 := binary_cube hd
    interval_cases n <;> cases b <;> norm_num at hm
  · rcases prime_cube hp ho hd with rfl | rfl <;> cases b <;> norm_num at hm

private theorem not_unitary_two {X : Type*} [Group X] [Group.IsPerfect X]
    (h : IsSU X 3 2) : False := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := h
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective (f := J.specialToProjective.comp e.toMonoidHom)
      (J.specialToProjective_surjective.comp e.surjective)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [HermitianForm.FixedFieldTwo.card_projective J hcard hconj]
      norm_num)
  exact Group.IsPerfect.not_isSolvable _
    (HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj)

private def unitaryCentralQuotient {F X : Type*} [Field F] [Finite F] [Group X]
    (J : HermitianForm 3 F) {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (e : X ≃* J.specialSubgroup) :
    (X ⧸ center X) ≃* ProjectiveSpecialUnitaryMatrixGroup J := by
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  have hz : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ :=
    (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
  exact (centerQuotientCongr e).trans
    ((QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hz).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective))

private theorem not_classical_of_orders {X : Type*} [Group X] [Group.IsPerfect X]
    (b : Bool) (q : ℕ) (hq : CoverParameter b q) (hm : IsSLSign X b 3 q)
    (hseed : 443520 ∣ Nat.card (X ⧸ center X))
    (hhost : Nat.card (X ⧸ center X) ∣ 86775571046077562880) : False := by
  have hparam : (∃ n, 1 ≤ n ∧ q = 2 ^ n) ∨ (q.Prime ∧ Odd q) := by
    rcases hq with ⟨n,hn,hq,_⟩ | hq
    · exact .inl ⟨n,hn,hq⟩
    · exact .inr hq
  cases b with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let a : (X ⧸ center X) ≃* PSL(3,F) := centerQuotientCongr e
    rw [Nat.card_congr a.toEquiv] at hseed hhost
    have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card.trans hhost
    rw [Matrix.PSL3.LinearThree.card_unipotent,hF] at hd
    rw [Matrix.PSL3.LinearThree.card_projective,hF] at hseed
    exact classical_order_impossible false q hparam hd hseed
  | true =>
    change IsSU X 3 q at hm
    have hq2 : 2 < q := by
      rcases hparam with ⟨n,hn,rfl⟩ | ⟨hp,ho⟩
      · have hn2 : 2 ≤ n := by
          by_contra hn2
          have he : n = 1 := by omega
          subst n
          exact not_unitary_two (by simpa using hm)
        exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
          (Nat.pow_le_pow_right (by decide) hn2)
      · have := hp.two_le
        have hne : q ≠ 2 := by rintro rfl; norm_num at ho
        omega
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    have hfixed : Nat.card {x : F // J.conj x = x} = q := by
      rcases hparam with ⟨n,hn,rfl⟩ | ⟨hp,_⟩
      · exact FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
      · let : Fact q.Prime := ⟨hp⟩
        simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
          J.conj q 1 (by decide) (by simpa using hF) (by simpa using hconj)
    let a := unitaryCentralQuotient J hq2 hF hfixed e
    rw [Nat.card_congr a.toEquiv] at hseed hhost
    have hd := (J.cube_dvd_card_projective hF hfixed).trans hhost
    rw [Representation.SU3.BinaryDegree.card_projective J hF hfixed] at hseed
    exact classical_order_impossible true q hparam hd hseed

private theorem m22Cover_of_orders {X : Type*} [Group X] [Group.IsPerfect X]
    (hm : ThreeCoverModel X)
    (hseed : 443520 ∣ Nat.card (X ⧸ center X))
    (hhost : Nat.card (X ⧸ center X) ∣ 86775571046077562880) : IsM22Cover X := by
  cases hm with
  | classical b q hq he => exact (not_classical_of_orders b q hq he hseed hhost).elim
  | alternating_six he =>
    rw [Nat.card_congr he.2.2.some.toEquiv,nat_card_alternatingGroup] at hseed
    norm_num at hseed
  | alternating_seven he =>
    rw [Nat.card_congr he.2.2.some.toEquiv,nat_card_alternatingGroup] at hseed
    norm_num at hseed
  | mathieu he => exact he

/-- An M₂₂ covering seed in a three-cover component of a full J₄ cover
forces its two-core quotient to be the actual triple cover of M₂₂. -/
theorem cubic_component_twoCore_m22
    {S Q K : Type*} [Group S] [Finite S] [Group Q] [Finite Q] [Group K] [Finite K]
    [IsQuasisimple S] [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (es : (S ⧸ center S) ≃* Sporadic.Mathieu.M22)
    (i : S →* Q) (hi : Function.Injective i)
    (j : Q →* K) (hj : Function.Injective j)
    (ek : (K ⧸ center K) ≃* Janko4.Model)
    (hm : ThreeCoverModel (Q ⧸ pCore 2 Q)) : IsM22Cover (Q ⧸ pCore 2 Q) := by
  let Y := Q ⧸ pCore 2 Q
  let Z := Y ⧸ center Y
  let π : Q →* Z := (QuotientGroup.mk' (center Y)).comp (QuotientGroup.mk' (pCore 2 Q))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup Z := IsQuasisimple.simple
  let : Group.IsPerfect Z := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Y)) (QuotientGroup.mk'_surjective _)
  have hz : ¬ Group.IsSolvable Z := Group.IsPerfect.not_isSolvable Z
  let : Group.IsSolvable π.ker := by
    have he : π.ker = centralPreimage (pCore 2 Q) := by
      ext x
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact centralPreimage_pCore_isSolvable 2
  let r := π.comp i
  let : Group.IsSolvable r.ker := by
    let g : r.ker →* π.ker := {
      toFun x := ⟨i x.val,x.property⟩
      map_one' := by ext; exact map_one i
      map_mul' x y := by ext; exact map_mul i x.val y.val }
    exact Group.isSolvable_of_isSolvable_injective (f := g)
      (fun x y h => Subtype.ext (hi (congrArg (fun z : π.ker => (z : Q)) h)))
  let ps := es.toMonoidHom.comp (QuotientGroup.mk' (center S))
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : IsSimpleGroup Sporadic.Mathieu.M22 := es.symm.isSimpleGroup
  let : Group.IsPerfect Sporadic.Mathieu.M22 := Group.IsPerfect.ofSurjective (f := ps)
    (es.surjective.comp (QuotientGroup.mk'_surjective (center S)))
  have hd := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable Sporadic.Mathieu.M22) ps
    (es.surjective.comp (QuotientGroup.mk'_surjective (center S))) r
  rw [Sporadic.Mathieu.m22_order] at hd
  let t := ek.toMonoidHom.comp ((QuotientGroup.mk' (center K)).comp j)
  have htker : t.ker ≤ center Q := by
    intro x hx
    have hx' : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp
      (ek.injective (hx.trans ek.map_one.symm))
    exact mem_center_iff.mpr (fun y => hj (by simpa only [map_mul] using mem_center_iff.mp hx' (j y)))
  let : Group.IsSolvable t.ker := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective htker)
  have hh := SimpleSection.card_dvd_of_solvable_representation hz π hπ t
  rw [Janko4.Cardinality.model_card] at hh
  exact m22Cover_of_orders hm hd hh


/-- An injective M₂₂ covering seed supplements the two-core of an M₂₂ covering quotient. -/
theorem m22_seed_covers_twoCore
    {S Q : Type*} [Group S] [Finite S] [Group Q] [Finite Q] [IsQuasisimple S]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (es : (S ⧸ center S) ≃* Sporadic.Mathieu.M22)
    (i : S →* Q) (hi : Function.Injective i)
    (eq : ((Q ⧸ pCore 2 Q) ⧸ center (Q ⧸ pCore 2 Q)) ≃* Sporadic.Mathieu.M22) :
    i.range ⊔ pCore 2 Q = ⊤ := by
  let Y := Q ⧸ pCore 2 Q
  let π := QuotientGroup.mk' (pCore 2 Q)
  let z := QuotientGroup.mk' (center Y)
  let r := z.comp (π.comp i)
  let N := centralPreimage (pCore 2 Q)
  let : Group.IsSolvable N := centralPreimage_pCore_isSolvable 2
  let : Group.IsSolvable r.ker := by
    let g : r.ker →* N := {
      toFun x := ⟨i x.val,(QuotientGroup.eq_one_iff (π (i x.val))).mp x.property⟩
      map_one' := by ext; exact map_one i
      map_mul' x y := by ext; exact map_mul i x.val y.val }
    exact Group.isSolvable_of_isSolvable_injective (f := g)
      (fun x y h => Subtype.ext (hi (congrArg (fun z : N => (z : Q)) h)))
  let : Group.IsSolvable r.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let ps := es.toMonoidHom.comp (QuotientGroup.mk' (center S))
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : IsSimpleGroup Sporadic.Mathieu.M22 := es.symm.isSimpleGroup
  let : Group.IsPerfect Sporadic.Mathieu.M22 := Group.IsPerfect.ofSurjective (f := ps)
    (es.surjective.comp (QuotientGroup.mk'_surjective (center S)))
  have hd := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable Sporadic.Mathieu.M22) ps
    (es.surjective.comp (QuotientGroup.mk'_surjective (center S))) r.rangeRestrict
  have htop : r.range = ⊤ := r.range.eq_top_of_le_card (by
    rw [Nat.card_congr eq.toEquiv]
    exact Nat.le_of_dvd Nat.card_pos hd)
  have hm : (π.comp i).range.map z = ⊤ := by
    rw [MonoidHom.map_range]
    exact htop
  have he := congrArg (comap z) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at he
  have ht := eq_top_of_sup_center_eq_top (π.comp i).range he
  have hiπ : i.range.map π = ⊤ := (MonoidHom.map_range π i).trans ht
  have hh := congrArg (comap π) hiπ
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
  exact hh

open Chapter4 Chapter4.Section04
/-- The component containing the original cubic seed has the genuine M₂₂
triple cover as its two-core quotient, and the seed generates it together
with its two-core. The full covering component is retained. -/
theorem pushingUp_cubic_component_m22 {G : Type*} [Group G] [Finite G]
    {L V A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hn : K.Normal) (e : (K ⧸ center K) ≃* Janko4.Model) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
    ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
      (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set R)) ∈
        solvableResidual (centralizer ({x} : Set R)) ∧
      IsQuasisimple (solvableResidual (centralizer ({x} : Set R))) ∧
      Nonempty (((solvableResidual (centralizer ({x} : Set R))) ⧸
        center (solvableResidual (centralizer ({x} : Set R)))) ≃* Sporadic.Mathieu.M22) ∧
      ∃! Q : Subgroup (centralizer ({(x : K)} : Set K)),
        Q.IsCComponent ∧
        (solvableResidual (centralizer ({x} : Set R))).map
          (R.subtype.elementCentralizerMap x) ≤ Q ∧ Q.Normal ∧
        IsQuasisimple (Q ⧸ pCore 2 Q) ∧
        (∃ c : center (Q ⧸ pCore 2 Q), orderOf c = 3) ∧
        Chapter1.Section02.LocalModels.IsM22Cover (Q ⧸ pCore 2 Q) ∧
        (solvableResidual (centralizer ({x} : Set R))).map
          (R.subtype.elementCentralizerMap x) ⊔ Q.pCoreIn 2 = Q := by
  obtain ⟨x,hx,hqx,hres,hs,⟨es⟩,Q,⟨hQ,hSQ,hnQ,hqQ,hcQ,hmQ⟩,hu⟩ :=
    pushingUp_cubic_component hw K hn e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
  let C := centralizer ({(x : K)} : Set K)
  let S := solvableResidual (centralizer ({x} : Set R))
  let := hs
  let := hqQ
  let i0 := (R.subtype.elementCentralizerMap x).comp S.subtype
  let i : S →* Q := i0.codRestrict Q (fun s => hSQ
    (mem_map_of_mem (R.subtype.elementCentralizerMap x) s.property))
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg
      (fun y : Q => ((y : C) : K)) hab)))
  let j : Q →* K := C.subtype.comp Q.subtype
  have hj : Function.Injective j := C.subtype_injective.comp Q.subtype_injective
  have hm := cubic_component_twoCore_m22 es i hi j hj e hmQ
  have hcover := m22_seed_covers_twoCore es i hi hm.2.2.some
  have hmap : i.range.map Q.subtype =
      S.map (R.subtype.elementCentralizerMap x) := by
    ext y
    constructor
    · rintro ⟨u,⟨s,rfl⟩,rfl⟩
      exact mem_map_of_mem _ s.property
    · rintro ⟨s,hs,rfl⟩
      exact ⟨i ⟨s,hs⟩,⟨⟨s,hs⟩,rfl⟩,rfl⟩
  have hc := congrArg (map Q.subtype) hcover
  rw [Subgroup.map_sup,hmap,← MonoidHom.range_eq_map,range_subtype] at hc
  refine ⟨x,hx,hqx,hres,hs,⟨es⟩,Q,⟨hQ,hSQ,hnQ,hqQ,hcQ,hm,hc⟩,?_⟩
  intro Q' hQ'
  exact hu Q' ⟨hQ'.1,hQ'.2.1,hQ'.2.2.1,hQ'.2.2.2.1,
    hQ'.2.2.2.2.1,.mathieu hQ'.2.2.2.2.2.1⟩

/-- The original witnesses, with the cubic seed placed in a unique normal
C-component of its full centralizer, the triple M₂₂ quotient, and generation
by the seed together with that component’s two-core. -/
@[expose] def MathieuPushingUpCubicMathieuCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := Janko4.InvolutionCentralizers.First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({x} : Set R)) ∈
            solvableResidual (centralizer ({x} : Set R)) ∧
          IsQuasisimple (solvableResidual (centralizer ({x} : Set R))) ∧
          Nonempty (((solvableResidual (centralizer ({x} : Set R))) ⧸
            center (solvableResidual (centralizer ({x} : Set R)))) ≃* Sporadic.Mathieu.M22) ∧
          ∃! Q : Subgroup (centralizer ({(x : K)} : Set K)),
            Q.IsCComponent ∧
            (solvableResidual (centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ≤ Q ∧ Q.Normal ∧
            IsQuasisimple (Q ⧸ pCore 2 Q) ∧
            (∃ c : center (Q ⧸ pCore 2 Q), orderOf c = 3) ∧
            Chapter1.Section02.LocalModels.IsM22Cover (Q ⧸ pCore 2 Q) ∧
            (solvableResidual (centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ⊔ Q.pCoreIn 2 = Q

/-- Construct the full-centralizer component on the same ordinary component,
retaining its ambient witnesses and relative centralizer factorization. -/
theorem mathieu_pushingUp_cubic_mathieu {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (h : MathieuPushingUpJankoInnerCase L V A) :
    MathieuPushingUpCubicMathieuCase L V A := by
  obtain ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,⟨e⟩,hprod⟩ := h
  exact ⟨J,H,W,hw,hf,K,hK,hn,hout,hF,hW,hprod,e,pushingUp_cubic_component_m22 hw K hn e⟩


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction supplies the cubic residual, its unique
normal containing component in the full cubic centralizer, and the actual
triple M₂₂ model for that component’s two-core quotient. The seed generates
the component together with its two-core. The second branch retains the previous involution,
residual-generation seeds and ambient M₂₂ component, unchanged. Neither
remaining source exclusion is assumed or claimed here. -/
theorem sourceOrbit_mathieu_hall_cubic_mathieu_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpCubicMathieuCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_seed_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp mathieu_pushingUp_cubic_mathieu id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
