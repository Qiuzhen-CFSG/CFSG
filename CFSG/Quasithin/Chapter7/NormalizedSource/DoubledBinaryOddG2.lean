module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddBalanced
public import Theory.SpecificGroups.G2.OddFrattiniEight
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
import all Theory.SpecificGroups.G2.OddFrattiniEight
import all Theory.SpecificGroups.G2.OddFrattiniSixteen

/-!
# The last outer exclusion for the original binary-three residual

In the odd-prime G₂ orthogonal cover, the two rank-one factors have the
same outer involution. Each single-factor extension maps onto PGL₂ with
central scalar kernel in its Sylow Frattini subgroup. In a projective Sylow,
the involutions outside the canonical PSL₂ subgroup are conjugate, since
that subgroup meets the Sylow in a noncyclic subgroup of index two.
Consequently all such exterior elements have the same Frattini image.

The two single-factor projections detect the full Frattini kernel in a
Sylow of the double extension. They descend through its literal diagonal
scalar kernel. In the original G₂ Sylow, all involutions outside the base
therefore have one Frattini image. If the Frattini quotient has order eight,
its involution images number between two and five: at most four in the base
and one outside. This characteristic subset excludes an order-seven
automorphism. Smaller quotients and the Burnside basis kernel also exclude
seven. The odd-index orthogonal embedding handles every odd prime, including
three, and the actual field isomorphism transports the result.

Sylow restriction and descent through the full original component center
now exclude the last possible outer SL₃(2) section in the complete Theorem B
catalogue. The Chapter12 companion applies this to the original H-star
witness, retaining the six placed models and the pushing-up alternative.
The private imports share the existing quaternion coordinates, marked
Sylow construction and invariant-subset count without changing their APIs.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, as used by 7.3.4 and
7.6.1, printed pp.699,702, refs/quasithin.pdf. The coordinate construction
retains the attribution and license in LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddG2
open Atlas.G2 Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open Atlas.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
open Atlas.G2.OddFrattiniSixteen Atlas.G2.OddFrattiniEight
variable {p : ℕ} [Fact p.Prime] (ho : Odd p) (d : ZMod p) (hd : d ≠ 0)
  (hns : ¬ IsSquare (-d))

include ho hns in
private theorem singleProjection_surjective : Function.Surjective (singleProjection d hd) := by
  let f := singleProjection d hd
  have hne : (SemidirectProduct.inl (-1) : Single d hd) ≠ 1 := by
    intro he
    have hh := congrArg (fun x : Single d hd => x.left.val 0 0) he
    change (-1 : ZMod p) = 1 at hh
    have h2 : (2 : ZMod p) = 0 := by linear_combination -hh
    have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h2) |>.resolve_left (Fact.out : p.Prime).ne_one
    subst p
    norm_num at ho
  have hk : Nat.card f.ker = 2 := by
    apply (Nat.card_eq_two_iff' (1 : f.ker)).mpr
    refine ⟨⟨SemidirectProduct.inl (-1),(singleProjection_kernel d hd hns _).mpr (Or.inr rfl)⟩,
      fun h => hne (congrArg Subtype.val h),?_⟩
    intro x hx
    rcases (singleProjection_kernel d hd hns x).mp x.property with hh | hh
    · exact (hx (Subtype.ext hh)).elim
    · exact Subtype.ext hh
  let : Finite PGL(2,ZMod p) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hcount := f.ker.card_mul_index
  rw [index_ker,hk] at hcount
  have hdom : Nat.card (Single d hd) = 2 * (p*(p^2-1)) := by
    rw [SemidirectProduct.card,Atlas.card_sl_two]
    simp [C2,Nat.card_eq_fintype_card,Nat.mul_comm]
  have hr : Nat.card f.range = Nat.card PGL(2,ZMod p) := by
    rw [GorensteinWalter.pgl2_card_formula]
    simp only [Nat.card_eq_fintype_card,ZMod.card] at *
    omega
  exact MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq hr)

include hns in
private theorem projective_mem_inner (x : Single d hd) :
    singleProjection d hd x ∈ (ProjectiveSpecialLinearGroup.toPGL (n:=Fin 2) (R:=ZMod p)).range ↔
      x.right = 1 := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (center SL(2,ZMod p)) y
    have he : singleProjection d hd (SemidirectProduct.inl a) = singleProjection d hd x := by
      simpa [singleProjection,SemidirectProduct.lift_inl,ProjectiveSpecialLinearGroup.toPGL,SpecialLinearGroup.toPGL] using hy
    have hk : singleProjection d hd ((SemidirectProduct.inl a)⁻¹*x)=1 := by simp [he]
    rcases (singleProjection_kernel d hd hns _).mp hk with hh | hh <;>
      simpa using congrArg SemidirectProduct.right hh
  · intro hx
    refine ⟨QuotientGroup.mk' (center SL(2,ZMod p)) x.left,?_⟩
    change SpecialLinearGroup.toPGL x.left = singleProjection d hd x
    simp [singleProjection,SemidirectProduct.lift,hx]

include ho in
private theorem pgl_inner_sylow_noncyclic (P : Sylow 2 PGL(2,ZMod p)) :
    ¬ IsCyclic ((ProjectiveSpecialLinearGroup.toPGL (n:=Fin 2) (R:=ZMod p)).range.subgroupOf
      (P : Subgroup PGL(2,ZMod p))) := by
  let : Finite PGL(2,ZMod p) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hp : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,Fact.out,ho,by decide,by simp⟩
  let J := (ProjectiveSpecialLinearGroup.toPGL (n:=Fin 2) (R:=ZMod p)).range
  let : J.Normal := J.normal_of_index_eq_two (GorensteinWalter.pgl2_psl2Range_index_eq_two _ hp)
  let H := J.subgroupOf (P : Subgroup PGL(2,ZMod p))
  intro hH
  let T := BenderSuzuki.External.hallSylowSubgroupOfNormal P J
  let eHT : H ≃* T := {
    toFun := fun x => ⟨⟨x.val.val,x.property⟩,by
      rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
      exact x.val.property⟩
    invFun := fun y => ⟨⟨y.val.val,by
      let yJ : J := y
      have hy : yJ ∈ (T : Subgroup J) := y.property
      rw [BenderSuzuki.External.hallSylowSubgroupOfNormal_coe] at hy
      exact hy⟩,y.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let : IsCyclic T := eHT.isCyclic.mp hH
  let eJ := (GorensteinWalter.psl2EquivToPGLRange (ZMod p)).symm
  let Q := T.mapSurjective (f:=eJ.toMonoidHom) eJ.surjective
  let eT : T ≃* Q := T.equivMapOfInjective eJ.toMonoidHom eJ.injective
  let : IsCyclic Q := eT.isCyclic.mp inferInstance
  obtain ⟨n,hn,⟨eD⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hp Q
  exact DihedralGroup.not_isCyclic
    (ne_of_gt (Nat.one_lt_pow (by omega : n ≠ 0) (by decide : 1<2)))
    (eD.isCyclic.mp inferInstance)

include ho hns in
private theorem single_outer_frattini (S : Sylow 2 (Single d hd))
    (c : S) (hc : c.val = SemidirectProduct.inr (.ofAdd 1))
    (x : S) (hx : singleProjection d hd x.val ^ 2 = 1) (hr : x.val.right ≠ 1) :
    QuotientGroup.mk' (frattini S) x = QuotientGroup.mk' (frattini S) c := by
  let : Finite PGL(2,ZMod p) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let P := S.mapSurjective (f:=singleProjection d hd) (singleProjection_surjective ho d hd hns)
  let f : S →* P := (singleProjection d hd).subgroupMap (S : Subgroup (Single d hd))
  have hf : Function.Surjective f := (singleProjection d hd).subgroupMap_surjective _
  have hk : f.ker ≤ frattini S := by
    intro y hy
    rcases (singleProjection_kernel d hd hns y.val).mp (congrArg Subtype.val hy) with he | he
    · rw [show y=1 from Subtype.ext he]; exact one_mem _
    · have hz : (SemidirectProduct.inl (-1) : Single d hd)^2=1 := by rw [←map_pow]; simp
      have ha : (SemidirectProduct.inl (quarterTurn p) : Single d hd)^2=
          SemidirectProduct.inl (-1) := by rw [←map_pow,quarterTurn_sq]
      obtain ⟨w,hw⟩ := BinaryFrattiniExtension.central_square_in_sylow S
        (single_scalar_central d hd) ha hz
      let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
      have hh : w^2=y := Subtype.ext (hw.trans he.symm)
      exact hh ▸ pth_power_mem_frattini_of_isPGroup (p:=2) w
  have hp : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,Fact.out,ho,by decide,by simp⟩
  let J := (ProjectiveSpecialLinearGroup.toPGL (n:=Fin 2) (R:=ZMod p)).range
  let H := J.subgroupOf (P : Subgroup PGL(2,ZMod p))
  have hxi : f x ∉ H := fun h => hr ((projective_mem_inner d hd hns x.val).mp h)
  have hci : f c ∉ H := by
    intro h
    have hh := (projective_mem_inner d hd hns c.val).mp h
    rw [hc] at hh
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1) hh
  have hi : H.index=2 := by
    let : J.Normal := J.normal_of_index_eq_two (GorensteinWalter.pgl2_psl2Range_index_eq_two _ hp)
    have hdvd : H.index ∣ 2 := by
      change J.relIndex (P : Subgroup PGL(2,ZMod p)) ∣ 2
      simpa [show J.index=2 from GorensteinWalter.pgl2_psl2Range_index_eq_two _ hp] using
        J.relIndex_dvd_index_of_normal (P : Subgroup PGL(2,ZMod p))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with he | he
    · have ht := index_eq_one.mp he
      exact (hxi (ht ▸ mem_top _)).elim
    · exact he
  obtain ⟨m,_,⟨e⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model _ hp P
  have hm := GorensteinWalter.pgl2_dihedral_sylow_parameter_ge_two _ hp P e
  have hconj := GorensteinWalter.dihedral_involutions_not_mem_noncyclic_index_two_isConj
    hm e H hi (pgl_inner_sylow_noncyclic ho P)
    (show GorensteinWalter.IsInvolution (f x) from ⟨fun hh => hxi (hh ▸ one_mem H),Subtype.ext hx⟩)
    (show GorensteinWalter.IsInvolution (f c) from ⟨fun hh => hci (hh ▸ one_mem H),by
      apply Subtype.ext
      change singleProjection d hd c.val ^ 2=1
      rw [←map_pow,hc,←map_pow]
      simp [show (Multiplicative.ofAdd (1 : ZMod 2))^2=1 by decide]⟩) hxi hci
  obtain ⟨a,ha⟩ := isConj_iff.mp hconj
  obtain ⟨b,rfl⟩ := hf a
  let π := QuotientGroup.mk' (frattini S)
  let q : P →* S ⧸ frattini S := f.liftOfSurjective hf ⟨π,by rw [QuotientGroup.ker_mk']; exact hk⟩
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  let : IsElementaryAbelian 2 (S ⧸ frattini S) := isElementaryAbelian_quotient_frattini
  have hh := congrArg q ha
  simpa [map_mul,map_inv,mul_comm,mul_left_comm,q,π] using hh

private theorem marked_sylow (S : Sylow 2 (Single d hd))
    (hC : (SemidirectProduct.inr : C2 →* Single d hd).range ≤ S) :
    ∃ R : Sylow 2 (Double d hd),
      (S : Subgroup (Single d hd)).map (firstInclusion d hd) ≤ R ∧
      (S : Subgroup (Single d hd)).map (secondInclusion d hd) ≤ R ∧
      (R : Subgroup (Double d hd)).map (firstProjection d hd) = S ∧
      (R : Subgroup (Double d hd)).map (secondProjection d hd) = S := by
  let i := firstInclusion d hd
  let j := secondInclusion d hd
  let r := firstProjection d hd
  let s := secondProjection d hd
  let P := (S : Subgroup (Single d hd)).map i ⊔ (S : Subgroup (Single d hd)).map j
  have hi (x : Single d hd) : r (i x) = x := rfl
  have hj (x : Single d hd) : s (j x) = x := rfl
  have hPr : P ≤ (S : Subgroup (Single d hd)).comap r := by
    apply sup_le
    · rintro _ ⟨x,hx,rfl⟩; exact hx
    · rintro _ ⟨x,hx,rfl⟩; exact hC ⟨x.right,rfl⟩
  have hPs : P ≤ (S : Subgroup (Single d hd)).comap s := by
    apply sup_le
    · rintro _ ⟨x,hx,rfl⟩; exact hC ⟨x.right,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩; exact hx
  let f : P →* S × S :=
    ((r.comp P.subtype).codRestrict _ (fun x => hPr x.property)).prod
      ((s.comp P.subtype).codRestrict _ (fun x => hPs x.property))
  have hf : Function.Injective f := by
    intro x y h
    have h₁ := congrArg (fun z : S × S => (z.1 : Single d hd)) h
    have h₂ := congrArg (fun z : S × S => (z.2 : Single d hd)) h
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact Prod.ext (congrArg SemidirectProduct.left h₁) (congrArg SemidirectProduct.left h₂)
    · exact congrArg (fun z : Single d hd => z.right) h₁
  have hPP : IsPGroup 2 P := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    have hSS : IsPGroup 2 (S × S) := IsPGroup.of_card (n := n+n) (by
      rw [Nat.card_prod,hn,pow_add])
    exact hSS.of_injective f hf
  obtain ⟨R,hPR⟩ := hPP.exists_le_sylow
  have hRr : (R : Subgroup (Double d hd)).map r = S :=
    S.is_maximal' (R.isPGroup'.map r) (by
      intro x hx
      exact ⟨i x,hPR ((show (S : Subgroup _).map i ≤ P from le_sup_left) (mem_map_of_mem i hx)),hi x⟩)
  have hRs : (R : Subgroup (Double d hd)).map s = S :=
    S.is_maximal' (R.isPGroup'.map s) (by
      intro x hx
      exact ⟨j x,hPR ((show (S : Subgroup _).map j ≤ P from le_sup_right) (mem_map_of_mem j hx)),hj x⟩)
  exact ⟨R,le_trans le_sup_left hPR,le_trans le_sup_right hPR,hRr,hRs⟩

include hns in
private theorem projective_squares (x : Double d hd)
    (hx : x^2=1 ∨ x^2=SemidirectProduct.inl (-1,-1)) :
    singleProjection d hd (firstProjection d hd x)^2=1 ∧
      singleProjection d hd (secondProjection d hd x)^2=1 := by
  have h1 : singleProjection d hd (firstProjection d hd x)^2 =
      singleProjection d hd (firstProjection d hd (x^2)) := by rw [map_pow,map_pow]
  have h2 : singleProjection d hd (secondProjection d hd x)^2 =
      singleProjection d hd (secondProjection d hd (x^2)) := by rw [map_pow,map_pow]
  rw [h1,h2]
  rcases hx with hh | hh
  · simp [hh]
  · rw [hh]
    constructor <;> exact (singleProjection_kernel d hd hns _).mpr (Or.inr rfl)

private theorem no_seven_of_outer_involutions {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hbound : Nat.card (P ⧸ frattini P) ≤ 8)
    (tP : P →* C2) (z : P) (hz : tP z=.ofAdd 1) (hzsq : z^2=1)
    (houter : ∀ x : P, x^2=1 → tP x ≠ 1 →
      QuotientGroup.mk' (frattini P) x=QuotientGroup.mk' (frattini P) z) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let t : P ⧸ frattini P →* C2 := QuotientGroup.lift _ tP
    (frattini_le_ker_of_square_image tP (by
      intro x; rw [pow_two]; change (tP x).toAdd+(tP x).toAdd=0
      exact CharTwo.add_self_eq_zero _))
  let π := QuotientGroup.mk' (frattini P)
  have ht (x : P) : t (π x)=tP x := rfl
  by_cases h8 : Nat.card (P ⧸ frattini P)=8
  · apply DoubledBinaryOddSporadic.no_seven_aut hP h8
    · let v : DoubledBinaryOddSporadic.involutionImages (P:=P) := ⟨π z,z,hzsq,rfl⟩
      let w : DoubledBinaryOddSporadic.involutionImages (P:=P) := ⟨π 1,1,one_pow 2,rfl⟩
      have hne : v ≠ w := by
        intro hh
        have hh := congrArg (fun v => t v.val) hh
        change t (π z)=t (π 1) at hh
        rw [ht,hz,show π 1=1 from map_one π,show t 1=1 from map_one t] at hh
        exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1) hh
      let : Nontrivial (DoubledBinaryOddSporadic.involutionImages (P:=P)) := ⟨⟨v,w,hne⟩⟩
      exact Finite.one_lt_card
    · have hsurj : Function.Surjective t := by
        intro x
        rcases (show ∀ c : C2, c=1 ∨ c=.ofAdd 1 from by decide) x with rfl | rfl
        · exact ⟨1,map_one _⟩
        · exact ⟨π z,(ht z).trans hz⟩
      have hcount : Nat.card t.ker=4 := by
        have hh := t.ker.card_mul_index
        rw [index_ker,t.range_eq_top_of_surjective hsurj,card_top,h8] at hh
        have hc2 : Nat.card C2=2 := by simp [C2]
        rw [hc2] at hh
        omega
      have hsubset : DoubledBinaryOddSporadic.involutionImages (P:=P) ⊆
          (t.ker : Set (P ⧸ frattini P)) ∪ {π z} := by
        rintro v ⟨y,hy,rfl⟩
        by_cases hc : tP y=1
        · exact Or.inl (by change t (π y)=1; rw [ht,hc])
        · exact Or.inr (houter y hy hc)
      have hh := (Set.ncard_le_ncard hsubset).trans (Set.ncard_union_le _ _)
      change Nat.card (DoubledBinaryOddSporadic.involutionImages (P:=P)) ≤ _ at hh
      rw [Set.ncard_singleton] at hh
      change _ ≤ Nat.card t.ker+1 at hh
      omega
  · obtain ⟨n,hn⟩ := (hP.to_quotient (frattini P)).exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra! hh
      have hb := Nat.pow_le_pow_right (by decide : 0<2) hh
      omega
    let α := quotientAut (frattini P)
    have hcop : Nat.Coprime 7 (Nat.card α.ker) := by
      obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hP).exists_card_eq
      rw [hk]
      exact (by decide : Nat.Coprime 7 2).pow_right k
    have hcount : Nat.card α.ker*Nat.card α.range=Nat.card (MulAut P) := by
      rw [←index_ker]; exact α.ker.card_mul_index
    intro hdiv
    have hh := (hcop.dvd_of_dvd_mul_left (hcount.symm ▸ hdiv)).trans α.range.card_subgroup_dvd_card
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn] at hh
    interval_cases n <;> norm_num [Fin.prod_univ_succ] at hh


include ho hns in
private theorem double_quotient_no_seven {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 (Single d hd))
    (hC : (SemidirectProduct.inr : C2 →* Single d hd).range ≤ S)
    (R : Sylow 2 (Double d hd))
    (hRa : (S : Subgroup (Single d hd)).map (firstInclusion d hd) ≤ R)
    (hRb : (S : Subgroup (Single d hd)).map (secondInclusion d hd) ≤ R)
    (hRr : (R : Subgroup (Double d hd)).map (firstProjection d hd) = S)
    (hRs : (R : Subgroup (Double d hd)).map (secondProjection d hd) = S)
    (j : R →* P) (hj : Function.Surjective j)
    (hk : ∀ x : R, j x = 1 ↔ x.val=1 ∨ x.val=SemidirectProduct.inl (-1,-1)) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  let hP := R.isPGroup'.of_surjective j hj
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (S ⧸ frattini S) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let r : R →* S := ((firstProjection d hd).comp (R : Subgroup (Double d hd)).subtype).codRestrict S
    (fun x => by
      change firstProjection d hd x.val ∈ (S : Subgroup _)
      rw [←hRr]
      exact mem_map_of_mem _ x.property)
  let s : R →* S := ((secondProjection d hd).comp (R : Subgroup (Double d hd)).subtype).codRestrict S
    (fun x => by
      change secondProjection d hd x.val ∈ (S : Subgroup _)
      rw [←hRs]
      exact mem_map_of_mem _ x.property)
  let a : S →* R := ((firstInclusion d hd).comp (S : Subgroup (Single d hd)).subtype).codRestrict R
    (fun x => hRa (mem_map_of_mem _ x.property))
  let b : S →* R := ((secondInclusion d hd).comp (S : Subgroup (Single d hd)).subtype).codRestrict R
    (fun x => hRb (mem_map_of_mem _ x.property))
  let c : S := ⟨SemidirectProduct.inr (.ofAdd 1),hC ⟨.ofAdd 1,rfl⟩⟩
  let z := a c
  have hz : z.val=SemidirectProduct.inr (.ofAdd 1) := rfl
  let tS : S →* C2 := SemidirectProduct.rightHom.comp (S : Subgroup (Single d hd)).subtype
  have hΦS : frattini S ≤ tS.ker := frattini_le_ker_of_square_image tS (by
    intro x
    rw [pow_two]
    change (tS x).toAdd + (tS x).toAdd=0
    exact CharTwo.add_self_eq_zero _)
  let πS := QuotientGroup.mk' (frattini S)
  let f : R →* (S ⧸ frattini S) × (S ⧸ frattini S) := (πS.comp r).prod (πS.comp s)
  have hker : f.ker=frattini R := by
    apply le_antisymm
    · intro x hx
      have hr : πS (r x)=1 := congrArg Prod.fst hx
      have hs : πS (s x)=1 := congrArg Prod.snd hx
      have hrΦ : r x ∈ frattini S := (QuotientGroup.eq_one_iff _).mp hr
      have hsΦ : s x ∈ frattini S := (QuotientGroup.eq_one_iff _).mp hs
      have hc : x.val.right=1 := hΦS hrΦ
      have he : x=a (r x)*b (s x) := by
        apply Subtype.ext
        apply SemidirectProduct.ext
        · change x.val.left=(x.val.left.1,1)*action d hd x.val.right (1,x.val.left.2)
          rw [hc,map_one]
          simp
        · change x.val.right=x.val.right*x.val.right
          simp [hc]
      rw [he]
      exact (frattini R).mul_mem
        (frattini_map_le_of_isPGroup (p:=2) a (mem_map_of_mem _ hrΦ))
        (frattini_map_le_of_isPGroup (p:=2) b (mem_map_of_mem _ hsΦ))
    · apply frattini_le_ker_of_square_image
      intro x
      apply Prod.ext <;> exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (S ⧸ frattini S)) _
  have hscalar (y : S) (hy : y.val=SemidirectProduct.inl (-1)) : πS y=1 := by
    have ha : (SemidirectProduct.inl (quarterTurn p) : Single d hd)^2=
        SemidirectProduct.inl (-1) := by rw [←map_pow,quarterTurn_sq]
    have hz2 : (SemidirectProduct.inl (-1) : Single d hd)^2=1 := by rw [←map_pow]; simp
    obtain ⟨w,hw⟩ := BinaryFrattiniExtension.central_square_in_sylow S
      (single_scalar_central d hd) ha hz2
    apply (QuotientGroup.eq_one_iff _).mpr
    have hh : w^2=y := Subtype.ext (hw.trans hy.symm)
    exact hh ▸ pth_power_mem_frattini_of_isPGroup (p:=2) w
  have hjf : j.ker ≤ f.ker := by
    intro x hx
    rcases (hk x).mp hx with he | he
    · rw [show x=1 from Subtype.ext he]; exact one_mem _
    · apply Prod.ext
      · exact hscalar (r x) (by change firstProjection d hd x.val=_; rw [he]; rfl)
      · exact hscalar (s x) (by change secondProjection d hd x.val=_; rw [he]; rfl)
  let fP : P →* (S ⧸ frattini S) × (S ⧸ frattini S) := j.liftOfSurjective hj ⟨f,hjf⟩
  have hfac (x : R) : fP (j x)=f x := by simp [fP]
  have hkerP : fP.ker=frattini P := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x,rfl⟩ := hj y
      have hx : x ∈ f.ker := by change f x=1; rw [←hfac]; exact hy
      rw [hker] at hx
      exact frattini_map_le_of_isPGroup (p:=2) j (mem_map_of_mem _ hx)
    · apply frattini_le_ker_of_square_image
      intro x
      apply Prod.ext <;> exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (S ⧸ frattini S)) _
  let e : P ⧸ frattini P →* (S ⧸ frattini S) × (S ⧸ frattini S) :=
    QuotientGroup.lift _ fP (le_of_eq hkerP.symm)
  have he : Function.Injective e := QuotientGroup.injective_lift_iff _ _ _ |>.mpr hkerP.symm
  let tR : R →* C2 := SemidirectProduct.rightHom.comp (R : Subgroup (Double d hd)).subtype
  have hkt : j.ker ≤ tR.ker := by
    intro x hx
    rcases (hk x).mp hx with hh | hh <;> change x.val.right=1 <;> rw [hh] <;> rfl
  let tP : P →* C2 := j.liftOfSurjective hj ⟨tR,hkt⟩
  have htfac (x : R) : tP (j x)=x.val.right := by simp [tP,tR]
  let π := QuotientGroup.mk' (frattini P)
  have hsq (x : R) (hx : (j x)^2=1) :
      singleProjection d hd (r x).val ^ 2=1 ∧ singleProjection d hd (s x).val ^ 2=1 := by
    have hxk : j (x^2)=1 := by rwa [map_pow]
    exact projective_squares d hd hns x.val ((hk (x^2)).mp hxk)
  have houter (x : R) (hx : (j x)^2=1) (hc : x.val.right ≠ 1) : π (j x)=π (j z) := by
    apply he
    change fP (j x)=fP (j z)
    rw [hfac,hfac]
    apply Prod.ext
    · exact single_outer_frattini ho d hd hns S c rfl (r x) (hsq x hx).1 hc
    · exact single_outer_frattini ho d hd hns S c rfl (s x) (hsq x hx).2 hc
  have hbound : Nat.card (P ⧸ frattini P) ≤ 8 :=
    (BinaryFrattiniExtension.elementary_card_le (π.comp j)
      ((QuotientGroup.mk'_surjective _).comp hj)).trans
      (double_sylow_frattini_le_eight d hd ho hns R)
  have hzsq : (j z)^2=1 := by
    rw [←map_pow]
    have hz2 : z^2=1 := by
      apply Subtype.ext
      change z.val^2=1
      rw [hz,←map_pow]
      simp [show (Multiplicative.ofAdd (1 : ZMod 2))^2=1 by decide]
    rw [hz2,map_one]
  apply no_seven_of_outer_involutions hP hbound tP (j z) (htfac z) hzsq
  intro y hy hc
  obtain ⟨x,rfl⟩ := hj y
  exact houter x hy (by rwa [htfac] at hc)


/-- Every Sylow two-subgroup of the actual odd-prime octonion model has no
order-seven automorphism. The characteristic involution images refine the
three-generator bound. -/
public theorem prime_sylow_no_seven (hp : 2 < p)
    (P : Sylow 2 (Model (ZMod p))) : ¬ 7 ∣ Nat.card (MulAut P) := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  let d := -a
  have hd : d ≠ 0 := neg_ne_zero.mpr ha0
  let H := (OrthogonalMap.inclusion d hd).range
  have hindex : ¬ 2 ∣ H.index := by
    rw [← even_iff_two_dvd]
    apply Nat.not_even_iff_odd.mpr
    by_cases hp3 : 3 < p
    · exact odd_index_of_diagonal_kernel
        (F := ZMod p) (by simp [Nat.card_eq_fintype_card]) hp3
        (action d hd) (OrthogonalMap.inclusion d hd)
        (inclusion_kernel d hd (by simpa [d] using ha))
    · have he : p = 3 := by omega
      subst p
      let j := OrthogonalMap.inclusion d hd
      let z : (RankOne 3 × RankOne 3) ⋊[action d hd] C2 := SemidirectProduct.inl (-1,-1)
      have hz : z ≠ 1 := by
        intro h
        have h' := congrArg (fun x : (RankOne 3 × RankOne 3) ⋊[action d hd] C2 => x.left.1.val 0 0) h
        change (-1 : ZMod 3) = 1 at h'
        have hz : (2 : ZMod 3) = 0 := by linear_combination -h'
        have hh := (ZMod.natCast_eq_zero_iff 2 3).mp hz
        norm_num at hh
      have hk : Nat.card j.ker = 2 := by
        apply (Nat.card_eq_two_iff' (1 : j.ker)).mpr
        have hj := inclusion_kernel d hd (by simpa [d] using ha)
        refine ⟨⟨z,(hj z).mpr (Or.inr rfl)⟩,fun h => hz (congrArg Subtype.val h),?_⟩
        intro x hx
        rcases (hj x).mp x.property with h | h
        · exact (hx (Subtype.ext h)).elim
        · exact Subtype.ext h
      have hdom : Nat.card ((RankOne 3 × RankOne 3) ⋊[action d hd] C2) = 1152 := by
        rw [SemidirectProduct.card,Nat.card_prod,Atlas.card_sl_two]
        norm_num [C2,Nat.card_eq_fintype_card]
      have hr : Nat.card H = 576 := by
        have h := j.ker.card_mul_index
        rw [index_ker,hk,hdom] at h
        change 2 * Nat.card H = 1152 at h
        omega
      have hidx := H.card_mul_index
      rw [hr,Atlas.G2.card_Model] at hidx
      norm_num [Nat.card_eq_fintype_card] at hidx
      have hh : H.index = 7371 := by omega
      rw [hh]
      decide
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hC : IsPGroup 2 C2 := IsPGroup.of_card (n:=1) (by simp [C2])
  obtain ⟨S,hS⟩ := (hC.of_surjective
    (SemidirectProduct.inr : C2 →* Single d hd).rangeRestrict
    (SemidirectProduct.inr : C2 →* Single d hd).rangeRestrict_surjective).exists_le_sylow
  obtain ⟨R,hRa,hRb,hRr,hRs⟩ := marked_sylow d hd S hS
  let f := (OrthogonalMap.inclusion d hd).rangeRestrict
  let Q := R.mapSurjective (f:=f) (OrthogonalMap.inclusion d hd).rangeRestrict_surjective
  let j : R →* Q := f.subgroupMap (R : Subgroup (Double d hd))
  have hj : Function.Surjective j := f.subgroupMap_surjective _
  have hk (x : R) : j x=1 ↔ x.val=1 ∨ x.val=SemidirectProduct.inl (-1,-1) := by
    rw [←inclusion_kernel d hd (by simpa [d] using ha)]
    constructor
    · intro hh
      exact congrArg (fun y : Q => y.val.val) hh
    · intro hh
      exact Subtype.ext (Subtype.ext hh)
  have hQ := double_quotient_no_seven ho d hd (by simpa [d] using ha) S hS R
    hRa hRb hRr hRs j hj hk
  have hm : ¬ 2 ∣ ((Q : Subgroup H).map H.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two Q.not_dvd_index hindex
  let U : Sylow 2 (Model (ZMod p)) := (Q.isPGroup'.map H.subtype).toSylow hm
  let e : Q ≃* U := Q.equivMapOfInjective H.subtype H.subtype_injective
  rw [Nat.card_congr (MulAut.congr ((P.equiv U).trans e.symm)).toEquiv]
  exact hQ

/-- The stored field and actual G₂ isomorphism transport the Sylow obstruction. -/
public theorem sylow_no_seven_of_model {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassificationModels.IsG2At Q p)
    (P : Sylow 2 Q) : ¬ 7 ∣ Nat.card (MulAut P) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let f := e.trans (fieldEquiv a)
  let R := P.mapSurjective (f:=f.toMonoidHom) f.surjective
  let c : P ≃* R := P.equivMapOfInjective f.toMonoidHom f.injective
  rw [Nat.card_congr (MulAut.congr c).toEquiv]
  apply prime_sylow_no_seven _ R
  have hne : p ≠ 2 := by rintro rfl; norm_num at ho
  have := hp.two_le
  omega

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- Sylow restriction excludes the original binary-three outer section. -/
public theorem no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassificationModels.IsG2At Q p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hf
  apply sylow_no_seven_of_model hp ho hm P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- Descent retains the entire center of the original perfect component. -/
public theorem cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    ∀ p : ℕ, p.Prime → Odd p → ¬ ClassificationModels.IsG2At (K ⧸ center K) p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hpo hm
  exact no_outer_section hp hpo hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

/-- The complete original Theorem B catalogue has no outer SL₃(2) section.
The placed-component alternative is separate and is retained by the consumer. -/
public theorem no_theoremB_outer_section {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    ¬ ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f := by
  intro ho
  cases DoubledBinaryOddBalanced.remaining_outer_models hm ho with
  | g2_odd p hp hpo e => exact cover_exclusion ho p hp hpo e

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddG2
