module
public import Theory.SpecificGroups.PSL2.PrimeSylowComponents
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Theory.GroupTheory.PPerfectHom

/-!
# Three-free two-perfect subgroups of odd-prime PSL₂

Dickson's classification makes these subgroups odd: the exceptional rows
have a cubic divisor, dihedral groups have a nontrivial two-quotient, and
two-perfection makes the cyclic quotient in the affine row odd. Projection
to each factor gives the same conclusion in the actual marked square.

Source: Aschbacher--Smith 8.3.8, printed p.725, using Huppert II.8.27.
The point-centralizer application retains the original quotient action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace Theory.PSL2.PrimeThreeFreeResidual

private theorem odd_of_commutative {A : Type*} [_root_.Group A] [Finite A]
    [IsMulCommutative A] (hp : IsPPerfect 2 A) : Odd (Nat.card A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact Nat.coprime_two_left.mp (coprime_card_of_isPPerfect_commGroup hp)

private theorem not_twoPerfect_dihedral {n : ℕ} (hp : IsPPerfect 2 (DihedralGroup n)) : False := by
  let parity : DihedralGroup n →* Multiplicative (ZMod 2) := {
    toFun
      | DihedralGroup.r _ => 1
      | DihedralGroup.sr _ => Multiplicative.ofAdd 1
    map_one' := rfl
    map_mul' a b := by
      cases a <;> cases b <;> simp
      change (0 : ZMod 2) = 1 + 1
      exact (ZMod.natCast_self 2).symm }
  have hz := hp.hom_eq_one_of_isPGroup
    (IsPGroup.of_card (p := 2) (n := 1) (by simp)) parity
  have h := DFunLike.congr_fun hz (DihedralGroup.sr 0)
  change Multiplicative.ofAdd (1 : ZMod 2) = 1 at h
  have hh := congrArg Multiplicative.toAdd h
  norm_num at hh

/-- A three-free two-perfect subgroup of odd-prime PSL₂ has odd order. -/
theorem odd_card {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (H : Subgroup (PSL2MatrixGroup F))
    (hp : IsPPerfect 2 H) (hthree : ¬ 3 ∣ Nat.card H) : Odd (Nat.card H) := by
  have hcardF : Nat.card F = p ^ 1 := by simpa using hF
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcardF H with hEl | hCy | hDi | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · let := hEl
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [ha]
    exact ho.pow
  · let : IsCyclic H := hCy.choose_spec.2.2
    exact odd_of_commutative hp
  · obtain ⟨_,_,_,⟨e⟩⟩ := hDi
    exact (not_twoPerfect_dihedral (hp.of_surjective e.toMonoidHom e.surjective)).elim
  · obtain ⟨_,⟨e⟩⟩ := hA4
    apply (hthree _).elim
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · obtain ⟨_,⟨e⟩⟩ := hS4
    apply (hthree _).elim
    rw [Nat.card_congr e.toEquiv,Nat.card_perm]
    norm_num [Nat.factorial]
  · obtain ⟨_,⟨e⟩⟩ := hA5
    apply (hthree _).elim
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · obtain ⟨a,t,_,_,N,C,hN,_,hcN,hC,_,hd,hs⟩ := hAff
    let := hN
    let := hC
    have hcomp : N.IsComplement' C := by
      refine ⟨mul_injective_of_disjoint hd,?_⟩
      intro g
      have hg : g ∈ (N : Set H) * (C : Set H) := by
        rw [←normal_mul N C,hs]; trivial
      obtain ⟨n,hn,c,hc,he⟩ := hg
      exact ⟨⟨⟨n,hn⟩,⟨c,hc⟩⟩,he⟩
    let : IsCyclic (H ⧸ N) := hcomp.symm.QuotientMulEquiv.isCyclic.mpr inferInstance
    have hq := odd_of_commutative
      (hp.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N))
    rw [card_eq_card_quotient_mul_card_subgroup N,hcN]
    exact hq.mul ho.pow
  · obtain ⟨a,_,had,⟨e⟩⟩ := hPSL
    have he : a = 1 := Nat.eq_one_of_dvd_one had
    subst a
    exact (hthree (prime_model_three_dvd_card (Fact.out : p.Prime) ho
      (by simpa using GaloisField.card p 1 (by decide)) e)).elim
  · obtain ⟨a,_,had,_⟩ := hPGL
    have := Nat.le_of_dvd (by decide : 0 < 1) had
    omega

/-- The oddness conclusion survives actual markings and homomorphic images. -/
theorem odd_card_image {A Q : Type*} [_root_.Group A] [Finite A] [_root_.Group Q]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (e : Q ≃* PSL2MatrixGroup F)
    (hp : IsPPerfect 2 A) (hthree : ¬ 3 ∣ Nat.card A) (f : A →* Q) :
    Odd (Nat.card f.range) := by
  let g := e.toMonoidHom.comp f
  have h3 : ¬ 3 ∣ Nat.card g.range := fun hd =>
    hthree (hd.trans (card_dvd_of_surjective g.rangeRestrict g.rangeRestrict_surjective))
  have h := odd_card ho hF g.range
    (hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective) h3
  have he : g.range = f.range.map e.toMonoidHom := MonoidHom.range_comp _ _
  rwa [he,card_map_of_injective e.injective] at h

/-- A two-perfect three-free subgroup of a marked PSL₂ square has odd order. -/
theorem odd_card_square {Q : Type*} [_root_.Group Q]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (e : Q ≃* PSL2MatrixGroup F)
    (U : Subgroup (Q × Q)) [Finite U]
    (hp : IsPPerfect 2 U) (hthree : ¬ 3 ∣ Nat.card U) : Odd (Nat.card U) := by
  let f : U →* Q := (MonoidHom.fst Q Q).comp U.subtype
  let g : U →* Q := (MonoidHom.snd Q Q).comp U.subtype
  have hf := odd_card_image ho hF e hp hthree f
  have hg := odd_card_image ho hF e hp hthree g
  let a : U →* f.range × g.range := f.rangeRestrict.prod g.rangeRestrict
  have ha : Function.Injective a := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)
  apply (hf.mul hg).of_dvd_nat
  simpa only [Nat.card_prod] using card_dvd_of_injective a ha

end Theory.PSL2.PrimeThreeFreeResidual
