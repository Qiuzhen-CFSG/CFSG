module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddWreath
public import Theory.SpecificGroups.PSL4.FermatFrattini
public import Theory.SpecificGroups.ClassicalUnitary.MersenneFrattini
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddSporadic
import all Theory.SpecificGroups.PSL4.OddFrattiniSixteen
import all Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen

/-!
# Degree-four outer exclusions for the original binary-three residual

The actual odd-index two-block subgroups in SL₄ and SU₄ are determinant-one
wreath products. For their Sylow two-subgroups, the cyclic determinant
splits and the two-dimensional base has at most two Frattini generators.
A literal quotient map identifies the doubled Frattini quotient with the
base Frattini quotient times C₂. The whole projective scalar kernel lies
in its kernel, including scalars of order four.

For an involution outside the block-diagonal base, the product of its two
coordinates is scalar. That scalar has a square root in every base Sylow,
so its Frattini image is trivial. The involutory cosets therefore lie in
at most six of the eight Frattini cosets: the four base cosets and at most
two on the swap side. Identity and swap give distinct involutory cosets.
This characteristic subset excludes an order-seven automorphism. Smaller
Frattini quotients and the Burnside basis kernel also have no seven-part.

Sylow restriction and descent through the full original component center
exclude both Fermat PSL₄ and Mersenne PSU₄ outer SL₃(2) sections. The
Chapter12 companion applies this to the same H-star witness. Odd G₂ is
the remaining outer family; placed components and pushing-up remain open.
The private imports share existing matrix coordinates and the involution
orbit-counting argument without changing their public boundaries.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, as used by
7.3.4 and 7.6.1, pp.699,702, refs/quasithin.pdf. Matrix constructions retain
the attribution and license in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddBalanced
open BalancedWreath
private abbrev C2 := Multiplicative (ZMod 2)
variable {R C : Type*} [Group R] [Finite R] [CommGroup C]

private def quotientMap (d : R →* C) (s : C →* R) (hR : IsPGroup 2 R) :
    W d →* (R ⧸ frattini R) × C2 := by
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini R)
  have hinv (x : R ⧸ frattini R) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) x
  exact {
    toFun := fun x => (q (x.left.val.1 * s (d x.left.val.1) * x.left.val.2),x.right)
    map_one' := by simp
    map_mul' := by
      intro x y
      apply Prod.ext
      · have hc : x.right = 1 ∨ x.right = Multiplicative.ofAdd 1 := by
          exact (show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right
        have hy : d y.left.val.2 = (d y.left.val.1)⁻¹ :=
          eq_inv_of_mul_eq_one_right y.left.property
        rcases hc with hc | hc <;>
          simp [SemidirectProduct.mul_left,action,swap,hc,map_mul,hy,map_inv,hinv,
            mul_comm,mul_left_comm,mul_assoc]
      · rfl }

private theorem quotientMap_apply (d : R →* C) (s : C →* R) (hR : IsPGroup 2 R)
    (x : W d) : quotientMap d s hR x =
      (QuotientGroup.mk' (frattini R) (x.left.val.1*s (d x.left.val.1)*x.left.val.2),x.right) := rfl

private theorem quotientMap_surjective (d : R →* C) (s : C →* R)
    (hs : d.comp s = MonoidHom.id C) (hR : IsPGroup 2 R) :
    Function.Surjective (quotientMap d s hR) := by
  rintro ⟨v,c⟩
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
  exact ⟨⟨sectionBase d s hs x,c⟩,by simp [quotientMap_apply,sectionBase]⟩

private theorem quotient_no_seven {P : Type*} [Group P] [Finite P]
    [IsCyclic C] (d : R →* C) (s : C →* R)
    (hs : d.comp s = MonoidHom.id C) (hR : IsPGroup 2 R) (hsmall : Nat.card (R ⧸ frattini R) ≤ 4)
    (j : W d →* P) (hj : Function.Surjective j)
    (hk : j.ker ≤ (quotientMap d s hR).ker)
    (hsq : ∀ x : W d, j x ^ 2 = 1 → x.right ≠ 1 →
      QuotientGroup.mk' (frattini R) (x.left.val.1*x.left.val.2)=1) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let hP := (BalancedWreath.isPGroup d hR).of_surjective j hj
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  let E := (R ⧸ frattini R) × C2
  let : IsElementaryAbelian 2 C2 := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      decide +kernel }
  let : IsElementaryAbelian 2 E := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 C2) x.2 }
  let f : P →* E := j.liftOfSurjective hj ⟨quotientMap d s hR,hk⟩
  have hfac (x : W d) : f (j x) = quotientMap d s hR x := by simp [f]
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x,rfl⟩ := quotientMap_surjective d s hs hR v
    exact ⟨j x,hfac x⟩
  have hphi := Theory.GroupTheory.frattini_le_ker_of_square_image f (fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) _)
  have hb : Nat.card (P ⧸ frattini P) ≤ Nat.card E := by
    let : Fact (IsPGroup 2 P) := ⟨hP⟩
    let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
    exact (BinaryFrattiniExtension.elementary_card_le
      ((QuotientGroup.mk' (frattini P)).comp j)
      ((QuotientGroup.mk'_surjective _).comp hj)).trans
      (by simpa [E,Nat.card_prod,Nat.mul_comm,C2] using BalancedWreath.card_frattini_le d s hs hR)
  have hphi_eq : frattini P = f.ker := by
    apply eq_of_le_of_card_ge hphi
    have h1 := card_eq_card_quotient_mul_card_subgroup (frattini P)
    have h2 := card_eq_card_quotient_mul_card_subgroup f.ker
    have hq := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    rw [hq] at h2
    have hpos := Nat.card_pos (α:=P ⧸ frattini P)
    nlinarith
  let e : P ⧸ frattini P ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hphi_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x : P) : e (QuotientGroup.mk' (frattini P) x) = f x := rfl
  have hbound : Nat.card (P ⧸ frattini P) ≤ 8 := by
    apply hb.trans
    simpa [E,Nat.card_prod,C2] using Nat.mul_le_mul_right 2 hsmall
  by_cases h8 : Nat.card (P ⧸ frattini P)=8
  · apply DoubledBinaryOddSporadic.no_seven_aut hP h8
    · apply Nat.add_one_le_iff.mpr
      let x : P := j (SemidirectProduct.inr (Multiplicative.ofAdd 1))
      have hx : x^2=1 := by
        dsimp [x]
        rw [←map_pow,←map_pow,show (Multiplicative.ofAdd (1 : ZMod 2))^2=1 by decide,
          map_one,map_one]
      let a : DoubledBinaryOddSporadic.involutionImages (P:=P) :=
        ⟨QuotientGroup.mk' (frattini P) 1,1,one_pow 2,rfl⟩
      let b : DoubledBinaryOddSporadic.involutionImages (P:=P) :=
        ⟨QuotientGroup.mk' (frattini P) x,x,hx,rfl⟩
      have hne : a ≠ b := by
        intro hab
        have hh := congrArg (fun z => (e z.val).2) hab
        change (f 1).2 = (f x).2 at hh
        rw [map_one] at hh
        change (1 : C2) = (f (j _)).2 at hh
        rw [hfac] at hh
        exact (by decide : (1:C2) ≠ Multiplicative.ofAdd 1) hh
      let : Nontrivial (DoubledBinaryOddSporadic.involutionImages (P:=P)) := ⟨⟨a,b,hne⟩⟩
      exact Finite.one_lt_card
    · let A := ((QuotientGroup.mk' (frattini R)).comp s).range
      have hAc : Nat.card A ≤ 2 := by
        let : IsCyclic A := isCyclic_of_surjective
          ((QuotientGroup.mk' (frattini R)).comp s).rangeRestrict
          ((QuotientGroup.mk' (frattini R)).comp s).rangeRestrict_surjective
        have hd := (Monoid.exponent_dvd_of_monoidHom A.subtype A.subtype_injective).trans
          (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R))
        rw [IsCyclic.exponent_eq_card] at hd
        exact Nat.le_of_dvd (by decide) hd
      let I : Set E := {v | v.2=1 ∨ v.1 ∈ A ∧ v.2=Multiplicative.ofAdd 1}
      let a : DoubledBinaryOddSporadic.involutionImages (P:=P) → I := fun v =>
        ⟨e v,by
          obtain ⟨y,hy,hv⟩ := v.property
          rw [←hv]
          obtain ⟨x,rfl⟩ := hj y
          rw [he,hfac,quotientMap_apply]
          by_cases hc : x.right=1
          · exact Or.inl hc
          · have hc' : x.right = Multiplicative.ofAdd 1 := by
              have hh := (show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right
              exact hh.resolve_left hc
            refine Or.inr ⟨?_,hc'⟩
            have hh := hsq x hy hc
            rw [map_mul] at hh
            have heq : QuotientGroup.mk' (frattini R)
                (x.left.val.1*s (d x.left.val.1)*x.left.val.2) =
                QuotientGroup.mk' (frattini R) (s (d x.left.val.1)) := by
              rw [map_mul,map_mul,mul_right_comm,hh,one_mul]
            rw [heq]
            exact ⟨d x.left.val.1,rfl⟩⟩
      have ha : Function.Injective a := fun x y h =>
        Subtype.ext (e.injective (congrArg Subtype.val h))
      apply (Nat.card_le_card_of_injective a ha).trans
      have hu : I = {v : E | v.2=1} ∪ {v : E | v.1 ∈ A ∧ v.2=Multiplicative.ofAdd 1} := rfl
      let a₁ : {v : E // v.2=1} ≃ (R ⧸ frattini R) := {
        toFun := fun v => v.val.1
        invFun := fun v => ⟨(v,1),rfl⟩
        left_inv := fun v => Subtype.ext (Prod.ext rfl v.property.symm)
        right_inv := fun _ => rfl }
      let a₂ : {v : E // v.1 ∈ A ∧ v.2=Multiplicative.ofAdd 1} ≃ A := {
        toFun := fun v => ⟨v.val.1,v.property.1⟩
        invFun := fun v => ⟨(v,Multiplicative.ofAdd 1),v.property,rfl⟩
        left_inv := fun v => Subtype.ext (Prod.ext rfl v.property.2.symm)
        right_inv := fun _ => rfl }
      have hc₁ := Nat.card_congr a₁
      have hc₂ := Nat.card_congr a₂
      change I.ncard ≤ 6
      rw [hu]
      apply (Set.ncard_union_le _ _).trans
      change Nat.card {v : E // v.2=1} +
        Nat.card {v : E // v.1 ∈ A ∧ v.2=Multiplicative.ofAdd 1} ≤ 6
      rw [hc₁,hc₂]
      omega
  · let : Fact (IsPGroup 2 P) := ⟨hP⟩
    let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
    obtain ⟨n,hn⟩ := (hP.to_quotient (frattini P)).exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra! h
      have hh := Nat.pow_le_pow_right (by decide : 0<2) h
      omega
    have hsmall' : Nat.card (P ⧸ frattini P) ≤ 4 := by
      rw [hn]
      exact Nat.pow_le_pow_right (by decide) hn2
    let α := quotientAut (frattini P)
    have hcop : Nat.Coprime 7 (Nat.card α.ker) := by
      obtain ⟨k,hk⟩ := (isPGroup_quotientAut_frattini_kernel hP).exists_card_eq
      rw [hk]
      exact (by decide : Nat.Coprime 7 2).pow_right k
    have hcount : Nat.card α.ker * Nat.card α.range = Nat.card (MulAut P) := by
      rw [←index_ker]; exact α.ker.card_mul_index
    intro hd
    have hh := (hcop.dvd_of_dvd_mul_left (hcount.symm ▸ hd)).trans α.range.card_subgroup_dvd_card
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ n hn] at hh
    interval_cases n <;> norm_num [Fin.prod_univ_succ] at hh

private theorem exists_sylow_wreath [Finite C]
    (d : R →* C) (s : C →* R) (hs : d.comp s = MonoidHom.id C) (hC : IsPGroup 2 C) :
    ∃ (P : Sylow 2 R) (hP : ∀ c, s c ∈ P),
      let dP := d.comp (P : Subgroup R).subtype
      let sP := s.codRestrict P hP
      dP.comp sP = MonoidHom.id C ∧
      Odd (BalancedWreath.map dP d (P : Subgroup R).subtype (MonoidHom.id C) rfl).range.index := by
  obtain ⟨P,hP⟩ := (hC.of_surjective s.rangeRestrict s.rangeRestrict_surjective).exists_le_sylow
  have hPs : ∀ c, s c ∈ P := fun c => hP ⟨c,rfl⟩
  refine ⟨P,hPs,?_,?_⟩
  · ext c
    exact DFunLike.congr_fun hs c
  · let dP := d.comp (P : Subgroup R).subtype
    let f := BalancedWreath.map dP d (P : Subgroup R).subtype (MonoidHom.id C) rfl
    have hf : Function.Injective f := BalancedWreath.map_injective _ _ _ _ _ Subtype.val_injective
    have hd : Function.Surjective d := fun c => ⟨s c,DFunLike.congr_fun hs c⟩
    have hdP : Function.Surjective dP := fun c => ⟨⟨s c,hPs c⟩,DFunLike.congr_fun hs c⟩
    have hb := BalancedWreath.card_mul d hd
    have hsmall := BalancedWreath.card_mul dP hdP
    have he := f.range.card_mul_index
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at he
    have hidx : f.range.index = (P : Subgroup R).index^2 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.card_pos (α:=W dP)) (Nat.card_pos (α:=C)))
      calc
        Nat.card (W dP)*Nat.card C*f.range.index = Nat.card (W d)*Nat.card C := by rw [mul_right_comm,he]
        _ = 2*Nat.card R^2 := hb
        _ = (2*Nat.card P^2)*(P : Subgroup R).index^2 := by rw [←(P : Subgroup R).card_mul_index]; ring
        _ = _ := by rw [←hsmall]
    change Odd f.range.index
    rw [hidx]
    exact (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using P.not_dvd_index)).pow

private theorem central_fourth_square_in_sylow {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) {z x : G} (hz : z ∈ center G) (hx : x^2=z) (hz4 : z^4=1) :
    ∃ y : P, (y : G)^2=z := by
  have hx8 : x^(2^3)=1 := by rw [show 2^3=2*4 by decide,pow_mul,hx,hz4]
  have hd : Nat.card (zpowers x) ∣ 2^3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx8
  obtain ⟨n,_,hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hC : IsPGroup 2 (zpowers x) := IsPGroup.of_card hn
  obtain ⟨S,hS⟩ := hC.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S P
  let e : S ≃* P := (S.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))
  refine ⟨e ⟨x,hS (mem_zpowers x)⟩,?_⟩
  change (g*x*g⁻¹)^2=z
  rw [←MulAut.conj_apply,←map_pow,hx]
  change g*z*g⁻¹=z
  rw [(mem_center_iff.mp hz g),mul_inv_cancel_right]

open Matrix Theory.SpecificGroups.PSL4.OddFrattiniSixteen
variable {F : Type*} [Field F] [Finite F]
local notation "GL₂" => GL (Fin 2) F
local notation "d" => (GeneralLinearGroup.det : GL₂ →* Fˣ)

private def scalarRoot (u : Fˣ) : GL₂ :=
  GeneralLinearGroup.diagonalPair F (u,1) * GeneralLinearGroup.coordinateSwap F

omit [Finite F] in
private theorem scalarRoot_sq (u : Fˣ) : scalarRoot u ^ 2 = GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarRoot,GeneralLinearGroup.diagonalPair,GeneralLinearGroup.coordinateSwap,
      pow_two,Matrix.mul_apply,Fin.sum_univ_two]

private theorem scalar_in_frattini (P : Sylow 2 GL₂) (x : P) (u : Fˣ)
    (hu : u^4=1) (he : (x : GL₂)=GeneralLinearGroup.scalar (Fin 2) u) :
    QuotientGroup.mk' (frattini P) x = 1 := by
  have hz : GeneralLinearGroup.scalar (Fin 2) u ∈ center GL₂ := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u,rfl⟩
  obtain ⟨y,hy⟩ := central_fourth_square_in_sylow P hz (scalarRoot_sq u)
    (by rw [←map_pow,hu,map_one])
  have hxy : y^2=x := Subtype.ext (hy.trans he.symm)
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  exact (QuotientGroup.eq_one_iff _).mpr
    (hxy ▸ pth_power_mem_frattini_of_isPGroup (p:=2) y)

omit [Finite F] in
private theorem inclusion_scalar (x : W d)
    (hx : inclusion x ∈ center SL(4,F)) :
    ∃ u : Fˣ, u^4=1 ∧ x.right=1 ∧
      x.left.val.1=GeneralLinearGroup.scalar (Fin 2) u ∧
      x.left.val.2=GeneralLinearGroup.scalar (Fin 2) u := by
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hr0 : r ≠ 0 := by intro hz; simp [hz] at hr
  let u : Fˣ := Units.mk0 r hr0
  have hc : x.right=1 := by
    have hcases := (show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right
    rcases hcases with hc | hc
    · exact hc
    · exfalso
      have hblock : block x.left.val.1.val x.left.val.2.val * swapMatrix = Matrix.scalar (Fin 4) r := by
        have hh := he.symm
        change (pairHom x.left * swapHom x.right).val = _ at hh
        rw [hc] at hh
        exact hh
      have hh := congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 0 0) hblock
      have hz : (0 : F)=r := by
        simpa [block,swapMatrix,Matrix.mul_apply,Fin.sum_univ_succ] using hh
      exact hr0 hz.symm
  have hblock : block x.left.val.1.val x.left.val.2.val = Matrix.scalar (Fin 4) r := by
    have hh := he.symm
    change (pairHom x.left * swapHom x.right).val = _ at hh
    rw [hc,map_one,mul_one] at hh
    exact hh
  refine ⟨u,Units.ext hr,hc,?_,?_⟩
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 0 0) hblock
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 0 1) hblock
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 1 0) hblock
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 1 1) hblock
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 2 2) hblock
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 2 3) hblock
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 3 2) hblock
    · exact congrArg (fun a : Matrix (Fin 4) (Fin 4) F => a 3 3) hblock

private abbrev detP (P : Sylow 2 GL₂) : P →* Fˣ :=
  (d).comp (P : Subgroup GL₂).subtype
private def sylowEmbedding (P : Sylow 2 GL₂) : W (detP P) →* SL(4,F) :=
  Theory.SpecificGroups.PSL4.OddFrattiniSixteen.inclusion.comp (BalancedWreath.map (detP P) d (P : Subgroup GL₂).subtype (MonoidHom.id _) rfl)
private def projectiveSylowMap (P : Sylow 2 GL₂) : W (detP P) →* PSL(4,F) :=
  (QuotientGroup.mk' (center SL(4,F))).comp (sylowEmbedding P)

private theorem projective_kernel (P : Sylow 2 GL₂)
    (hP : ∀ u, detSection (F:=F) u ∈ P)
    (x : W (detP P)) (hx : projectiveSylowMap P x = 1) :
    quotientMap (detP P) ((detSection (F:=F)).codRestrict P hP) P.isPGroup' x = 1 := by
  let sP := (detSection (F:=F)).codRestrict P hP
  let q := QuotientGroup.mk' (frattini P)
  have hc : sylowEmbedding P x ∈ center SL(4,F) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨u,hu,hc,hfirst,hsecond⟩ := inclusion_scalar
    (BalancedWreath.map (detP P) d (P : Subgroup GL₂).subtype (MonoidHom.id _) rfl x) hc
  change (x.left.val.1 : GL₂)=GeneralLinearGroup.scalar (Fin 2) u at hfirst
  change (x.left.val.2 : GL₂)=GeneralLinearGroup.scalar (Fin 2) u at hsecond
  have hr : x.right=1 := hc
  have heq : x.left.val.1 = x.left.val.2 := Subtype.ext (hfirst.trans hsecond.symm)
  have hdet : detP P x.left.val.1 = u^2 := by
    change GeneralLinearGroup.det (x.left.val.1 : GL₂) = u^2
    rw [hfirst]
    apply Units.ext
    simp [pow_two]
  have hsquare : q (sP (u^2)) = 1 := by
    rw [map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
    exact pth_power_mem_frattini_of_isPGroup (p:=2) (sP u)
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hsquare' : q (x.left.val.1^2) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (pth_power_mem_frattini_of_isPGroup (p:=2) x.left.val.1)
  apply Prod.ext
  · change q (x.left.val.1*sP (detP P x.left.val.1)*x.left.val.2)=1
    rw [←heq,hdet,map_mul,map_mul,mul_right_comm,←map_mul,←pow_two,hsquare',one_mul,hsquare]
  · exact hr

private theorem projective_square (P : Sylow 2 GL₂) (x : W (detP P))
    (hx : projectiveSylowMap P x ^ 2 = 1) (hc : x.right ≠ 1) :
    QuotientGroup.mk' (frattini P) (x.left.val.1*x.left.val.2)=1 := by
  have hcentral : sylowEmbedding P (x^2) ∈ center SL(4,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projectiveSylowMap P (x^2)=1
    rwa [map_pow]
  obtain ⟨u,hu,_,hfirst,_⟩ := inclusion_scalar
    (BalancedWreath.map (detP P) d (P : Subgroup GL₂).subtype (MonoidHom.id _) rfl (x^2)) hcentral
  have hc' : x.right=Multiplicative.ofAdd 1 :=
    ((show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right).resolve_left hc
  apply scalar_in_frattini P (x.left.val.1*x.left.val.2) u hu
  change (((x^2).left.val.1 : P) : GL₂)=GeneralLinearGroup.scalar (Fin 2) u at hfirst
  have hm : (x^2).left.val.1=x.left.val.1*x.left.val.2 := by
    simp [pow_two,SemidirectProduct.mul_left,BalancedWreath.action,BalancedWreath.swap,hc']
  rw [hm] at hfirst
  exact hfirst

/-- The actual projective Sylow of a Fermat linear four-space has no order-seven automorphism. -/
theorem linear_four_sylow_no_seven
    (hF : ∃ k : ℕ, Nat.card F = 2^(2^k)+1) (P : Sylow 2 PSL(4,F)) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  have hC : IsPGroup 2 Fˣ := by
    obtain ⟨k,hk⟩ := hF
    apply IsPGroup.of_card (n:=2^k)
    rw [Nat.card_units,hk,Nat.add_sub_cancel]
  obtain ⟨R,hR,hs,hi⟩ := exists_sylow_wreath d (detSection (F:=F)) detSection_spec hC
  let a := sylowEmbedding R
  have ho : Odd (Nat.card F) := by
    obtain ⟨k,hk⟩ := hF
    rw [hk]
    exact (even_two.pow_of_ne_zero (by positivity : 2^k ≠ 0)).add_one
  have hidx : ¬ 2 ∣ a.range.index := by
    change ¬ 2 ∣ (sylowEmbedding R).range.index
    rw [sylowEmbedding,MonoidHom.range_comp]
    have he := (BalancedWreath.map (detP R) d (R : Subgroup GL₂).subtype (MonoidHom.id _) rfl).range.index_map_of_injective
      (f:=Theory.SpecificGroups.PSL4.OddFrattiniSixteen.inclusion)
      Theory.SpecificGroups.PSL4.OddFrattiniSixteen.inclusion_injective
    rw [he]
    exact Nat.prime_two.not_dvd_mul hi.not_two_dvd_nat (odd_index ho).not_two_dvd_nat
  let htwo : IsPGroup 2 a.range :=
    (BalancedWreath.isPGroup (detP R) R.isPGroup').of_surjective
      a.rangeRestrict a.rangeRestrict_surjective
  let S : Sylow 2 SL(4,F) := htwo.toSylow hidx
  let π := QuotientGroup.mk' (center SL(4,F))
  let Q := S.mapSurjective (f:=π) (QuotientGroup.mk'_surjective _)
  let j : W (detP R) →* Q := (π.subgroupMap a.range).comp a.rangeRestrict
  have hj : Function.Surjective j := (π.subgroupMap_surjective a.range).comp a.rangeRestrict_surjective
  have hno := quotient_no_seven (detP R) ((detSection (F:=F)).codRestrict R hR)
    hs R.isPGroup' (GeneralLinearGroup.FermatFrattini.sylow_frattini_le_four hF R) j hj
    (fun x hx => projective_kernel R hR x (congrArg Subtype.val hx))
    (fun x hx hc => projective_square R x (congrArg Subtype.val hx) hc)
  rw [Nat.card_congr (MulAut.congr (P.equiv Q)).toEquiv]
  exact hno

/-- The stored field and projective model markings preserve the Sylow obstruction. -/
theorem linear_four_sylow_no_seven_of_model {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hf : ∃ k : ℕ, p=2^(2^k)+1) (hm : ClassicalGroup.IsPSL Q 4 p)
    (P : Sylow 2 Q) : ¬ 7 ∣ Nat.card (MulAut P) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let c : P ≃* R := P.equivMapOfInjective e.toMonoidHom e.injective
  rw [Nat.card_congr (MulAut.congr c).toEquiv]
  exact linear_four_sylow_no_seven (hF.symm ▸ hf) R

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)

/-- Sylow restriction excludes the original binary-three outer section. -/
theorem linear_four_no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hf : ∃ k : ℕ, p=2^(2^k)+1) (hm : ClassicalGroup.IsPSL Q 4 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hsurj
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hsurj
  apply linear_four_sylow_no_seven_of_model hf hm P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- The exclusion descends through the entire original perfect component center. -/
theorem linear_four_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    ∀ p : ℕ, (∃ k : ℕ, p=2^(2^k)+1) → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 4 p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hm
  exact linear_four_no_outer_section hp hm _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

namespace Unitary
open BenderSuzuki.MatrixGroups Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.OddFundamental
open Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U₂" => HermitianForm.unitarySubgroup (form σ hσ 2)
local notation "Cnorm" => OddFourRanks.normOne (form σ hσ 4)
local notation "dU" => Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.det σ hσ
local notation "sU" => Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.detSection σ hσ
local notation "incU" => Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.inclusion σ hσ

private local instance unitaryGroup : Group U₂ := Subgroup.toGroup _
private local instance sylowGroup (P : Sylow 2 U₂) : Group P := Subgroup.toGroup _
private local instance sylowFrattiniGroup (P : Sylow 2 U₂) : Group (P ⧸ frattini P) :=
  QuotientGroup.Quotient.group _

omit [Finite F] in
private theorem scalarRoot_mem (u : Cnorm) : scalarRoot u.val ∈ U₂ := by
  have hu := OddFourRanks.normOne_norm (form σ hσ 4) u
  change σ (u.val : F) * (u.val : F)=1 at hu
  rw [HermitianForm.mem_unitarySubgroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarRoot,GeneralLinearGroup.diagonalPair,GeneralLinearGroup.coordinateSwap,
      HermitianForm.conjTranspose,form,Matrix.mul_apply,Fin.sum_univ_two,hu]

private theorem scalar_in_frattini (P : Sylow 2 U₂) (x : P) (u : Cnorm)
    (hu : u^4=1) (he : ((x : U₂) : GL₂)=GeneralLinearGroup.scalar (Fin 2) u.val) :
    QuotientGroup.mk' (frattini P) x = QuotientGroup.mk' (frattini P) (1 : P) := by
  let : One (P ⧸ frattini P) := (sylowFrattiniGroup σ hσ P).toOne
  rw [map_one]
  let z : U₂ := x
  let y : U₂ := ⟨scalarRoot u.val,scalarRoot_mem σ hσ u⟩
  have hz : z ∈ center U₂ := by
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    change b.val*(x : U₂).val=(x : U₂).val*b.val
    rw [he]
    have hh : GeneralLinearGroup.scalar (Fin 2) u.val ∈ center GL₂ := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u.val,rfl⟩
    exact mem_center_iff.mp hh b.val
  have hy : y^2=z := Subtype.ext ((scalarRoot_sq u.val).trans he.symm)
  have hz4 : z^4=1 := by
    apply Subtype.ext
    change (x : U₂).val^4=1
    rw [he,←map_pow,show u.val^4=1 from congrArg Subtype.val hu,map_one]
  obtain ⟨v,hv⟩ := central_fourth_square_in_sylow P hz hy hz4
  have hvx : v^2=x := Subtype.ext hv
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  exact (QuotientGroup.eq_one_iff _).mpr
    (hvx ▸ pth_power_mem_frattini_of_isPGroup (p:=2) v)

private theorem inclusion_scalar (x : W dU) {p : ℕ}
    (hj : ∀ a, σ a=a^p)
    (hx : ProjectiveKernel.project (form σ hσ 4) (incU x)=1) :
    ∃ u : Cnorm, u^4=1 ∧ x.right=1 ∧
      x.left.val.1.val=GeneralLinearGroup.scalar (Fin 2) u.val ∧
      x.left.val.2.val=GeneralLinearGroup.scalar (Fin 2) u.val := by
  have hz : (incU x).val ∈ center (GL (Fin 4) F) :=
    ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hx)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u,hu⟩ := hz
  have hs : GeneralLinearGroup.scalar (Fin 4) u ∈ (form σ hσ 4).specialSubgroup :=
    hu.symm ▸ (incU x).property
  have hpows := (ProjectiveKernel.scalar_special_iff (form σ hσ 4) hj u).mp hs
  have hnorm : u ∈ Cnorm := by
    change σ (u : F)=(u : F)⁻¹
    rw [hj]
    apply (mul_eq_one_iff_eq_inv₀ (Units.ne_zero u)).mp
    have hh := congrArg Units.val hpows.2
    change (u : F)^(p+1)=1 at hh
    simpa only [pow_succ] using hh
  let un : Cnorm := ⟨u,hnorm⟩
  have hc : x.right=1 := by
    rcases (show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right with hc | hc
    · exact hc
    · exfalso
      have hh := congrArg (fun a : GL (Fin 4) F => a.val 0 0) hu
      change (u : F) = ((Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.pairHom σ hσ x.left *
        Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.swapHom σ hσ x.right).val.val 0 0) at hh
      rw [hc] at hh
      have hh0 : ((Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.pairHom σ hσ x.left *
        Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.swapHom σ hσ (Multiplicative.ofAdd 1)).val.val 0 0) = 0 := by
        change ((blockMatrix x.left.val.1.val.val x.left.val.2.val.val *
          Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.swapMatrix : Matrix (Fin 4) (Fin 4) F)) 0 0=0
        simp [blockMatrix,Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.swapMatrix,
          Matrix.reindex_apply,Matrix.mul_apply,Fin.sum_univ_succ,finSumFinEquiv]
        rfl
      exact Units.ne_zero u (hh.trans hh0)
  have hblock : blockMatrix x.left.val.1.val.val x.left.val.2.val.val = Matrix.scalar (Fin 4) (u : F) := by
    have hh := congrArg Units.val hu.symm
    change (Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.pairHom σ hσ x.left *
      Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.swapHom σ hσ x.right).val.val = _ at hh
    rw [hc,map_one,mul_one] at hh
    exact hh
  refine ⟨un,Subtype.ext hpows.1,hc,?_,?_⟩
  · apply Units.ext
    ext i j
    have hh := congrArg (fun a : Matrix (Fin 4) (Fin 4) F =>
      a (finSumFinEquiv (m:=2) (n:=2) (.inl i)) (finSumFinEquiv (m:=2) (n:=2) (.inl j))) hblock
    fin_cases i <;> fin_cases j <;> simpa [blockMatrix,Matrix.reindex_apply,Matrix.scalar,un] using hh
  · apply Units.ext
    ext i j
    have hh := congrArg (fun a : Matrix (Fin 4) (Fin 4) F =>
      a (finSumFinEquiv (m:=2) (n:=2) (.inr i)) (finSumFinEquiv (m:=2) (n:=2) (.inr j))) hblock
    fin_cases i <;> fin_cases j <;> simpa [blockMatrix,Matrix.reindex_apply,Matrix.scalar,un] using hh

private abbrev detP (P : Sylow 2 U₂) : P →* Cnorm :=
  (dU).comp (P : Subgroup U₂).subtype
private def sylowEmbedding (P : Sylow 2 U₂) :
    W (detP σ hσ P) →* (form σ hσ 4).specialSubgroup :=
  (incU).comp (BalancedWreath.map (detP σ hσ P) dU (P : Subgroup U₂).subtype (MonoidHom.id _) rfl)
private def projectiveSylowMap (P : Sylow 2 U₂) :
    W (detP σ hσ P) →* ProjectiveSpecialUnitaryMatrixGroup (form σ hσ 4) :=
  (ProjectiveKernel.project (form σ hσ 4)).comp (sylowEmbedding σ hσ P)

private theorem projective_kernel {p : ℕ} (hj : ∀ a, σ a=a^p)
    (P : Sylow 2 U₂) (hP : ∀ u, sU u ∈ P)
    (x : W (detP σ hσ P)) (hx : projectiveSylowMap σ hσ P x = 1) :
    quotientMap (detP σ hσ P) ((sU).codRestrict P hP) P.isPGroup' x =
      (QuotientGroup.mk' (frattini P) (1 : P), (1 : C2)) := by
  let : One (P ⧸ frattini P) := (sylowFrattiniGroup σ hσ P).toOne
  rw [map_one]
  let sP := (sU).codRestrict P hP
  let q := QuotientGroup.mk' (frattini P)
  obtain ⟨u,hu,hc,hfirst,hsecond⟩ := inclusion_scalar σ hσ
    (BalancedWreath.map (detP σ hσ P) dU (P : Subgroup U₂).subtype (MonoidHom.id _) rfl x) hj hx
  change (x.left.val.1 : U₂).val=GeneralLinearGroup.scalar (Fin 2) u.val at hfirst
  change (x.left.val.2 : U₂).val=GeneralLinearGroup.scalar (Fin 2) u.val at hsecond
  have hr : x.right=1 := hc
  have heq : x.left.val.1 = x.left.val.2 := Subtype.ext (Subtype.ext (hfirst.trans hsecond.symm))
  have hdet : detP σ hσ P x.left.val.1 = u^2 := by
    apply Subtype.ext
    change GeneralLinearGroup.det (x.left.val.1 : U₂).val = u.val^2
    rw [hfirst]
    apply Units.ext
    simp [pow_two]
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hsquare : q (sP (u^2)) = 1 := by
    rw [map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pth_power_mem_frattini_of_isPGroup (p:=2) (sP u))
  have hsquare' : q (x.left.val.1^2) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (pth_power_mem_frattini_of_isPGroup (p:=2) x.left.val.1)
  apply Prod.ext
  · change q (x.left.val.1*sP (detP σ hσ P x.left.val.1)*x.left.val.2)=1
    rw [←heq,hdet,map_mul,map_mul,mul_right_comm,←map_mul,←pow_two,hsquare',one_mul,hsquare]
  · exact hr

private theorem projective_square {p : ℕ} (hj : ∀ a, σ a=a^p)
    (P : Sylow 2 U₂) (x : W (detP σ hσ P))
    (hx : projectiveSylowMap σ hσ P x ^ 2 = 1) (hc : x.right ≠ 1) :
    QuotientGroup.mk' (frattini P) (x.left.val.1*x.left.val.2)=
      QuotientGroup.mk' (frattini P) (1 : P) := by
  have hcentral : projectiveSylowMap σ hσ P (x^2)=1 := by rwa [map_pow]
  obtain ⟨u,hu,_,hfirst,_⟩ := inclusion_scalar σ hσ
    (BalancedWreath.map (detP σ hσ P) dU (P : Subgroup U₂).subtype (MonoidHom.id _) rfl (x^2)) hj hcentral
  have hc' : x.right=Multiplicative.ofAdd 1 :=
    ((show ∀ c : C2, c=1 ∨ c=Multiplicative.ofAdd 1 from by decide) x.right).resolve_left hc
  apply scalar_in_frattini σ hσ P (x.left.val.1*x.left.val.2) u hu
  change (((x^2).left.val.1 : U₂) : GL₂)=GeneralLinearGroup.scalar (Fin 2) u.val at hfirst
  have hm : (x^2).left.val.1=x.left.val.1*x.left.val.2 := by
    simp [pow_two,SemidirectProduct.mul_left,BalancedWreath.action,BalancedWreath.swap,hc']
  rw [hm] at hfirst
  exact hfirst

private theorem sylow_no_seven {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hm : ∃ k : ℕ, p+1=2^k)
    (hF : Nat.card F=p^2) (hj : ∀ a, σ a=a^p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup (form σ hσ 4))) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  have hC : IsPGroup 2 Cnorm := by
    obtain ⟨k,hk⟩ := hm
    apply IsPGroup.of_card (n:=k)
    rw [norm_one_card σ hσ (Fact.out : p.Prime).one_lt.le hF hj,hk]
  obtain ⟨R,hR,hs,hi⟩ := exists_sylow_wreath dU sU
    (Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.detSection_spec σ hσ) hC
  let a := sylowEmbedding σ hσ R
  have hidx : ¬ 2 ∣ a.range.index := by
    change ¬ 2 ∣ (sylowEmbedding σ hσ R).range.index
    rw [sylowEmbedding,MonoidHom.range_comp]
    have he := (BalancedWreath.map (detP σ hσ R) dU (R : Subgroup U₂).subtype (MonoidHom.id _) rfl).range.index_map_of_injective
      (f:=incU) (Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.inclusion_injective σ hσ)
    rw [he]
    exact Nat.prime_two.not_dvd_mul hi.not_two_dvd_nat
      (Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.odd_index σ hσ ho hF hj).not_two_dvd_nat
  let htwo : IsPGroup 2 a.range :=
    (BalancedWreath.isPGroup (detP σ hσ R) R.isPGroup').of_surjective
      a.rangeRestrict a.rangeRestrict_surjective
  let S : Sylow 2 (form σ hσ 4).specialSubgroup := htwo.toSylow hidx
  let π := ProjectiveKernel.project (form σ hσ 4)
  let Q := S.mapSurjective (f:=π) (ProjectiveKernel.project_surjective _)
  let j : W (detP σ hσ R) →* Q := (π.subgroupMap a.range).comp a.rangeRestrict
  have hjs : Function.Surjective j := (π.subgroupMap_surjective a.range).comp a.rangeRestrict_surjective
  have hno := quotient_no_seven (detP σ hσ R) ((sU).codRestrict R hR)
    hs R.isPGroup' (MersenneFrattini.unitary_two_frattini_le σ hσ hm hF hj R) j hjs
    (fun x hx => projective_kernel σ hσ hj R hR x (congrArg Subtype.val hx))
    (fun x hx hc => projective_square σ hσ hj R x (congrArg Subtype.val hx) hc)
  rw [Nat.card_congr (MulAut.congr (P.equiv Q)).toEquiv]
  exact hno
end Unitary

/-- The full Hermitian-form and projective-kernel transport gives the same
obstruction for the original Mersenne unitary model. -/
theorem unitary_four_sylow_no_seven_of_model {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hm : ∃ k : ℕ, p+1=2^k)
    (hmodel : ClassicalGroup.IsPSU Q 4 p) (P : Sylow 2 Q) :
    ¬ 7 ∣ Nat.card (MulAut P) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hmodel
  obtain ⟨basis,a,ap,hbasis,ha,hap⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.exists_identityGram_transport J p hp hF hj
  let b := e.trans ap
  let R := P.mapSurjective (f:=b.toMonoidHom) b.surjective
  let c : P ≃* R := P.equivMapOfInjective b.toMonoidHom b.injective
  rw [Nat.card_congr (MulAut.congr c).toEquiv]
  have ho : Odd p := by
    obtain ⟨k,hk⟩ := hm
    have hk0 : k ≠ 0 := by intro hz; simp only [hz,pow_zero] at hk; have := hp.two_le; omega
    have he : Even (p+1) := hk.symm ▸ even_two.pow_of_ne_zero hk0
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp he)
  exact Unitary.sylow_no_seven J.conj J.conj_involutive ho hm hF hj R

/-- The Mersenne unitary family has no original binary-three outer section. -/
theorem unitary_four_no_outer_section {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} (hp : p.Prime) (hm : ∃ k : ℕ, p+1=2^k) (hmodel : ClassicalGroup.IsPSU Q 4 p)
    (U : Subgroup (MulAut.Outer Q)) (f : U →* BinaryLinearThree.Group) :
    ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 Q := default
  let : Group.IsSolvable (fixingSubgroup (MulAut Q) (P : Set Q)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hd := MulAut.simple_outer_section_card_dvd_sylow_aut P
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) U f hf
  apply unitary_four_sylow_no_seven_of_model hp hm hmodel P
  apply dvd_trans ?_ hd
  rw [Matrix.PSL3Two.card_SL]
  decide

/-- Descent keeps the entire original unitary component center. -/
theorem unitary_four_cover_exclusion {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) :
    ∀ p : ℕ, p.Prime → (∃ k : ℕ, p+1=2^k) → ¬ ClassicalGroup.IsPSU (K ⧸ center K) 4 p := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨U,f,hf⟩ := ho
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let a := U.equivMapOfInjective j
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  intro p hp hm hmodel
  exact unitary_four_no_outer_section hp hm hmodel _ (f.comp a.symm.toMonoidHom)
    (hf.comp a.symm.surjective)

/-- Only the original odd-prime G₂ family remains in the outer branch. -/
inductive RemainingOuterModel (Q : Type*) [Group Q] : Prop
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : ClassificationModels.IsG2At Q p)

/-- Inspect the same full component catalogue after the two degree-four exclusions. -/
theorem remaining_outer_models {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinearThree.Group,
      Function.Surjective f) : RemainingOuterModel (K ⧸ center K) := by
  cases DoubledBinaryOddWreath.remaining_outer_models hm ho with
  | g2_odd p hp hq e => exact .g2_odd p hp hq e
  | linear_four p hp hf e => exact (linear_four_cover_exclusion ho p hf e).elim
  | unitary_four p hp hf e => exact (unitary_four_cover_exclusion ho p hp hf e).elim

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddBalanced
