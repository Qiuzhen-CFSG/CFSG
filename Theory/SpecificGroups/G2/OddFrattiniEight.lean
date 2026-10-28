module
public import Theory.SpecificGroups.G2.OddFrattiniSixteen
public import Theory.GroupTheory.NormalizedSupCard
import all Theory.SpecificGroups.G2.OddFrattiniSixteen

/-!
# Three Frattini generators for odd-prime G₂ Sylow subgroups

The orthogonal cover is a diagonal involution extension of two SL₂ factors.
Choose a Sylow subgroup in the single-factor extension containing the given
involution. Its two embeddings generate a Sylow subgroup in the double
extension: the two projections embed their join into the product of the
single Sylows, and maximality identifies both projected Sylow images.

Each single-factor image in the doubled Frattini quotient has order at most
four. Their common outer involution survives, detected by the literal C₂
projection. The subgroup product formula bounds the quotient order by eight.
The original diagonal-kernel and odd-index calculation then transfers this
bound to every Sylow subgroup of the actual G₂ model, including p = 3.

`import all` deliberately shares the internal quaternion coordinates and
odd-index transport with `OddFrattiniSixteen`; no private implementation
appears in the exported theorem statements. The older bound is preserved.
Source: the Sylow restriction in Aschbacher--Smith 4.4.10--11 and 12.1.9,
printed pp.621,793. Coordinate attribution and license: LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Atlas.G2.OddFrattiniEight
open MultiplierOrdinary.OddTwoPrimary OrthogonalMap OddFrattiniSixteen
variable {p : ℕ} [Fact p.Prime] (d : ZMod p) (hd : d ≠ 0)

private def secondProjection : Double d hd →* Single d hd :=
  SemidirectProduct.map (MonoidHom.snd _ _) (MonoidHom.id _) (by
    intro c
    have hc : c = 1 ∨ c = .ofAdd 1 := by
      exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c.toAdd
    rcases hc with rfl | rfl
    · ext A; simp
    · apply MonoidHom.ext
      intro A
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,action,singleAction,involutionHom_generator]
      rfl)
private def firstInclusion : Single d hd →* Double d hd :=
  SemidirectProduct.map (MonoidHom.inl _ _) (MonoidHom.id _) (by
    intro c
    have hc : c = 1 ∨ c = .ofAdd 1 := by
      exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c.toAdd
    rcases hc with rfl | rfl
    · apply MonoidHom.ext; intro A; simp
    · apply MonoidHom.ext; intro A
      simp [action,singleAction,involutionHom_generator,productTwist,MulEquiv.prodCongr])
private def secondInclusion : Single d hd →* Double d hd :=
  SemidirectProduct.map (MonoidHom.inr _ _) (MonoidHom.id _) (by
    intro c
    have hc : c = 1 ∨ c = .ofAdd 1 := by
      exact (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) c.toAdd
    rcases hc with rfl | rfl
    · apply MonoidHom.ext; intro A; simp
    · apply MonoidHom.ext; intro A
      simp [action,singleAction,involutionHom_generator,productTwist,MulEquiv.prodCongr])

private theorem split (x : Double d hd) :
    x = firstInclusion d hd (SemidirectProduct.inl x.left.1) *
      secondInclusion d hd (secondProjection d hd x) := by
  apply SemidirectProduct.ext
  · change x.left = (x.left.1,1) * action d hd 1 (1,x.left.2)
    simp
  · exact (one_mul _).symm

private theorem firstPart (x : Double d hd) :
    (SemidirectProduct.inl x.left.1 : Single d hd) =
      firstProjection d hd x * (SemidirectProduct.inr x.right)⁻¹ :=
  (eq_mul_inv_iff_mul_eq).mpr (SemidirectProduct.inl_left_mul_inr_right (firstProjection d hd x))

private theorem diagonal_sylow_frattini_le_eight (ho : Odd p) (hns : ¬ IsSquare (-d))
    (S : Sylow 2 (Single d hd))
    (hC : (SemidirectProduct.inr : C2 →* Single d hd).range ≤ S) :
    ∃ R : Sylow 2 (Double d hd), Nat.card (R ⧸ frattini R) ≤ 8 := by
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
  have hfirst (x : R) : (SemidirectProduct.inl x.val.left.1 : Single d hd) ∈ S := by
    rw [firstPart]
    exact S.mul_mem (hRr ▸ mem_map_of_mem r x.property)
      (S.inv_mem (hC ⟨x.val.right,rfl⟩))
  have hsecond (x : R) : s x.val ∈ S := by
    change s x.val ∈ (S : Subgroup _)
    rw [← hRs]
    exact mem_map_of_mem s x.property
  let a : S →* R := (i.comp (S : Subgroup (Single d hd)).subtype).codRestrict _
    (fun x => hPR ((show (S : Subgroup _).map i ≤ P from le_sup_left) (mem_map_of_mem i x.property)))
  let b : S →* R := (j.comp (S : Subgroup (Single d hd)).subtype).codRestrict _
    (fun x => hPR ((show (S : Subgroup _).map j ≤ P from le_sup_right) (mem_map_of_mem j x.property)))
  have hab (x : R) : x = a ⟨_,hfirst x⟩ * b ⟨_,hsecond x⟩ :=
    Subtype.ext (split d hd x.val)
  let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
  let : IsElementaryAbelian 2 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  let π := QuotientGroup.mk' (frattini R)
  let A := (π.comp a).range
  let B := (π.comp b).range
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom A.subtype A.subtype_injective).trans
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) }
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom B.subtype B.subtype_injective).trans
      (IsElementaryAbelian.exponent_dvd_p 2 (R ⧸ frattini R)) }
  have hA : Nat.card A ≤ 4 :=
    (BinaryFrattiniExtension.elementary_card_le (π.comp a).rangeRestrict
      (π.comp a).rangeRestrict_surjective).trans (single_sylow_frattini_le_four ho d hd hns S)
  have hB : Nat.card B ≤ 4 :=
    (BinaryFrattiniExtension.elementary_card_le (π.comp b).rangeRestrict
      (π.comp b).rangeRestrict_surjective).trans (single_sylow_frattini_le_four ho d hd hns S)
  have hAB : A ⊔ B = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini R) y
    rw [hab x,map_mul]
    exact mul_mem_sup ⟨_,rfl⟩ ⟨_,rfl⟩
  let c : S := ⟨SemidirectProduct.inr (.ofAdd 1),hC ⟨.ofAdd 1,rfl⟩⟩
  have hc : a c = b c := rfl
  have hcne : π (a c) ≠ 1 := by
    intro he
    have hm : a c ∈ frattini R := (QuotientGroup.eq_one_iff _).mp he
    let t : R →* C2 := SemidirectProduct.rightHom.comp (R : Subgroup (Double d hd)).subtype
    have hΦ : frattini R ≤ t.ker := Theory.GroupTheory.frattini_le_ker_of_square_image t (by
      intro x
      rw [pow_two]
      change (t x).toAdd + (t x).toAdd = 0
      exact CharTwo.add_self_eq_zero _)
    have hz : t (a c) = 1 := hΦ hm
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1) hz
  have hI : 2 ≤ Nat.card (A ⊓ B : Subgroup (R ⧸ frattini R)) := by
    apply (Subgroup.one_lt_card_iff_ne_bot _).mpr
    intro hbot
    have hv : π (a c) ∈ A ⊓ B := ⟨⟨c,rfl⟩,⟨c,congrArg π hc.symm⟩⟩
    rw [hbot,mem_bot] at hv
    exact hcne hv
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hAB,card_top] at hmul
  refine ⟨R,?_⟩
  have hsmall : Nat.card A * Nat.card B ≤ 16 :=
    (Nat.mul_le_mul hA hB).trans (by decide)
  nlinarith

private theorem double_sylow_frattini_le_eight (ho : Odd p) (hns : ¬ IsSquare (-d))
    (P : Sylow 2 (Double d hd)) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  have hC : IsPGroup 2 C2 := IsPGroup.of_card (n := 1) (by simp [C2])
  obtain ⟨S,hS⟩ := (hC.of_surjective
    (SemidirectProduct.inr : C2 →* Single d hd).rangeRestrict
    (SemidirectProduct.inr : C2 →* Single d hd).rangeRestrict_surjective).exists_le_sylow
  obtain ⟨R,hR⟩ := diagonal_sylow_frattini_le_eight d hd ho hns S hS
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv R)]
  exact hR
end Atlas.G2.OddFrattiniEight

public section
namespace Atlas.G2.OddFrattiniEight
open OddFrattiniSixteen

/-- The original odd-prime G₂ Sylow subgroup has at most three generators. -/
theorem prime_frattini_card_le_eight {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (P : Sylow 2 (Model (ZMod p))) : Nat.card (P ⧸ frattini P) ≤ 8 :=
  prime_frattini_card_le_of_double_bound hp 8
    (fun d hd hns R => double_sylow_frattini_le_eight d hd
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hns R) P

/-- Field transport retains the actual octonion model and every marked Sylow. -/
theorem frattini_card_le_eight {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hF : Nat.card F = p)
    (P : Sylow 2 (Model F)) : Nat.card (P ⧸ frattini P) ≤ 8 := by
  have hp : 2 < p := by
    have hprime := (Fact.out : p.Prime).two_le
    have hne : p ≠ 2 := by rintro rfl; norm_num at ho
    omega
  let := Fintype.ofFinite F
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := fieldEquiv e.symm
  let Q := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have he : P ≃* Q := P.equivMapOfInjective f.toMonoidHom f.injective
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr he]
  exact prime_frattini_card_le_eight hp Q
end Atlas.G2.OddFrattiniEight
