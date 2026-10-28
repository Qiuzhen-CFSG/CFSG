module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionIsotypic
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderPair

/-!
# Cubic stabilization of a repeated chosen-seed type

A starred cubic actor exchanging complementary summands has a stabilizer
whose common fixed space on either summand has dimension one. The proof
uses the same actor rank on the whole pair and strict minimality on its
index-two stabilizer; it does not count constituent types as copies.

For the chosen-seed application, an additional disjoint copy of the same
irreducible type rules out that fixed line. All stabilizer displacements
lie in the line and hence in the seed. On the other copy the component
action is therefore unchanged, so the stabilizer commutes with the component
on the seed. This makes the fixed line an invariant proper subspace,
contradicting irreducibility. The original action is retained through a
surjective homomorphism, allowing application to the faithful normalizer
image without changing the component or its central cover.

This proves the needed specialization of D.2.9(6) at D.3.12. Its actual
application is `SeedAlternativesMovedExhaustionStabilization`; D.3.13--19
and normalizer-orbit exhaustion remain with the source325 assembly owner.
Source: Aschbacher--Smith, printed pp.180--183 and 201--204.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) H W)

omit [FiniteDimensional (ZMod 2) W] in
private theorem ratio_cross_lt {A B : Subgroup H}
    (hA : IsElementaryTwo A) (hB : IsElementaryTwo B)
    (h : actionRatio ρ A < actionRatio ρ B) :
    fixedCodim ρ A * rank B < fixedCodim ρ B * rank A := by
  have ha : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  have hb : (rank B : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB.rank_pos)
  have hh := (ENNReal.div_lt_iff (Or.inl ha) (Or.inl (by simp))).mp h
  have hh2 : (fixedCodim ρ A : ℝ≥0∞) <
      (fixedCodim ρ B * rank A : ℝ≥0∞) / rank B := by
    simpa only [actionRatio,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have hh' := (ENNReal.lt_div_iff_mul_lt (Or.inl hb) (Or.inl (by simp))).mp hh2
  exact_mod_cast hh'

/-- A swapping starred actor has a one-dimensional stabilizer fixed space
on either complete summand. The strict minimum excludes the two-dimensional
fixed-space boundary in D.2.9(5ii). -/
theorem starred_swapping_fixed_finrank_one
    (I : Submodule (ZMod 2) W) {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    {a : H} (ha : a ∈ A) (hm : I.map (ρ a) ≠ I)
    (hcomp : IsCompl I (I.map (ρ a))) (hdim : 2 < Module.finrank (ZMod 2) I)
    (htwo : ∀ b ∈ A, I.map (ρ b) = I ∨ I.map (ρ b) = I.map (ρ a)) :
    Module.finrank (ZMod 2)
      (I ⊓ fixedSpace ρ (A ⊓ subspaceStabilizer ρ I) : Submodule (ZMod 2) W) = 1 := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let B := A ⊓ subspaceStabilizer ρ I
  let C := I ⊓ fixedSpace ρ B
  let J := I.map (ρ a)
  have ha2 : a*a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hr : rank A = rank B + 1 := pair_stabilizer_rank ρ I A hA.1.2.1 ha ha2 hm htwo
  have hb : fixedCodim ρ A ≤ 2 * rank A :=
    (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hA.1.1)
  have hl := swapped_pair_codim_lower_bound ρ I A ha ha2 hcomp.disjoint
  have hB : B ≠ ⊥ := by
    intro hz
    rw [hz,Representation.BinaryOffender.rank_bot,zero_add] at hr
    rw [hr] at hb
    omega
  have heB : IsElementaryTwo B := hA.1.2.1.of_le inf_le_left hB
  have hpB : IsPGroup 2 B := by
    let := heB.2
    exact IsElementaryAbelian.isPGroup 2 B
  have hpos : 0 < Module.finrank (ZMod 2) C := by
    have hi : I ≠ ⊥ := fun hz => by
      rw [hz,finrank_bot] at hdim
      omega
    obtain ⟨v,hv,hv0,hvf⟩ := PermutedSupports.exists_nonzero_fixed ρ B hpB I hi inf_le_right
    exact Nat.pos_of_ne_zero (fun hz => hv0 ((Submodule.finrank_eq_zero.mp hz).le ⟨hv,hvf⟩))
  have hac (b : B) : a * b.val = b.val * a :=
    congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) ⟨b.val,b.property.1⟩)
  have hfixed : (fixedSpace ρ B).map (ρ a) = fixedSpace ρ B := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩ b
      change ρ b.val (ρ a v) = ρ a v
      rw [←Module.End.mul_apply,←map_mul,←hac b,map_mul,Module.End.mul_apply]
      exact congrArg (ρ a) (hv b)
    · intro v hv
      refine ⟨ρ a v,?_,?_⟩
      · intro b
        change ρ b.val (ρ a v) = ρ a v
        rw [←Module.End.mul_apply,←map_mul,←hac b,map_mul,Module.End.mul_apply]
        exact congrArg (ρ a) (hv b)
      · rw [←Module.End.mul_apply,←map_mul,ha2,map_one,Module.End.one_apply]
  have hCJ : C.map (ρ a) = J ⊓ fixedSpace ρ B := by
    have hinj : Function.Injective (ρ a) :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)).injective
    change (I ⊓ fixedSpace ρ B).map (ρ a) = J ⊓ fixedSpace ρ B
    rw [Submodule.map_inf (ρ a) hinj,hfixed]
  have hstJ : B ≤ subspaceStabilizer ρ J := by
    apply le_subspaceStabilizer
    rintro b hb _ ⟨v,hv,rfl⟩
    refine ⟨ρ b v,(hb.2 v).2 hv,?_⟩
    rw [←Module.End.mul_apply,←Module.End.mul_apply,←map_mul,←map_mul,hac ⟨b,hb⟩]
  have hsplit := fixedSpace_inf_disjoint_sup ρ I J B inf_le_right hstJ hcomp.disjoint
  rw [hcomp.sup_eq_top,top_inf_eq] at hsplit
  have hsum := C.finrank_sup_add_finrank_inf_eq (J ⊓ fixedSpace ρ B)
  have hdC : Disjoint C (J ⊓ fixedSpace ρ B) := hcomp.disjoint.mono inf_le_left inf_le_left
  rw [hdC.eq_bot,finrank_bot,add_zero,←hsplit,←hCJ,finrank_map_action] at hsum
  have hdimW := I.finrank_sup_add_finrank_inf_eq J
  rw [hcomp.sup_eq_top,hcomp.disjoint.eq_bot,finrank_bot,add_zero,
    finrank_top,finrank_map_action] at hdimW
  have hfixedB := fixedCodim_add_finrank ρ B
  have hrest := fixedCodim_add_finrank (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B)
  rw [(restrictedFixedSpaceEquiv ρ I B inf_le_right).finrank_eq] at hrest
  have hlt : B < A := lt_of_le_of_ne inf_le_left (by
    intro he
    have : rank A = rank A + 1 := he ▸ hr
    omega)
  have hcross := ratio_cross_lt ρ hA.1.2.1 heB (QhatStar.ratio_lt_of_lt ρ hA hlt hB)
  change fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) +
    Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) I at hrest
  change Module.finrank (ZMod 2) I +
    fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) ≤ fixedCodim ρ A at hl
  have hfC := C.finrank_le
  change Module.finrank (ZMod 2) C = 1
  by_contra hn
  have htwoC : 2 ≤ Module.finrank (ZMod 2) C := by omega
  have hbound : 2 * Module.finrank (ZMod 2) I ≤
      2 * rank B + 2 + Module.finrank (ZMod 2) C := by omega
  have hcodB : fixedCodim ρ B + 2 * Module.finrank (ZMod 2) C =
      2 * Module.finrank (ZMod 2) I := by omega
  have hleft : (2 * Module.finrank (ZMod 2) I - Module.finrank (ZMod 2) C) * rank B ≤
      fixedCodim ρ A * rank B := by
    apply Nat.mul_le_mul_right
    omega
  have hcf : Module.finrank (ZMod 2) C ≤ Module.finrank (ZMod 2) I := Submodule.finrank_mono inf_le_left
  have hsub : 2 * Module.finrank (ZMod 2) I - Module.finrank (ZMod 2) C +
      Module.finrank (ZMod 2) C = 2 * Module.finrank (ZMod 2) I := by omega
  nlinarith [Nat.mul_le_mul_right (Module.finrank (ZMod 2) C) hbound,
    Nat.zero_le ((Module.finrank (ZMod 2) C - 2) * (2 * Module.finrank (ZMod 2) I - Module.finrank (ZMod 2) C))]

open Representation.BinaryOffender.Homogeneous

omit [Finite H] in
/-- A normalizing actor with all displacement in a common fixed line cannot
preserve one irreducible constituent when another disjoint copy is present. -/
theorem no_fixed_line_with_repeated_constituent
    (N B : Subgroup H) [N.Normal] (I : Submodule (ZMod 2) W)
    (S R : Subrepresentation (ρ.comp N.subtype))
    (hS : IsIrreducible S.toRepresentation) (hd : 1 < Module.finrank (ZMod 2) S.toSubmodule)
    (hSI : S.toSubmodule ≤ I) (hRI : R.toSubmodule ≤ I)
    (hsame : SameModule S R) (hdis : Disjoint S R)
    (hBI : B ≤ subspaceStabilizer ρ I) (hBS : B ≤ subspaceStabilizer ρ S.toSubmodule)
    (hline : Module.finrank (ZMod 2) (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) W) = 1)
    (hfixed : ∃ v ∈ S, v ≠ 0 ∧ v ∈ fixedSpace ρ B)
    (hmove : ∀ b ∈ B, ∀ v ∈ I, ρ b v - v ∈ fixedSpace ρ B) : False := by
  let C := I ⊓ fixedSpace ρ B
  have hSC : S.toSubmodule ⊓ fixedSpace ρ B = C := by
    apply Submodule.eq_of_le_of_finrank_eq (inf_le_inf_right _ hSI)
    obtain ⟨v,hv,hv0,hvf⟩ := hfixed
    have hnonzero : S.toSubmodule ⊓ fixedSpace ρ B ≠ ⊥ := by
      intro hz
      exact hv0 (hz.le ⟨hv,hvf⟩)
    have hpos := Nat.pos_of_ne_zero (fun hz => hnonzero (Submodule.finrank_eq_zero.mp hz))
    have hle := Submodule.finrank_mono (inf_le_inf_right (fixedSpace ρ B) hSI)
    change _ = Module.finrank (ZMod 2) (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) W)
    omega
  have hCS : C ≤ S.toSubmodule := hSC.symm.le.trans inf_le_left
  have hdisp (b : H) (hb : b ∈ B) (v : W) (hv : v ∈ I) : ρ b v - v ∈ S :=
    hCS ⟨I.sub_mem ((hBI hb v).2 hv) hv,hmove b hb v hv⟩
  have hcomm (b : H) (hb : b ∈ B) (n : N) (v : S) :
      ρ b (ρ n.val v.val) = ρ n.val (ρ b v.val) := by
    let n' : N := ⟨b⁻¹*n.val*b,by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n.val n.property b⁻¹⟩
    have hR (r : R) : R.toRepresentation n' r = R.toRepresentation n r := by
      apply Subtype.ext
      apply sub_eq_zero.mp
      have hRmem : ρ n'.val r.val - ρ n.val r.val ∈ R :=
        R.toSubmodule.sub_mem (R.apply_mem_toSubmodule n' r.property) (R.apply_mem_toSubmodule n r.property)
      have hSmem : ρ n'.val r.val - ρ n.val r.val ∈ S := by
        have hbr := hdisp b hb r.val (hRI r.property)
        have hnbr := S.apply_mem_toSubmodule n hbr
        have hbi := hdisp b⁻¹ (B.inv_mem hb) (ρ n.val r.val)
          (hRI (R.apply_mem_toSubmodule n r.property))
        have hnbr' := (hBS (B.inv_mem hb) _).2 hnbr
        have hh := S.toSubmodule.add_mem hnbr' hbi
        change ρ (b⁻¹*n.val*b) r.val - ρ n.val r.val ∈ S.toSubmodule
        have heq : ρ (b⁻¹*n.val*b) r.val - ρ n.val r.val =
            ρ b⁻¹ (ρ n.val (ρ b r.val-r.val)) + (ρ b⁻¹ (ρ n.val r.val)-ρ n.val r.val) := by
          simp only [map_mul,Module.End.mul_apply,map_sub]
          abel
        rw [heq]
        exact hh
      have hh : ρ n'.val r.val - ρ n.val r.val ∈ S ⊓ R := ⟨hSmem,hRmem⟩
      rw [hdis.eq_bot] at hh
      exact hh
    obtain ⟨e,he⟩ := hsame
    have hSact (w : S) : S.toRepresentation n' w = S.toRepresentation n w := by
      apply e.injective
      rw [he,he,hR]
    have hw := congrArg Subtype.val (hSact v)
    have hh := congrArg (ρ b) hw
    change ρ b (ρ (b⁻¹*n.val*b) v.val) = ρ b (ρ n.val v.val) at hh
    rw [←Module.End.mul_apply,←map_mul] at hh
    have hg : b * (b⁻¹*n.val*b) = n.val*b := by group
    rw [hg,map_mul,Module.End.mul_apply] at hh
    exact hh.symm
  let F : Subrepresentation (ρ.comp N.subtype) := {
    toSubmodule := S.toSubmodule ⊓ fixedSpace ρ B
    apply_mem_toSubmodule := by
      rintro n v ⟨hv,hvf⟩
      refine ⟨S.apply_mem_toSubmodule n hv,?_⟩
      intro b
      change ρ b.val (ρ n.val v) = ρ n.val v
      rw [hcomm b.val b.property n ⟨v,hv⟩]
      exact congrArg (ρ n.val) (hvf b) }
  have hFS : F ≤ S := fun _ hv => hv.1
  have hFn : F ≠ ⊥ := by
    intro hz
    obtain ⟨v,hv,hv0,hvf⟩ := hfixed
    have hh : v ∈ F := ⟨hv,hvf⟩
    rw [hz] at hh
    exact hv0 hh
  have he : F = S := by
    by_contra hn
    exact hFn (((Subrepresentation.irreducible_iff_isAtom S).mp hS).2 F
      (lt_of_le_of_ne hFS hn))
  have he' := congrArg Subrepresentation.toSubmodule he
  change S.toSubmodule ⊓ fixedSpace ρ B = S.toSubmodule at he'
  have hh : Module.finrank (ZMod 2) S.toSubmodule = 1 := by rw [←he',hSC]; exact hline
  omega

/-- A repeated constituent prevents a starred actor from swapping its two
complete type components. The actor may be presented through any literal
surjective action map; normality is retained in the original group. -/
theorem starred_stabilizes_repeated_pair
    {P : Type*} [Group P] (f : P →* H) (hf : Function.Surjective f)
    (N : Subgroup P) [N.Normal]
    (S R : Subrepresentation ((ρ.comp f).comp N.subtype))
    (hS : IsIrreducible S.toRepresentation) (hd : 1 < Module.finrank (ZMod 2) S.toSubmodule)
    (I J : Submodule (ZMod 2) W) (hcomp : IsCompl I J)
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hSI : S.toSubmodule ≤ I) (hRI : R.toSubmodule ≤ I)
    (hsame : SameModule S R) (hdis : Disjoint S R)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ)
    (hperm : ∀ b ∈ A, I.map (ρ b) = I ∨ I.map (ρ b) = J)
    (hseed : A ⊓ subspaceStabilizer ρ I ≤ subspaceStabilizer ρ S.toSubmodule) :
    A ≤ subspaceStabilizer ρ I := by
  intro a ha
  by_contra hn
  have hm : I.map (ρ a) ≠ I := fun he => hn ((subspace_map_eq_iff ρ I a).mp he)
  have hs : I.map (ρ a) = J := (hperm a ha).resolve_left hm
  have hc : IsCompl I (I.map (ρ a)) := hs.symm ▸ hcomp
  let B := A ⊓ subspaceStabilizer ρ I
  let B' := B.comap f
  have hline := starred_swapping_fixed_finrank_one ρ I hA ha hm hc hdim (by
    intro b hb
    simpa only [hs] using hperm b hb)
  have hfix : fixedSpace (ρ.comp f) B' = fixedSpace ρ B := by
    rw [fixedSpace_comp_map,Subgroup.map_comap_eq_self_of_surjective hf]
  have hBI : B' ≤ subspaceStabilizer (ρ.comp f) I := by
    intro b hb v
    exact hb.2 v
  have hBS : B' ≤ subspaceStabilizer (ρ.comp f) S.toSubmodule := by
    intro b hb v
    exact hseed hb v
  have hSl : Module.finrank (ZMod 2) (I ⊓ fixedSpace (ρ.comp f) B' : Submodule (ZMod 2) W) = 1 := by
    rw [hfix]
    exact hline
  have hSfixed : ∃ v ∈ S, v ≠ 0 ∧ v ∈ fixedSpace (ρ.comp f) B' := by
    let : IsElementaryAbelian 2 A := hA.1.2.1.2
    have hp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left
    have hSn : S.toSubmodule ≠ ⊥ := by
      intro hz
      rw [hz,finrank_bot] at hd
      omega
    obtain ⟨v,hv,hv0,hvf⟩ := PermutedSupports.exists_nonzero_fixed ρ B hp
      S.toSubmodule hSn hseed
    exact ⟨v,hv,hv0,hfix.symm ▸ hvf⟩
  apply no_fixed_line_with_repeated_constituent (ρ.comp f) N B' I S R
    hS hd hSI hRI hsame hdis hBI hBS hSl hSfixed
  intro b hb v hv c
  change ρ (f c.val) (ρ (f b) v-v) = ρ (f b) v-v
  apply sub_eq_zero.mp
  let w := ρ (f c.val) (ρ (f b) v-v) - (ρ (f b) v-v)
  have hv' : ρ (f b) v-v ∈ I := I.sub_mem ((hb.2 v).2 hv) hv
  have hw : w ∈ I := I.sub_mem ((c.property.2 _).2 hv') hv'
  have he : ρ a w = w :=
    sub_eq_zero.mp (hA.1.2.2.1 a ha (f c.val) c.property.1 (f b) hb.1 v)
  exact Submodule.disjoint_def.mp hc.disjoint w hw ⟨w,hw,he⟩

omit [FiniteDimensional (ZMod 2) W] in
/-- Equal full components of simple constituents imply equal module type. -/
theorem sameModule_of_typePart_eq {E : Type*} [Group E]
    {σ : Representation (ZMod 2) E W} (S R : Subrepresentation σ)
    (hS : IsIrreducible S.toRepresentation) (hR : IsIrreducible R.toRepresentation)
    (he : typePart S = typePart R) : SameModule S R := by
  by_contra hn
  have hh := typePart_disjoint hS hR hn
  rw [←he] at hh
  have hz := disjoint_self.mp hh
  exact ((Subrepresentation.irreducible_iff_isAtom S).mp hS).1
    (bot_unique ((le_typePart S).trans hz.le))

omit [FiniteDimensional (ZMod 2) W] in
/-- A proper simple seed inside its full component has a disjoint same-type copy. -/
theorem exists_disjoint_same_in_typePart {E : Type*} [Group E]
    {σ : Representation (ZMod 2) E W} (S : Subrepresentation σ)
    (hS : IsIrreducible S.toRepresentation) (hlt : S < typePart S) :
    ∃ R : Subrepresentation σ, SameModule S R ∧ R ≤ typePart S ∧ Disjoint S R := by
  have hex : ∃ R : {R : Subrepresentation σ // SameModule S R}, ¬ R.val ≤ S := by
    by_contra! hn
    exact hlt.not_ge (iSup_le hn)
  obtain ⟨R,hR⟩ := hex
  refine ⟨R.val,R.property,le_iSup (fun B : {B : Subrepresentation σ // SameModule S B} => B.val) R,?_⟩
  exact ((Subrepresentation.irreducible_iff_isAtom R.val).mp
    (R.property.irreducible hS)).not_le_iff_disjoint.mp hR |>.symm
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
