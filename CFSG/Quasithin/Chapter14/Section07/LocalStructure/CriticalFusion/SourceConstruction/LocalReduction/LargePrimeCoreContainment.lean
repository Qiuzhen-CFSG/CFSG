module
public import Theory.GroupAction.ElementaryEightPointResidual.CoverNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeFaithfulCover

/-!
# Full factor normalizers and the first five-residual contradiction

The literal prime-to-five residual of a full star-factor preimage has
nontrivial two-core whenever its star image is nontrivial: otherwise it
centralizes the faithful binary section. Distinct full factor preimages
normalize one another's residuals, retaining the entire original two-core.

A full dihedral factor cannot normalize the selected reflection's common
eight-group. Its actual five-residual would centralize that group, since
GL₃(2) has order prime to five. The reflection's displacement would then
be both in the canonical five-support and in its fixed complement. Coprime
splitting and faithfulness contradict the reflection's order two.

Source: Aschbacher–Smith 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
LargePrimeCoreContainmentSource applies these facts to the original witnesses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
variable {G : Type u} [Group G] [Finite G]

open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter12.Section08 CriticalFusion.Source Representation Representation.BinaryOffender ChapterD
open scoped IsMulCommutative

omit [Finite G] in
/-- A full star preimage with a nontrivial residual image has a nontrivial
intrinsic two-core: otherwise its residual would centralize the faithful module. -/
theorem local_five_residual_core_ne_bot
    {I U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction I U Z) (B : Subgroup (HStar I))
    (hne : actorImage I ((primeToResidual 5
      ((B.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype)).map
      ((B.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype).subtype) ≠ ⊥) :
    let K2 := (B.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    ((primeToResidual 5 K2).map K2.subtype).pCoreIn 2 ≠ ⊥ := by
  let K2 := (B.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
  let K0 := (primeToResidual 5 K2).map K2.subtype
  have hK2I : K2 ≤ I := map_subtype_le _
  have hK0I : K0 ≤ I := (map_subtype_le _).trans hK2I
  have hUcore : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) a.le_local a.normalizes
  have hcoreK2 : I.pCoreIn 2 ≤ K2 := by
    apply map_mono
    intro x hx
    change (x : I ⧸ pCore 2 I) ∈ B
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact B.one_mem
  have hUK0 : U ≤ normalizer (K0 : Set G) :=
    (hUcore.trans hcoreK2).trans (K2.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image K2 (primeToResidual 5 K2)))
  have hcomm : ⁅U,K0⁆ ≤ K0.pCoreIn 2 := by
    apply le_trans (le_inf (le_normalizer_iff_commutator_le_right.mp hUK0) ?_)
      (inf_pCoreIn_le_of_le 2 hK0I)
    exact (le_normalizer_iff_commutator_le_left.mp (hK0I.trans a.normalizes)).trans hUcore
  change K0.pCoreIn 2 ≠ ⊥
  intro hzero
  have hcent : K0 ≤ centralizer (U : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (bot_unique (hcomm.trans hzero.le)))
  apply hne
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨k,hk,rfl⟩
  change QuotientGroup.mk' (pCore 2 I) k = 1
  apply a.faithful
  apply LinearMap.ext
  intro v
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  have hv : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) = v := congrArg Additive.ofMul hu
  rw [←hv,a.conjugation]
  have he : (⟨(k : G) * u * (k : G)⁻¹,
      (a.normalizes k.property u).mp u.property⟩ : U) = u := by
    apply Subtype.ext
    change (k : G) * (u : G) * (k : G)⁻¹ = (u : G)
    have hh : (u : G) * (k : G) = (k : G) * (u : G) := hcent hk u u.property
    rw [←hh,mul_inv_cancel_right]
  rw [he]
  simp only [map_one,Module.End.one_apply]

omit [Finite G] in
/-- Distinct canonical full factor preimages normalize the literal other
five-residual. The complete two-core preimage is retained. -/
theorem local_factor_normalizes_other_five_residual
    {I U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction I U Z) :
    let := BinaryGroupAction.action a.representation
    ∀ (f : CanonicalFiveDihedralFamily (G := HStar I)
        (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
      (i j : smallSupportFactors (HStar I)
        (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2), i ≠ j →
      let K1 := ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
      let K2 := ((f.factor j).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
      K1 ≤ normalizer ((primeToResidual 5 K2).map K2.subtype : Set G) := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro f i j hij
  let q := QuotientGroup.mk' (pCore 2 I)
  let B1 := (f.factor i).comap q
  let B2 := (f.factor j).comap q
  have hn : B1 ≤ normalizer (B2 : Set I) := by
    rw [←comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
    apply comap_mono
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro x hx y hy
    exact (f.commute hij x y hx hy).eq.symm
  have hm : B1.map I.subtype ≤ normalizer (B2.map I.subtype : Set G) :=
    (map_mono hn).trans (B2.le_normalizer_map I.subtype)
  exact hm.trans (normalizer_le_normalizer_characteristic_image
    (B2.map I.subtype) (primeToResidual 5 (B2.map I.subtype)))


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter12.Section08 CriticalFusion.Source Representation Representation.BinaryOffender ChapterD
open Chapter14.Section06.OddNormalizer
open scoped IsMulCommutative
universe u

/-- A full dihedral factor cannot preserve the original reflection's common
eight-group: its five-residual would fix a nonzero part of its moved support. -/
theorem local_factor_not_normalizes_common
    {G : Type u} [Group G] [Finite G] {I U Z : Subgroup G}
    [IsElementaryAbelian 2 U] (a : LocalQuotientAction I U Z) :
    let := BinaryGroupAction.action a.representation
    ∀ (f : CanonicalFiveDihedralFamily (G := HStar I)
        (V := Multiplicative (Additive (U ⧸ Z.subgroupOf U))))
      (i : smallSupportFactors (HStar I)
        (Multiplicative (Additive (U ⧸ Z.subgroupOf U))) 2)
      (A : Subgroup (HStar I)) (C : Subgroup G),
      A ≤ f.factor i → Nat.card A = 2 →
      C = supportPreimage a (subspaceCommutator a.representation ⊤ A) →
      ∀ (_ : IsElementaryAbelian 2 C), Nat.card C = 8 →
      ¬ ((f.factor i).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype ≤
        normalizer (C : Set G) := by
  intro _
  let := BinaryGroupAction.action a.representation
  intro f i A C hAi hAc hC hCE hc hn
  let := hCE
  let W := Additive (U ⧸ Z.subgroupOf U)
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := (f.factor i).comap q
  let K1 := B.map I.subtype
  let K0 := (primeToResidual 5 K1).map K1.subtype
  have hm : actorImage I K0 = (primeToResidual 5 (f.factor i)).map (f.factor i).subtype := by
    have he := map_embedded_primeToResidual_of_hom 5 B I.subtype
    change ((((primeToResidual 5 (B.map I.subtype)).map (B.map I.subtype).subtype).comap
      I.subtype).map q) = _
    rw [←he,comap_map_eq_self_of_injective I.subtype_injective,
      map_embedded_primeToResidual_of_hom 5 B q,
      show B.map q = f.factor i from map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _) _]
  have hPi : i.val ≤ actorImage I K0 := by
    rw [hm]
    intro x hx
    refine ⟨⟨x,f.contains i hx⟩,?_,rfl⟩
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    have hh := orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard (⟨x,hx⟩ : i.val))
    rw [i.property.2.1] at hh
    change x ^ (5 ^ 1) = (1 : HStar I)
    simpa only [pow_one,Subgroup.coe_pow,Subgroup.coe_one] using
      congrArg (fun z : i.val => (z : HStar I)) hh
  let α := C.normalizerMonoidHom.comp (inclusion hn)
  have hk : primeToResidual 5 K1 ≤ α.ker := primeToResidual_le_ker α (by
    rw [card_mulAut_of_elementary_eight C hc]
    decide)
  have hcentral : K0 ≤ centralizer (C : Set G) := by
    rintro x ⟨k,hk0,rfl⟩ c hc0
    have he := congrArg (fun b : MulAut C => (b ⟨c,hc0⟩ : G)) (hk hk0)
    change (k : G) * c * (k : G)⁻¹ = c at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hfix : subspaceCommutator a.representation ⊤ A ≤ fixedSpace a.representation i.val := by
    intro v hv p
    obtain ⟨k,hk0,hkp⟩ := hPi p.property
    change a.representation (p : HStar I) v = v
    rw [←hkp]
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
    have hvu : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) = v := congrArg Additive.ofMul hu
    have huC : (u : G) ∈ C := hC.symm ▸ (mem_supportPreimage a _ u).mpr (hvu.symm ▸ hv)
    rw [←hvu,a.conjugation]
    apply congrArg (fun u => Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u))
    apply Subtype.ext
    change (k : G) * (u : G) * (k : G)⁻¹ = (u : G)
    have hh : (u : G) * (k : G) = (k : G) * (u : G) := hcentral hk0 u huC
    rw [←hh,mul_inv_cancel_right]
  have hs : subspaceCommutator a.representation ⊤ (f.factor i) =
      subspaceCommutator a.representation ⊤ i.val := by
    apply (BinaryGroupAction.submoduleEquivSubgroup (V := W)).injective
    simpa only [←BinaryGroupAction.commutator_eq] using f.support i
  have hmove : subspaceCommutator a.representation ⊤ A ≤
      subspaceCommutator a.representation ⊤ i.val := by
    rw [←hs]
    apply Submodule.span_mono
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact ⟨g,hAi hg,v,hv,rfl⟩
  have hcop : Nat.Coprime (Nat.card i.val) (Nat.card (Multiplicative W)) := by
    rw [i.property.2.1]
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (Multiplicative W)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hsplit := ActionSupport.fixed_support_isCompl (V := Multiplicative W) i.val hcop
  rw [BinaryGroupAction.fixedPoints_eq,BinaryGroupAction.commutator_eq] at hsplit
  have hzero : subspaceCommutator a.representation ⊤ A = ⊥ := by
    apply (BinaryGroupAction.submoduleEquivSubgroup (V := W)).injective
    rw [OrderIso.map_bot]
    exact bot_unique ((le_inf
      (BinaryGroupAction.submoduleEquivSubgroup.monotone hmove)
      (BinaryGroupAction.submoduleEquivSubgroup.monotone hfix)).trans hsplit.disjoint.symm.le_bot)
  have hAbot : A = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    change x = 1
    apply a.faithful
    apply LinearMap.ext
    intro v
    simpa only [map_one,Module.End.one_apply,MonoidHom.comp_apply,Subgroup.coe_subtype] using
      (subspaceCommutator_eq_bot_iff a.representation ⊤ A).mp hzero (Submodule.mem_top : v ∈ ⊤) ⟨x,hx⟩
  rw [hAbot,card_bot] at hAc
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
