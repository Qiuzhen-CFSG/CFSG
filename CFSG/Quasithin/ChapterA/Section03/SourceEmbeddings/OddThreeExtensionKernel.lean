module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCentralizers

/-!
# Constructing the elementary kernel in the odd ternary source branch

The local join has zero two-core. A.3.6 supplies the primary core shapes;
the involution-centralizer theorem identifies the quotient prime with the
ternary defining prime. Its natural-action clause then gives actual two
coordinates over that prime field, rather than only a Fitting-core identity.

Source: Aschbacher--Smith A.3.6 and A.3.21, printed pp.43--45,55--56.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

theorem extension_of_defining_quotient
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : B.IsCComponent)
    (hn : ¬ fittingSubgroup B ≤ center B)
    {q : ℕ} [Fact q.Prime] (hq : 3 < q)
    (hF : fittingSubgroup B = pCore q B)
    (e : (B ⧸ fittingSubgroup B) ≃* SL(2,ZMod q)) :
    ElementaryModel q 2 (fittingSubgroup B) ∧
      HasExtension B (ElementaryModel q 2) (fun X _ => IsSL X 2 q) := by
  have hquot : NoncentralFitting.PrimeSL2FittingQuotient B :=
    ⟨q,Fact.out,hq,⟨e⟩⟩
  have hd : q ∣ Nat.card (fittingSubgroup B) := by
    have hne : Nat.card (pCore q B) ≠ 1 := by
      intro he
      exact hn (by rw [hF,(eq_bot_iff_card _).mpr he]; exact bot_le)
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := q) (G := B)).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro he
      apply hne
      rw [hn,he,pow_zero]
    rw [hF,hn]
    exact dvd_pow_self q hn0
  have hs := NoncentralFitting.CoreShapes.PrimaryShapes.primary_shapes
    RankActions.primeSL2CoverRigidity hG hO hB hquot q hd
  have ha := NoncentralFitting.CoreShapes.DefiningPrime.natural_action_of_shape
    hG hB hn hq e hF hs
  obtain ⟨F,_,_,hcard,v,ρ,_⟩ := ha
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hcard,ZMod.card])
  have hel : ElementaryModel q 2 (fittingSubgroup B) :=
    ⟨(MulEquiv.subgroupCongr (NoncentralFitting.generalizedFitting_eq_fitting hB hn)).symm.trans
      (v.trans (AddEquiv.piCongrRight (fun _ : Fin 2 => a.toAddEquiv)).toMultiplicative)⟩
  exact ⟨hel, fittingSubgroup B,inferInstance,hel,
    ⟨ZMod q,inferInstance,inferInstance,Nat.card_zmod q,⟨e⟩⟩⟩

theorem rankThree_local_extension
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    {κ : GroupClass} (hA : IsSQTK κ A)
    {q residue : ℕ} [Fact q.Prime] (ho : Odd q)
    (hR : RankThreeLocalStructure H q residue) (f : A →* H) (hf : Function.Injective f)
    (S : Sylow 2 A) {B : Subgroup A} (hB : B ∈ localCComponents S)
    (hnS : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hn : ¬ IsQuasisimple (B ⧸ pCore 2 B))
    (unitary : Bool)
    (hm : IsPSLSign A unitary 3 q ∨ IsSLSign A unitary 3 q) :
    3 < q ∧ ElementaryModel q 2 (fittingSubgroup B) ∧
      HasExtension B (ElementaryModel q 2) (fun X _ => IsSL X 2 q) := by
  have hnB : ¬ IsQuasisimple B := by
    intro hq
    let := hq
    have htop : (⊤ : Subgroup B).IsCComponent := by
      simpa only [subgroupOf_self] using
        hB.subgroupOf_of_le (show B ≤ B from le_rfl) (show B ≤ B ⊔ S from le_sup_left)
    let := pCore_isNilpotent (p := 2) (G := B)
    have hbar := htop.map_quotient (pCore 2 B)
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 B))] at hbar
    let : Nontrivial (⊤ : Subgroup (B ⧸ pCore 2 B)) :=
      (nontrivial_iff_ne_bot _).mpr hbar.ne_bot
    let : Nontrivial (B ⧸ pCore 2 B) := (topEquiv (G := B ⧸ pCore 2 B)).injective.nontrivial
    exact hn (IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective (pCore 2 B)))
  let J := B ⊔ (S : Subgroup A)
  let D := B.subgroupOf J
  let e : D ≃* B := subgroupOfEquivOfLe le_sup_left
  have hnc : ¬ fittingSubgroup D ≤ center D := by
    intro hh
    have hr : solvableRadical D = center D := by
      apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hh)
      exact le_solvableRadical (center D) inferInstance
        (Group.isSolvable_of_comm (fun a b => Subtype.ext
          (mem_center_iff.mp a.property b).symm))
    let := hB.perfect
    let := hB.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple D := ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact hnB (IsQuasisimple.of_mulEquiv e)
  obtain ⟨hO,hF⟩ := rankThree_local_core_and_fitting hA ho hR f hf S hB hn
  have hquotD := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity (hA.subgroup J) hO hB hnc
  let eQ : (D ⧸ fittingSubgroup D) ≃* (B ⧸ fittingSubgroup B) :=
    QuotientGroup.congr _ _ e (map_fitting_equiv e)
  have hquotB : NoncentralFitting.PrimeSL2FittingQuotient B := by
    obtain ⟨r,hr,hr3,⟨er⟩⟩ := hquotD
    exact ⟨r,hr,hr3,⟨eQ.symm.trans er⟩⟩
  obtain ⟨hq,⟨eB⟩⟩ := odd_three_fitting_quotient ho hR f hf S B hnS hF hquotB unitary hm
  have hFD : fittingSubgroup D = pCore q D := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [map_fitting_equiv e,pCore_map_iso q e,hF]
  obtain ⟨helD,_⟩ := extension_of_defining_quotient (hA.subgroup J) hO hB hnc hq hFD (eQ.trans eB)
  let eF : fittingSubgroup D ≃* fittingSubgroup B :=
    ((fittingSubgroup D).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_fitting_equiv e))
  have helB : ElementaryModel q 2 (fittingSubgroup B) := ⟨eF.symm.trans helD.some⟩
  exact ⟨hq,helB,fittingSubgroup B,inferInstance,helB,
    ⟨ZMod q,inferInstance,inferInstance,Nat.card_zmod q,⟨eB⟩⟩⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
