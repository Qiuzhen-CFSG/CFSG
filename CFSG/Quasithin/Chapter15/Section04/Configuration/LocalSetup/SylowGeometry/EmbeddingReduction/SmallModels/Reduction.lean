module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Transport
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# Reducing the small-model exclusions to concrete Sylow actions

Let L be normal in the local overgroup H and let T be Sylow two in H.
The Sylow subgroup of L/O₂(L) is the image of T ∩ L. Coprime normalizer
lifting shows that its automizer on the image of P embeds, after transporting
P through the quotient, in the original Aut_T(P). Thus its order divides
|Aut_T(P)|. In particular an induced automizer divisible by sixteen is
incompatible with the actual D₈ automizer of the contrary configuration.

`Restriction Q` states the remaining fixed-carrier calculation: for each
permutable Sylow-two/odd-complement pair, either every two-subgroup of the
extendible pair automizer is reducible, or the Sylow-induced automizer has
order divisible by sixteen. It retains both the elementary order-nine and
extraspecial order-27 complement possibilities. Reducibility contradicts the
transported intrinsic action; the other alternative contradicts divisibility.

Ambient equivalences transport this calculation. The SL₃ and PSL₃ branches
are both retained until coefficient transport and the proved trivial center
of SL₃(3) identify them with the same concrete projective carrier. The two
exclusions at the end are conditional on the fixed PSL₃(3) and M₁₁
calculations; neither calculation is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 1.3.4, printed pp.509–511, and the second paragraph of
15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels
open Chapter1 Chapter1.XiEmbedding Chapter1.XiEmbedding.InvariantThree
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- The two local obstructions used for the small surviving models. -/
def Restriction (Q : Type*) [Group Q] : Prop :=
  ∀ (S : Sylow 2 Q) (R : Subgroup Q), XiOddQuotient 3 R →
    (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q) →
    PairReducible (S : Subgroup Q) R ∨ 16 ∣ Nat.card (automizer (S : Subgroup Q) R)

/-- Coprime normalizer lifting retains the induced two-automizer in the
original complement automizer. -/
theorem quotient_automizer_card_dvd
    {T X P H L : Subgroup G} (h : LocalInput 3 T X P H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hPL : P ≤ L) :
    Nat.card (automizer (quotientImage L T) (quotientImage L P)) ∣
      Nat.card (automizer T P) := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let R := P.subgroupOf L
  let e := complementEquiv h hPL
  let γ := (MulAut.congr e).toMonoidHom
  have hTL : T ≤ normalizer L :=
    (le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS⟩ := component_sylow hT hLH hLn
  have hker : q.ker ≤ T.subgroupOf L := by
    dsimp only [q]
    rw [QuotientGroup.ker_mk', ← hS]
    exact pCore_isPGroup.le_sylow_of_normal S
  have hpre : (quotientImage L T).comap q = T.subgroupOf L :=
    comap_map_eq_self hker
  let _ : Fact (IsPGroup 3 R) := ⟨h.odd_complement.isPGroup.comap_subtype⟩
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    dsimp only [q]
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_dvd_pow
    exact (Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)).of_dvd_right hn
  have hN := normalizer_map_eq_of_coprime_kernel 3 R q
    (QuotientGroup.mk'_surjective _) hcop
  have hle : automizer (quotientImage L T) (quotientImage L P) ≤
      (automizer T P).map γ := by
    rintro a ⟨s, rfl⟩
    have hsN : (s : XiQuotient L) ∈ (normalizer (R : Set L)).map q :=
      hN ▸ s.property.2
    obtain ⟨n, hn, hns⟩ := hsN
    have hnT : (n : G) ∈ T := by
      have hnq : n ∈ (quotientImage L T).comap q := by
        change q n ∈ quotientImage L T
        rw [hns]
        exact s.property.1
      rwa [hpre] at hnq
    have hnP : (n : G) ∈ normalizer P := by
      rw [← subgroupOf_normalizer_eq hPL] at hn
      exact hn
    let t : (T ⊓ normalizer P : Subgroup G) := ⟨n, hnT, hnP⟩
    refine ⟨P.normalizerMonoidHom (inclusion inf_le_right t), ⟨t, rfl⟩, ?_⟩
    apply MulEquiv.ext
    intro r
    apply Subtype.ext
    rw [show γ (P.normalizerMonoidHom (inclusion inf_le_right t)) =
      normalizerAction h hPL t from rfl, normalizerAction_coe h hPL hTL]
    obtain ⟨p, rfl⟩ := e.surjective r
    change quotientAut (pCore 2 L) _ (q _) = _
    rw [quotientAut_apply_mk]
    change q (n * (⟨p, hPL p.property⟩ : L) * n⁻¹) =
      (s : XiQuotient L) * q (⟨p, hPL p.property⟩ : L) * (s : XiQuotient L)⁻¹
    rw [map_mul, map_mul, map_inv, hns]
  have hd := card_dvd_of_le hle
  rwa [card_map_of_injective (MulAut.congr e).injective] at hd

omit [Finite G] in
/-- An ambient equivalence transports each induced conjugation action. -/
theorem automizer_map_le {Q : Type v} [Group Q] (e : G ≃* Q) (T P : Subgroup G) :
    (automizer T P).map (MulAut.congr (e.subgroupMap P)).toMonoidHom ≤
      automizer (T.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  rintro a ⟨b, ⟨t, rfl⟩, rfl⟩
  let t' : (T.map e.toMonoidHom ⊓ normalizer (P.map e.toMonoidHom) : Subgroup Q) :=
    ⟨e t, ⟨t, t.property.1, rfl⟩,
      P.le_normalizer_map e.toMonoidHom ⟨t, t.property.2, rfl⟩⟩
  refine ⟨t', ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := (e.subgroupMap P).surjective x
  apply Subtype.ext
  change e t * e (p : G) * (e t)⁻¹ =
    (e.subgroupMap P) (P.normalizerMonoidHom (inclusion inf_le_right t)
      ((e.subgroupMap P).symm ((e.subgroupMap P) p)))
  rw [MulEquiv.symm_apply_apply]
  change e t * e (p : G) * (e t)⁻¹ = e ((t : G) * p * (t : G)⁻¹)
  simp only [map_mul, map_inv]

omit [Finite G] in
private theorem automizer_card_dvd_map {Q : Type v} [Group Q] [Finite Q]
    (e : G ≃* Q) (T P : Subgroup G) :
    Nat.card (automizer T P) ∣
      Nat.card (automizer (T.map e.toMonoidHom) (P.map e.toMonoidHom)) := by
  calc
    Nat.card (automizer T P) =
        Nat.card ((automizer T P).map (MulAut.congr (e.subgroupMap P)).toMonoidHom) :=
      (card_map_of_injective (MulAut.congr (e.subgroupMap P)).injective).symm
    _ ∣ _ := card_dvd_of_le (automizer_map_le e T P)

/-- The order of an induced automizer is preserved by an ambient equivalence. -/
theorem automizer_card_map {Q : Type v} [Group Q] [Finite Q]
    (e : G ≃* Q) (T P : Subgroup G) :
    Nat.card (automizer (T.map e.toMonoidHom) (P.map e.toMonoidHom)) =
      Nat.card (automizer T P) := by
  have hd := automizer_card_dvd_map e T P
  have hr := automizer_card_dvd_map e.symm (T.map e.toMonoidHom) (P.map e.toMonoidHom)
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.symm_apply_apply
  have hT : (T.map e.toMonoidHom).map e.symm.toMonoidHom = T := by
    rw [map_map, he, map_id]
  have hP : (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
    rw [map_map, he, map_id]
  have hcard := congrArg₂ (fun A B : Subgroup G => Nat.card (automizer A B)) hT hP
  exact Nat.dvd_antisymm (hr.trans (by rw [hcard])) hd

/-- The fixed-carrier calculation also applies to every isomorphic copy. -/
theorem restriction_of_equiv {Q : Type v} [Group Q] [Finite Q]
    (e : G ≃* Q) (hc : Restriction Q) : Restriction G := by
  intro S R hR hperm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hperm' : (R.map e.toMonoidHom : Set Q) * (S' : Set Q) =
      (S' : Set Q) * (R.map e.toMonoidHom : Set Q) := by
    have hh := congrArg (Set.image e) hperm
    change (e '' (R : Set G)) * (e '' (S : Set G)) =
      (e '' (S : Set G)) * (e '' (R : Set G))
    simpa only [Set.image_mul] using hh
  rcases hc S' (R.map e.toMonoidHom)
      (hR.of_mulEquiv (e.subgroupMap R)) hperm' with hred | hd
  · exact Or.inl (SporadicActions.pairReducible_of_map e S R hred)
  · right
    rwa [show (S' : Subgroup Q) = (S : Subgroup G).map e.toMonoidHom from rfl,
      automizer_card_map] at hd

/-- A sixteen-divisibility calculation contradicts the actual D₈ automizer;
the alternative reducibility calculation contradicts the intrinsic action. -/
theorem not_restriction_of_dihedral
    {T X P H L : Subgroup G} (h : LocalInput 3 T X P H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hPL : P ≤ L) (hD : Nonempty (automizer T P ≃* DihedralGroup 4)) :
    ¬ Restriction (XiQuotient L) := by
  intro hc
  obtain ⟨S, hS⟩ := component_quotient_sylow hT hLH hLn
  have hp := component_quotient_permute h hPL
  rw [← hS] at hp
  rcases hc S (quotientImage L P)
      (h.odd_complement.of_mulEquiv (complementEquiv h hPL)) hp with hred | hd
  · rw [hS] at hred
    exact not_pairReducible h hPL
      ((le_sup_right.trans h.overgroup).trans
        ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)) hred
  · rw [hS] at hd
    have hd' := hd.trans (quotient_automizer_card_dvd h hT hLH hLn hPL)
    obtain ⟨e⟩ := hD
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hd'
    norm_num at hd'

omit [Finite G] in
/-- Both source covers give the same actual PSL₃(3) carrier, using the
proved trivial center over the three-element field. -/
theorem equiv_pslThree_of_linearThreeModel
    (hm : LinearThreeModel 3 G) : Nonempty (G ≃* Matrix.PSL3Three.PSL) := by
  rcases hm with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · let _ : Fintype F := Fintype.ofFinite F
    let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ⟨e.trans ((Matrix.SpecialLinearGroup.ringEquiv eF.symm).trans
      Matrix.PSL3Three.equiv)⟩
  · let _ : Fintype F := Fintype.ofFinite F
    let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF.symm)⟩

/-- Conditional linear-three exclusion. The only remaining input is the
fixed PSL₃(3) Sylow-pair calculation. -/
theorem not_linearThreeModel_of_restriction
    (hc : Restriction Matrix.PSL3Three.PSL)
    {T X P H L : Subgroup G} (h : LocalInput 3 T X P H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hXL : X ≤ L) (hD : Nonempty (automizer T P ≃* DihedralGroup 4)) :
    ¬ LinearThreeModel 3 (XiQuotient L) := by
  intro hm
  obtain ⟨e⟩ := equiv_pslThree_of_linearThreeModel hm
  exact not_restriction_of_dihedral h hT hLH hLn
    ((le_sup_right.trans h.complement.le).trans hXL) hD
    (restriction_of_equiv e hc)

/-- Conditional M₁₁ exclusion. The only remaining input is the fixed
Mathieu carrier's Sylow-pair calculation. -/
theorem not_mathieuEleven_of_restriction
    (hc : Restriction Sporadic.Mathieu.M11)
    {T X P H L : Subgroup G} (h : LocalInput 3 T X P H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hXL : X ≤ L) (hD : Nonempty (automizer T P ≃* DihedralGroup 4)) :
    ¬ Nonempty (XiQuotient L ≃* Sporadic.Mathieu.M11) := by
  rintro ⟨e⟩
  exact not_restriction_of_dihedral h hT hLH hLn
    ((le_sup_right.trans h.complement.le).trans hXL) hD
    (restriction_of_equiv e hc)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels
