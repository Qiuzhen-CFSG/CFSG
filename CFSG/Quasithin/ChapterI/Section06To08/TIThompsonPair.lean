module
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugateSpan
public import Stellmacher.ElementaryAbelianMaxPair.Intermediate
public import Stellmacher.ElementaryAbelianMaxPair.Normalizers

/-!
# A TI conjugate span in a two-factor Thompson subgroup

Suppose the elementary Thompson subgroup of a Sylow two-subgroup has two
maximum elementary factors. A conjugate of a TI subgroup through an
external involution cannot generate a maximum elementary span whose product
with the involution commutator group is a conjugate Thompson subgroup.
Point coverage puts the full conjugate span inside that subgroup; the
intermediate-subgroup argument then forces normalization, and weak closure
gives the contradiction.

Source: Aschbacher–Smith, original 2.4.21, printed p.536.
-/

public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem pair_family_maxJ (T U W : Subgroup G)
    (hpair : elementaryAbelianMaxSubgroups T = {U,W}) :
    elementaryAbelianMaxSubgroups (elementaryAbelianMaxJ T) = {U,W} ∧
      U ⊔ W = elementaryAbelianMaxJ T := by
  have hgen : U ⊔ W = elementaryAbelianMaxJ T := by
    change _ = sSup (elementaryAbelianMaxSubgroups T)
    rw [hpair,sSup_insert,sSup_singleton]
  have hRT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hA => hA.1
  have hU : U ∈ elementaryAbelianMaxSubgroups T := by rw [hpair]; exact Set.mem_insert _ _
  refine ⟨?_,hgen⟩
  ext A
  constructor
  · intro hA
    have hAT : A ∈ elementaryAbelianMaxSubgroups T :=
      ⟨hA.1.trans hRT,hA.2.1,fun B hBT hB =>
        (hU.2.2 B hBT hB).trans (hA.2.2 U (hgen ▸ le_sup_left) hU.2.1)⟩
    rwa [hpair] at hAT
  · intro hA
    have hAT : A ∈ elementaryAbelianMaxSubgroups T := hpair ▸ hA
    exact ⟨le_sSup hAT,hAT.2.1,fun B hBR hB => hAT.2.2 B (hBR.trans hRT) hB⟩

omit [Finite G] in
private theorem conjugate_cover_transport (Z R : Subgroup G)
    (hcover : ∀ r∈R, r^2=1 → r≠1 →
      ∃ k : G, Z.conjBy k ≤ R ∧ r∈Z.conjBy k) (h : G) :
    ∀ r∈R.conjBy h, r^2=1 → r≠1 →
      ∃ k : G, Z.conjBy k ≤ R.conjBy h ∧ r∈Z.conjBy k := by
  rintro r ⟨b,hb,rfl⟩ hb2 hb1
  have hb2' : b^2=1 := by
    apply (MulAut.conj h).injective
    simpa only [map_pow,map_one,MulEquiv.coe_toMonoidHom] using hb2
  have hb1' : b≠1 := by intro he; apply hb1; rw [he,map_one]
  obtain ⟨k,hk,hbk⟩ := hcover b hb hb2' hb1'
  refine ⟨h*k,?_,?_⟩
  · rw [conjBy_mul]
    exact map_mono hk
  · rw [conjBy_mul]
    exact ⟨b,hbk,rfl⟩

/-- The TI conjugate span forces a conjugate elementary Thompson subgroup
back to the original one. This is the last contradiction in the central
involution branch of original 2.4.21. -/
theorem IsTISubgroup.not_conjugate_product_of_maxJ_pair
    (T : Sylow 2 G) (U W Z V : Subgroup G) (a g h : G)
    (hpair : elementaryAbelianMaxSubgroups (T : Subgroup G) = {U,W})
    (hTI : IsTISubgroup Z)
    (ha : a∈Z.conjBy g) (ha1 : a≠1) (ha2 : a^2=1)
    (hout : a∉elementaryAbelianMaxJ (T : Subgroup G))
    (hcover : ∀ r∈elementaryAbelianMaxJ (T : Subgroup G), r^2=1 → r≠1 →
      ∃ k : G, Z.conjBy k ≤ elementaryAbelianMaxJ (T : Subgroup G) ∧ r∈Z.conjBy k)
    (hK : ⁅elementaryAbelianMaxJ (T : Subgroup G),zpowers a⁆ ≤
      elementaryAbelianMaxJ (T : Subgroup G))
    (hVmax : V∈elementaryAbelianMaxSubgroups (⊤ : Subgroup G))
    (hspan : V=conjugateSpanBy (Z.conjBy g)
      ⁅elementaryAbelianMaxJ (T : Subgroup G),zpowers a⁆)
    (hprod : ⁅elementaryAbelianMaxJ (T : Subgroup G),zpowers a⁆ ⊔ V =
      (elementaryAbelianMaxJ (T : Subgroup G)).conjBy h) : False := by
  let R := elementaryAbelianMaxJ (T : Subgroup G)
  let K := ⁅R,zpowers a⁆
  let E := Z.conjBy g
  let P := R.conjBy h
  let X := conjugateSpanBy E R
  have hEV : E≤V := by rw [hspan]; exact le_conjugateSpanBy _ _
  have haV : a∈V := hEV ha
  have hVP : V≤P := by
    change V≤R.conjBy h
    rw [←hprod]
    exact le_sup_right
  have haP : a∈P := hVP haV
  have hEP (r : G) (hr : r∈R) : E.conjBy r≤P := by
    have hraP : r*a*r⁻¹∈P := by
      have hc : ⁅r,a⁆∈K := commutator_mem_commutator hr (mem_zpowers a)
      have hmul : ⁅r,a⁆*a∈P := P.mul_mem ((hprod ▸ le_sup_left) hc) haP
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hmul
    have hra2 : (r*a*r⁻¹)^2=1 := by
      simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj r) ha2
    have hra1 : r*a*r⁻¹≠1 := by
      intro he
      apply ha1
      exact (MulAut.conj r).map_eq_one_iff.mp he
    obtain ⟨k,hk,hra⟩ := conjugate_cover_transport Z R hcover h _ hraP hra2 hra1
    have heq := hTI.conjugate_eq_of_common_point (r*g) k (r*a*r⁻¹) hra1 (by
      change r*a*r⁻¹∈Z.conjBy (r*g)
      rw [conjBy_mul]
      exact ⟨a,ha,rfl⟩) hra
    change Z.conjBy (r*g)=Z.conjBy k at heq
    change (Z.conjBy g).conjBy r ≤ P
    rw [←conjBy_mul,heq]
    exact hk
  have hXP : X≤P := by
    apply (closure_le _).mpr
    rintro b ⟨r,hr,z,hz,rfl⟩
    exact hEP r hr ⟨z,hz,rfl⟩
  have hVX : V≤X := by
    rw [hspan]
    exact conjugateSpanBy_mono le_rfl hK
  have hRX : R≤normalizer (X : Set G) := le_normalizer_conjugateSpanBy E R
  obtain ⟨hpairR,hgen⟩ := pair_family_maxJ (T : Subgroup G) U W hpair
  have hpairP : elementaryAbelianMaxSubgroups P={U.conjBy h,W.conjBy h} :=
    maxFamily_pair_map (MulAut.conj h).toMonoidHom (MulAut.conj h).injective R U W hpairR
  have hgenP : U.conjBy h ⊔ W.conjBy h=P := by
    change U.map _ ⊔ W.map _ = R.map _
    rw [←Subgroup.map_sup,hgen]
  have hVin : V∈elementaryAbelianMaxSubgroups P :=
    ⟨hVP,hVmax.2.1,fun B _ hB => hVmax.2.2 B le_top hB⟩
  rw [hpairP,Set.mem_insert_iff,Set.mem_singleton_iff] at hVin
  have hRK : R≤normalizer (K : Set G) := normalizer_commutator_ge_left R (zpowers a)
  have hRP : R≤normalizer (P : Set G) := by
    rcases hVin with hV | hV
    · apply normalizes_pair_of_normalizes_intermediate P V (W.conjBy h) X K R
        (by rwa [←hV] at hpairP) (by rwa [←hV] at hgenP) hVX hXP hRX hRK hprod
    · apply normalizes_pair_of_normalizes_intermediate P V (U.conjBy h) X K R
        (by simpa only [hV,Set.pair_comm] using hpairP)
        (by simpa only [hV,sup_comm] using hgenP) hVX hXP hRX hRK hprod
  have he := maxJ_conjugate_eq_of_normalizes T h hRP
  exact hout (he ▸ haP)
end CFSG.Quasithin.ChapterI.Section06To08
