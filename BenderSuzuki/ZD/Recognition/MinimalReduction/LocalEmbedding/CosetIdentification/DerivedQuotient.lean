module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction
public import BenderSuzuki.SE.Borel
public import BenderSuzuki.SE.Lemma312
public import BenderSuzuki.SE.InvolutionCore
import Mathlib.GroupTheory.IsPerfect

/-!
# The local derived Bender quotient and strong embedding

Let R be the closure of the distinguished involutions inside a centralizer,
and let D be the derived group of the same closure realized in the ambient
group. The structural ZD conclusion places the odd core of R in R'. Since
R' is normal in R, its own odd core is precisely this restricted core.
The first isomorphism theorem therefore identifies R'/O₂′(R') with
(R/O₂′(R))'. Transport to D preserves the core and the specified Borel.

In each actual simple Bender model, the normal Sylow two-subgroup of a
Borel acts regularly on the other cosets. Every involution of the Borel
belongs to that Sylow subgroup, hence fixes no other coset. This proves
strong embedding, which then lifts through the odd kernel.

Source: GLS, Volume 4, Chapter 2, (4E)(3–4), and Chapter 4, Lemma 3.2.
No involution-coset identification, ambient normality of the local closure,
or identification of the specified involution with a structural witness
is used. The model action theorems use actual multiplicative equivalences.
-/

noncomputable section
namespace BenderSuzuki.ZD.LocalDerivedQuotient
open PFAppendixIII PFchapter1section1


/-- Every solvable Sylow two-normalizer in an actual simple Bender model
is strongly embedded, by the regular action of its normal Sylow subgroup. -/
public theorem borel_stronglyEmbedded {G : Type*} [Group G] [Finite G]
    {B : Subgroup G} (hG : IsSimpleBenderGroup G) (hB : IsBorelSubgroup B) :
    IsStronglyEmbedded B := by
  classical
  let : IsSimpleGroup G := hG.isSimple
  obtain ⟨n, hn, hGn⟩ := hG.exists_exponent
  let : Group.IsPerfect G := ⟨hGn.isPerfect hn⟩
  have hproper : B ≠ ⊤ := by
    intro htop
    have : Group.IsSolvable B := hB.1
    have : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := B.subtype) (fun g => ⟨⟨g, by rw [htop]; trivial⟩, rfl⟩)
    exact Group.IsPerfect.not_isSolvable G inferInstance
  obtain ⟨S, hS⟩ := hB.2
  have hSbot : (S : Subgroup G) ≠ ⊥ := by
    intro hb
    apply hproper
    rw [hS, hb]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have htwo : 2 ∣ Nat.card S := by
    rcases S.isPGroup'.card_eq_or_dvd with h | h
    · exact False.elim (hSbot (Subgroup.card_eq_one.mp h))
    · exact h
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  have hsInv : IsInvolution (s : G) := by
    have hs' : orderOf (s : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hs
    exact ⟨(orderOf_eq_prime_iff.mp hs').2, (orderOf_eq_prime_iff.mp hs').1⟩
  refine ⟨hproper, ⟨s, ?_, hsInv⟩, ?_⟩
  · rw [hS]
    exact Subgroup.le_normalizer s.property
  obtain ⟨P, hPn, hregular⟩ := simpleBender_borel_normalSylow_regular hB hG
  let : (P : Subgroup B).Normal := hPn
  let : Unique (Sylow 2 B) := Sylow.unique_of_normal P hPn
  intro g hg x hxB hxg hx
  have hxP : (⟨x, hxB⟩ : B) ∈ (P : Subgroup B) := by
    obtain ⟨T, hT⟩ := (isPGroup_zpowers_of_involution (IsInvolution.subtype hx hxB)).exists_le_sylow
    have hTP : T = P := Subsingleton.elim _ _
    rw [hTP] at hT
    exact hT (Subgroup.mem_zpowers _)
  let R := (P : Subgroup B).map B.subtype
  let xr : R := ⟨x, ⟨⟨x, hxB⟩, hxP, rfl⟩⟩
  have hgq : (QuotientGroup.mk g⁻¹ : G ⧸ B) ≠ QuotientGroup.mk 1 := by
    intro heq
    have hm := QuotientGroup.eq.mp heq
    exact hg (by simpa using hm)
  have hfix : x • (QuotientGroup.mk g⁻¹ : G ⧸ B) = QuotientGroup.mk g⁻¹ := by
    rcases hxg with ⟨y, hy, hyx⟩
    change QuotientGroup.mk (x * g⁻¹) = (QuotientGroup.mk g⁻¹ : G ⧸ B)
    rw [QuotientGroup.eq]
    have heq : (x * g⁻¹)⁻¹ * g⁻¹ = y⁻¹ := by
      have hyx' : g⁻¹ * y * g = x := by simpa [MulAut.conj_apply] using hyx
      rw [← hyx']
      group
    rw [heq]
    exact B.inv_mem hy
  obtain ⟨r, hr, huniq⟩ := hregular hgq hgq
  have heq : xr = 1 := (huniq xr hfix).trans (huniq 1 (by simp)).symm
  exact hx.ne_one (congrArg Subtype.val heq)

/-- Strong embedding lifts through an odd normal subgroup contained in the preimage. -/
private theorem stronglyEmbedded_of_odd_quotient {G : Type*} [Group G] [Finite G]
    (O N : Subgroup G) [O.Normal] (hON : O ≤ N) (hodd : Odd (Nat.card O))
    (hN : IsStronglyEmbedded (N.map (QuotientGroup.mk' O))) : IsStronglyEmbedded N := by
  let q := QuotientGroup.mk' O
  have hker : q.ker ≤ N := by simpa only [q, QuotientGroup.ker_mk'] using hON
  have hcomap : (N.map q).comap q = N := Subgroup.comap_map_eq_self hker
  have htwo : 2 ∣ Nat.card N :=
    (even_iff_two_dvd.mp hN.card_even).trans (Subgroup.card_map_dvd N q)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  have hxInv : IsInvolution (x : G) := by
    have hx' : orderOf (x : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hx
    exact ⟨(orderOf_eq_prime_iff.mp hx').2, (orderOf_eq_prime_iff.mp hx').1⟩
  refine ⟨?_, ⟨x, x.property, hxInv⟩, ?_⟩
  · intro htop
    apply hN.ne_top
    rw [htop, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective O)]
  · intro g hg y hy hyg hyInv
    apply hN.2.2 (g := q g) (x := q y) ?_ ⟨y, hy, rfl⟩ ?_
      (IsInvolution.quotient_mk_of_odd_kernel O hodd hyInv)
    · intro hqg
      exact hg (show g ∈ N from hcomap ▸ hqg)
    · rw [← rightConjugate_map]
      exact ⟨y, hyg, rfl⟩


private theorem core_restrict {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hH : pPrimeCore 2 G ≤ H) :
    pPrimeCore 2 H = (pPrimeCore 2 G).subgroupOf H := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mp
      (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 H)
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    have hc : Nat.card ((pPrimeCore 2 G).subgroupOf H) = Nat.card (pPrimeCore 2 G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
    rw [hc]
    exact pPrimeCore_coprime_card

private theorem derived_equiv {G : Type*} [Group G] [Finite G]
    (hO : pPrimeCore 2 G ≤ commutator G) :
    ∃ e : (commutator G ⧸ pPrimeCore 2 (commutator G)) ≃*
        commutator (G ⧸ pPrimeCore 2 G),
      ∀ d : commutator G,
        (e (QuotientGroup.mk' (pPrimeCore 2 (commutator G)) d) : G ⧸ pPrimeCore 2 G) =
          QuotientGroup.mk' (pPrimeCore 2 G) (d : G) := by
  let O := pPrimeCore 2 G
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  let D := commutator G
  let X := commutator (G ⧸ O)
  have hmap : D.map q = X := by
    simp only [D, X, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective O)]
  let f : D →* X := (q.comp D.subtype).codRestrict X (fun d => by
    rw [← hmap]
    exact ⟨d, d.property, rfl⟩)
  have hf : Function.Surjective f := by
    intro x
    have hx : (x : G ⧸ O) ∈ D.map q := hmap.symm ▸ x.property
    obtain ⟨d, hd, hdx⟩ := hx
    exact ⟨⟨d, hd⟩, Subtype.ext hdx⟩
  have hk : pPrimeCore 2 D = f.ker := by
    rw [core_restrict D hO]
    ext d
    change (d : G) ∈ O ↔ f d = 1
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff (N := O) (d : G)).symm
  let e := (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨e, fun d => ?_⟩
  change ((QuotientGroup.quotientKerEquivOfSurjective f hf)
    (QuotientGroup.quotientMulEquivOfEq hk (QuotientGroup.mk d)) : G ⧸ O) = q d
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem derived_structure {G : Type*} [Group G] [Finite G]
    (M : Subgroup G)
    (hO : pPrimeCore 2 G ≤ M ⊓ commutator G)
    (hmodel : IsSimpleBenderGroup (commutator (G ⧸ pPrimeCore 2 G)))
    (hB : IsBorelSubgroup (((M ⊓ commutator G).map
      (QuotientGroup.mk' (pPrimeCore 2 G))).subgroupOf
        (commutator (G ⧸ pPrimeCore 2 G)))) :
    IsSimpleBenderGroup (commutator G ⧸ pPrimeCore 2 (commutator G)) ∧
    pPrimeCore 2 (commutator G) ≤ M.comap (commutator G).subtype ∧
    IsBorelSubgroup ((M.comap (commutator G).subtype).map
      (QuotientGroup.mk' (pPrimeCore 2 (commutator G)))) := by
  obtain ⟨e, he⟩ := derived_equiv (hO.trans inf_le_right)
  let D := commutator G
  let Q := G ⧸ pPrimeCore 2 G
  let X := commutator Q
  let q := QuotientGroup.mk' (pPrimeCore 2 G)
  let qD := QuotientGroup.mk' (pPrimeCore 2 D)
  let N := M.comap D.subtype
  let B := ((M ⊓ D).map q).subgroupOf X
  have hmap : (N.map qD).map e.toMonoidHom = B := by
    ext x
    constructor
    · rintro ⟨y, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨(d : G), ⟨hd, d.property⟩, (he d).symm⟩
    · rintro ⟨d, ⟨hdM, hdD⟩, hdx⟩
      refine ⟨qD ⟨d, hdD⟩, ⟨⟨d, hdD⟩, hdM, rfl⟩, ?_⟩
      exact Subtype.ext ((he ⟨d, hdD⟩).trans hdx)
  refine ⟨hmodel.map_mulEquiv e.symm, ?_, ?_⟩
  · rw [core_restrict D (hO.trans inf_le_right)]
    intro d hd
    exact (hO hd).1
  · have hb' : IsBorelSubgroup ((N.map qD).map e.toMonoidHom) := hmap.symm ▸ hB
    have hh := hb'.map_mulEquiv e.symm
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact e.symm_apply_apply x
    rw [Subgroup.map_map, hid, Subgroup.map_id] at hh
    exact hh


private theorem quotient_equiv {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) :
    ∃ qe : (A ⧸ pPrimeCore 2 A) ≃* (B ⧸ pPrimeCore 2 B),
      ∀ a : A, qe (QuotientGroup.mk' (pPrimeCore 2 A) a) =
        QuotientGroup.mk' (pPrimeCore 2 B) (e a) := by
  have hO := pPrimeCore_map_iso 2 e
  let : ((pPrimeCore 2 A).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let qe := (quotientMulEquivOfMulEquiv e (pPrimeCore 2 A)).trans
    (QuotientGroup.quotientMulEquivOfEq hO)
  refine ⟨qe, fun a => ?_⟩
  change QuotientGroup.quotientMulEquivOfEq hO
    (quotientMulEquivOfMulEquiv e _ (QuotientGroup.mk a)) = _
  rw [quotientMulEquivOfMulEquiv_mk, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem transport_data {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) (N : Subgroup A) (M : Subgroup B)
    (hNM : ∀ a, e a ∈ M ↔ a ∈ N)
    (hmodel : IsSimpleBenderGroup (A ⧸ pPrimeCore 2 A))
    (hO : pPrimeCore 2 A ≤ N)
    (hB : IsBorelSubgroup (N.map (QuotientGroup.mk' (pPrimeCore 2 A)))) :
    IsSimpleBenderGroup (B ⧸ pPrimeCore 2 B) ∧
    pPrimeCore 2 B ≤ M ∧
    IsBorelSubgroup (M.map (QuotientGroup.mk' (pPrimeCore 2 B))) := by
  obtain ⟨qe, hqe⟩ := quotient_equiv e
  have hmap : N.map e.toMonoidHom = M := by
    ext b
    rw [Subgroup.mem_map_equiv]
    exact (hNM (e.symm b)).symm.trans (by rw [e.apply_symm_apply])
  have hcore : pPrimeCore 2 B ≤ M := by
    rw [← pPrimeCore_map_iso 2 e, ← hmap]
    exact Subgroup.map_mono hO
  have hcomp : qe.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 A)) =
      (QuotientGroup.mk' (pPrimeCore 2 B)).comp e.toMonoidHom := by
    ext a
    exact hqe a
  refine ⟨hmodel.map_mulEquiv qe, hcore, ?_⟩
  have hb := hB.map_mulEquiv qe
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmap] at hb
  exact hb

/-- The relative and ambient realizations of the local derived group agree. -/
private theorem local_derived_equiv
    {G : Type*} [Group G] (Z : Set G) (u : G) :
    let C := Subgroup.centralizer ({u} : Set G)
    let R := Subgroup.closure (C.subtype ⁻¹' Z)
    let L := centralizerClosure Z u
    let D := (commutator L).map L.subtype
    ∃ eD : commutator R ≃* D,
      ∀ d : commutator R, (eD d : G) = (((d : R) : C) : G) := by
  let C := Subgroup.centralizer ({u} : Set G)
  let R := Subgroup.closure (C.subtype ⁻¹' Z)
  let L := centralizerClosure Z u
  let D := (commutator L).map L.subtype
  let eR : R ≃* L := (R.equivMapOfInjective C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr (centralizerClosure_eq_map Z u).symm)
  have hcomm : (commutator R).map eR.toMonoidHom = commutator L := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective eR.toMonoidHom eR.surjective]
  let eD : commutator R ≃* D := ((eR.subgroupMap (commutator R)).trans
    (MulEquiv.subgroupCongr hcomm)).trans
      ((commutator L).equivMapOfInjective L.subtype L.subtype_injective)
  have heD (d : commutator R) : (eD d : G) = ((d : R) : C) := rfl
  exact ⟨eD, heD⟩

/-- The derived quotient and Borel subgroup supplied by local ZD, in the ambient
subgroup convention. No identification of the specified central involution is needed. -/
public theorem local_derived_data
    {G : Type*} [Group G] [Finite G] (Z : Set G) (M : Subgroup G) (u : G)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype)) :
    let L := centralizerClosure Z u
    let D := (commutator L).map L.subtype
    let N := M.comap D.subtype
    let O := pPrimeCore 2 D
    IsSimpleBenderGroup (D ⧸ O) ∧ O ≤ N ∧
      IsBorelSubgroup (N.map (QuotientGroup.mk' O)) ∧ IsStronglyEmbedded N := by
  let C := Subgroup.centralizer ({u} : Set G)
  let R := Subgroup.closure (C.subtype ⁻¹' Z)
  let L := centralizerClosure Z u
  let D := (commutator L).map L.subtype
  let N := M.comap D.subtype
  let MR := (M.comap C.subtype).comap R.subtype
  obtain ⟨eD, heD⟩ := local_derived_equiv Z u
  obtain ⟨_, _, _, _, _, _, _, hmodel, hcore, hborel, _⟩ := hs
  obtain ⟨hmodelD, hcoreD, hborelD⟩ := derived_structure MR hcore hmodel hborel
  have hNM : ∀ d : commutator R,
      eD d ∈ N ↔ d ∈ MR.comap (commutator R).subtype := by
    intro d
    change (eD d : G) ∈ M ↔ (((d : R) : C) : G) ∈ M
    rw [heD]
  obtain ⟨hmodel', hcore', hborel'⟩ := transport_data eD
    (MR.comap (commutator R).subtype) N hNM hmodelD hcoreD hborelD
  exact ⟨hmodel', hcore', hborel',
    stronglyEmbedded_of_odd_quotient (pPrimeCore 2 D) N hcore'
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (borel_stronglyEmbedded hmodel' hborel')⟩

/-- The precise local quotient comparison, including the odd-core equality.
The core restriction is taken inside the relative closure, where its derived
subgroup is normal; no ambient normality of the local closure is asserted. -/
public theorem local_derived_quotient_equiv
    {G : Type*} [Group G] [Finite G] (Z : Set G) (M : Subgroup G) (u : G)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype)) :
    let C := Subgroup.centralizer ({u} : Set G)
    let R := Subgroup.closure (C.subtype ⁻¹' Z)
    let L := centralizerClosure Z u
    let D := (commutator L).map L.subtype
    ∃ eD : commutator R ≃* D,
      (∀ d : commutator R, (eD d : G) = (((d : R) : C) : G)) ∧
      (pPrimeCore 2 D).comap eD.toMonoidHom =
        (pPrimeCore 2 R).subgroupOf (commutator R) ∧
      ∃ eQ : (D ⧸ pPrimeCore 2 D) ≃* commutator (R ⧸ pPrimeCore 2 R),
        ∀ d : commutator R,
          (eQ (QuotientGroup.mk' (pPrimeCore 2 D) (eD d)) : R ⧸ pPrimeCore 2 R) =
            QuotientGroup.mk' (pPrimeCore 2 R) (d : R) := by
  let C := Subgroup.centralizer ({u} : Set G)
  let R := Subgroup.closure (C.subtype ⁻¹' Z)
  let L := centralizerClosure Z u
  let D := (commutator L).map L.subtype
  obtain ⟨eD, heD⟩ := local_derived_equiv Z u
  obtain ⟨_, _, _, _, _, _, _, _, hcore, _, _⟩ := hs
  have hO : pPrimeCore 2 R ≤ commutator R := hcore.trans inf_le_right
  have hrestrict := core_restrict (commutator R) hO
  have htransport : (pPrimeCore 2 D).comap eD.toMonoidHom =
      pPrimeCore 2 (commutator R) := by
    rw [← pPrimeCore_map_iso 2 eD]
    exact Subgroup.comap_map_eq_self_of_injective eD.injective _
  obtain ⟨qe, hqe⟩ := quotient_equiv eD
  obtain ⟨de, hde⟩ := derived_equiv hO
  refine ⟨eD, heD, htransport.trans hrestrict, qe.symm.trans de, fun d => ?_⟩
  change (de (qe.symm (QuotientGroup.mk' (pPrimeCore 2 D) (eD d))) :
    R ⧸ pPrimeCore 2 R) = _
  rw [← hqe d, qe.symm_apply_apply]
  exact hde d
end BenderSuzuki.ZD.LocalDerivedQuotient
