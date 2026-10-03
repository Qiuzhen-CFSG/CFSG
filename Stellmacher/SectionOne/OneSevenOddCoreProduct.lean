module
public import Stellmacher.SectionOne.SL2ProductFactorNormalizer
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Theory.GroupTheory.CenterlessProduct
public import Mathlib.GroupTheory.Commutator.Finite

/-!
# The odd core of a product of the (1.7) factors

For an internal product E of the refined SL₂(2) factors, the odd core of
the ambient group splits as E' times its centralizer in the odd core.
These factors are normalized by the odd core by definition.

Each factor is centerless, so E meets its centralizer trivially. Factorwise
innerness writes an odd-core element as e c with e in E and c centralizing E.
The order of e is odd, whereas E/E' has exponent two, so e lies in E'.
Finally E' lies in the odd core, since every factor's derived subgroup does.
This gives the two commuting, disjoint factors required in (1.7)(a).
Every square in E lies in its derived subgroup and hence in the odd core;
the final theorem records that E has two-group image modulo that odd core,
as needed to transport the transvection-generated product in (9.3).
The centerless product/centralizer intersection is public for the Sylow
normal-closure argument used after (9.4)(5).

Source: Stellmacher (1.7), Journal of Algebra 190 (1997), p.19,
`refs/latex/stellmacher-n-group.tex`. The proof needs only the stated factor
properties, not the full faithful-action hypotheses of Section 1.
-/

namespace Stellmacher.SectionOne
universe u

private theorem product_disjoint_centralizer
    {G : Type u} [Group G] [Finite G]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hSL : ∀ D ∈ F, IsSL2Two D) :
    Disjoint E (Subgroup.centralizer (E : Set G)) := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let P := ∀ i : I, (i : Subgroup G)
  have hcomm : Pairwise (fun i j : I => ∀ x y : G,
      x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2.2 i i.property j j.property
      (fun heq => hij (Subtype.ext heq)) x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E := (Subgroup.noncommPiCoprod_range).trans hprod.1.symm
  have hcenter (i : I) : Subgroup.center (i : Subgroup G) = ⊥ :=
    RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two (hSL i i.property)
  have hinj : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (Subgroup.iSupIndep_of_centerless_of_pairwise_commute (fun i : I => (i : Subgroup G))
      hcenter hcomm)
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨p,hpx⟩ := show x ∈ f.range from hf ▸ hx.1
  have hpone : p = 1 := by
    funext i
    have hpcenter : p i ∈ Subgroup.center (i : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro y
      let q : P := Pi.mulSingle i y
      have hqE : f q ∈ E := hf ▸ (show f q ∈ f.range from ⟨q, rfl⟩)
      have hc : f q * f p = f p * f q := by
        rw [hpx]
        exact Subgroup.mem_centralizer_iff.mp hx.2 (f q) hqE
      have hpq : q*p=p*q := hinj (by simpa using hc)
      have hi := congrArg (fun z : P => z i) hpq
      change q i * p i = p i * q i at hi
      simpa [q] using hi
    rw [hcenter i] at hpcenter
    exact hpcenter
  change x = 1
  rw [← hpx,hpone,map_one]

/-- An internal SL₂(2) product meets its ambient centralizer trivially. -/
public theorem sl2_product_disjoint_centralizer
    {G : Type u} [Group G] [Finite G]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hSL : ∀ D ∈ F, IsSL2Two D) :
    Disjoint E (Subgroup.centralizer (E : Set G)) :=
  product_disjoint_centralizer E F hprod hSL

private theorem factor_square_mem_derived
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (d : D) :
    d ^ 2 ∈ commutator D := by
  have hcardC : Nat.card (commutator D) = 3 := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    exact hD.2.1.2.1
  have hcardQ : Nat.card (D ⧸ commutator D) = 2 := by
    have hh := (commutator D).index_mul_card
    rw [Subgroup.index_eq_card, hcardC, RankOneThreeGroupAssembly.isSL2Two_card hD.1] at hh
    omega
  have hp := pow_card_eq_one' (x := QuotientGroup.mk' (commutator D) d)
  rw [hcardQ, ← map_pow] at hp
  exact (QuotientGroup.eq_one_iff _).mp hp

private theorem derived_and_square_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    (commutator E).map E.subtype ≤ oddCore G ∧
      ∀ e : E, (e : G) ^ 2 ∈ (commutator E).map E.subtype := by
  classical
  let I := {D : Subgroup G // D ∈ F}
  let P := ∀ i : I, (i : Subgroup G)
  let R := (commutator E).map E.subtype
  have hcomm : Pairwise (fun i j : I => ∀ x y : G,
      x ∈ (i : Subgroup G) → y ∈ (j : Subgroup G) → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2.2 i i.property j j.property
      (fun heq => hij (Subtype.ext heq)) x hx y hy
  let f : P →* G := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E := (Subgroup.noncommPiCoprod_range).trans hprod.1.symm
  have hmap : (commutator P).map f = R := by
    dsimp only [R]
    rw [map_commutator_eq, hf, Subgroup.map_subtype_commutator]
  have hiE (i : I) : (i : Subgroup G) ≤ E := by
    rw [hprod.1]
    exact le_iSup (fun j : I => (j : Subgroup G)) i
  constructor
  · change R ≤ oddCore G
    rw [← hmap]
    rintro x ⟨p, hp, rfl⟩
    change f p ∈ oddCore G
    rw [Subgroup.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro i _
    have hpi : p i ∈ commutator (i : Subgroup G) := by
      have hm := Subgroup.mem_map_of_mem
        (Pi.evalMonoidHom (fun i : I => (i : Subgroup G)) i) hp
      rw [map_commutator_eq] at hm
      exact Subgroup.commutator_mono le_top le_top hm
    exact (hF i i.property).2.1.1 (Subgroup.mem_map_of_mem (i : Subgroup G).subtype hpi)
  · intro e
    obtain ⟨p, hp⟩ := show (e : G) ∈ f.range from hf ▸ e.property
    rw [← hp, ← map_pow]
    change f (p ^ 2) ∈ R
    rw [Subgroup.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro i _
    have hpi := factor_square_mem_derived (i : Subgroup G) (hF i i.property) (p i)
    have hle : (commutator (i : Subgroup G)).map (i : Subgroup G).subtype ≤ R := by
      dsimp only [R]
      rw [Subgroup.map_subtype_commutator, Subgroup.map_subtype_commutator]
      exact Subgroup.commutator_mono (hiE i) (hiE i)
    exact hle (Subgroup.mem_map_of_mem (i : Subgroup G).subtype hpi)

public theorem oneSevenFactor_oddCore_product
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    IsInternalDirectProductFamily (oddCore G)
      (fun i : Fin 2 => if i = 0 then (commutator E).map E.subtype
        else oddCore G ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  let R := (commutator E).map E.subtype
  let C := Subgroup.centralizer (E : Set G)
  obtain ⟨hRW, hsquare⟩ := derived_and_square_data E F hprod hF
  have hRE : R ≤ E := Subgroup.map_subtype_le _
  have hdis : Disjoint E C := product_disjoint_centralizer E F hprod
    (fun D hD => (hF D hD).1)
  have hsup : oddCore G = R ⊔ (oddCore G ⊓ C) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨e, hec⟩ := sl2_product_normalizer_exists_inner E F hprod
        (fun D hD => (hF D hD).1) w (fun D hD =>
          ((show oddCore G ≤ oddCore G ⊔ D from le_sup_left).trans
            ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp
              (hF D hD).2.2.2)) hw)
      let c := (e : G)⁻¹ * w
      have hc : c ∈ C := hec
      have heccomm : Commute (e : G) c :=
        Subgroup.mem_centralizer_iff.mp hc e e.property
      have hwprod : w = (e : G) * c := by simp [c]
      let n := Nat.card (oddCore G)
      have hwn : w ^ n = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨w,hw⟩ : oddCore G)))
      have hmul : (e : G)^n * c^n = 1 := by
        rw [← heccomm.mul_pow, ← hwprod]
        exact hwn
      have hen : (e : G)^n = 1 :=
        (Subgroup.disjoint_iff_mul_eq_one.mp hdis (E.pow_mem e.property n)
          (C.pow_mem hc n) hmul).1
      let q := QuotientGroup.mk' (commutator E)
      have hq2 : (q e)^2 = 1 := by
        rw [← map_pow]
        apply (QuotientGroup.eq_one_iff _).mpr
        obtain ⟨d, hd, heq⟩ := hsquare e
        have hde : d = e^2 := Subtype.ext heq
        exact hde ▸ hd
      have hqn : (q e)^n = 1 := by
        rw [← map_pow, show e^n = 1 from Subtype.ext hen, map_one]
      have hqone : q e = 1 := by
        apply orderOf_eq_one_iff.mp
        apply Nat.eq_one_of_dvd_one
        have hcop : Nat.Coprime 2 n := pPrimeCore_coprime_card (p := 2) (G := G)
        simpa only [hcop.gcd_eq_one] using
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq2) (orderOf_dvd_of_pow_eq_one hqn)
      have heR : (e : G) ∈ R :=
        Subgroup.mem_map_of_mem E.subtype ((QuotientGroup.eq_one_iff _).mp hqone)
      have hcW : c ∈ oddCore G := (oddCore G).mul_mem
        ((oddCore G).inv_mem (hRW heR)) hw
      rw [hwprod]
      exact (R ⊔ (oddCore G ⊓ C)).mul_mem
        ((show R ≤ R ⊔ (oddCore G ⊓ C) from le_sup_left) heR)
        ((show oddCore G ⊓ C ≤ R ⊔ (oddCore G ⊓ C) from le_sup_right) ⟨hcW,hc⟩)
    · exact sup_le hRW inf_le_left
  refine ⟨?_, ?_, ?_⟩
  · apply hsup.trans
    apply le_antisymm
    · apply sup_le
      · simpa using (le_iSup (fun i : Fin 2 => if i = 0 then R else oddCore G ⊓ C) 0)
      · simpa using (le_iSup (fun i : Fin 2 => if i = 0 then R else oddCore G ⊓ C) 1)
    · apply iSup_le
      intro i
      dsimp only
      by_cases hi : i = 0
      · simp only [hi, ↓reduceIte]
        exact le_sup_left
      · simp only [hi, ↓reduceIte]
        exact le_sup_right
  · intro i j hij
    have hd : Disjoint R (oddCore G ⊓ C) := hdis.mono hRE inf_le_right
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa only [Fin.zero_eta, Fin.mk_one, ↓reduceIte, one_ne_zero] using hd
    · simpa only [Fin.zero_eta, Fin.mk_one, ↓reduceIte, one_ne_zero] using hd.symm
    · exact (hij rfl).elim
  · intro i j hij a ha b hb
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a ∈ R at ha
      have hb' : b ∈ oddCore G ⊓ C := by simpa using hb
      exact Subgroup.mem_centralizer_iff.mp hb'.2 a (hRE ha)
    · change b ∈ R at hb
      have ha' : a ∈ oddCore G ⊓ C := by simpa using ha
      exact (Subgroup.mem_centralizer_iff.mp ha'.2 b (hRE hb)).symm
    · exact (hij rfl).elim

/-- The product of the one-seven factors has two-group image modulo the odd core. -/
public theorem oneSevenFactor_oddCore_quotient_isPGroup
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    IsPGroup 2 (E.map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
  obtain ⟨hderived, hsquare⟩ := derived_and_square_data E F hprod hF
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro element
  refine ⟨1, ?_⟩
  apply Subtype.ext
  obtain ⟨original, horiginal, heq⟩ := element.property
  change (element : G ⧸ pPrimeCore 2 G) ^ (2 ^ 1) = 1
  rw [← heq, pow_one, ← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (hderived (hsquare ⟨original, horiginal⟩))

end Stellmacher.SectionOne
