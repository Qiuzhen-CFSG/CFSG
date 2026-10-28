module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PointwiseFrattiniSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.OrbitNormalizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowModels
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowRankLower
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Frattini
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.CentralizerResidualProducts
public import Theory.Frattini.Intersection
public import Theory.Frattini.PGroup

/-!
# The terminal two-component contradiction in original 2.5.20

The proved I.7.5 makes a returning component Sylow commute with the original
one. Its Frattini subgroup centralizes K by the literal source fixer action.
An involution in that Frattini subgroup and the prescribed paired residual
identify the returning component, leaving exactly two Sylow conjugates in T.
Their tight embedding then makes T permute the two components and normalize
K₀. The source normalizer obstruction excludes this in NormalitySource.

All component Sylows, quotient maps and conjugations are the original ones.
The final consumer supplies tightness from NormalityTight; the genuine
preceding paired residual identity remains the one earlier source input.
Source: Aschbacher–Smith 2.5.20, printed p.564.
-/

namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Normality
open Subgroup Theory.GroupTheory ComponentRefinement ComponentSelection
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem source_frattini_ne_bot
    (c : MathieuSourceSetup H K M S z) (hm : IsSmallRemainingComponent K) :
    frattini ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G) ≠ ⊥ := by
  let P := (MathieuSourceSetup.exists_relative_component_sylow c).choose
  let e := MathieuSourceSetup.component_sylow_equiv c
  have hs := hm.sylowTwoShape P
  obtain ⟨F, hFP, hF⟩ := hs.exists_four_le P
  let := hF
  have hfour : 4 ≤ Nat.card P := by
    simpa only [IsKleinFour.card_four] using card_le_of_le hFP
  have hz := hs.center_card
  let Q : Subgroup G := (S : Subgroup H).map H.subtype ⊓ K
  have hQp : IsPGroup 2 Q := P.isPGroup'.of_equiv e.symm
  let : Fact (IsPGroup 2 Q) := ⟨hQp⟩
  intro hbot
  let : IsElementaryAbelian 2 Q := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hbot
  let : IsMulCommutative P := ⟨⟨fun a b => e.symm.injective (by
    simpa only [map_mul] using (inferInstance : IsMulCommutative Q).is_comm.comm (e.symm a) (e.symm b))⟩⟩
  rw [center_eq_top, card_top] at hz
  omega

private theorem source_tight_setup
    (c : MathieuSourceSetup H K M S z) (hm : IsSmallRemainingComponent K)
    (htight : IsTightlyEmbedded K) :
    TightPGroupSetup K ⊤ ((S : Subgroup H).map H.subtype ⊓ K) c.T := by
  let Y := (S : Subgroup H).map H.subtype
  let Q := Y ⊓ K
  obtain ⟨P, hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  have hpQ : IsPGroup 2 Q := (S.isPGroup'.map H.subtype).to_le inf_le_left
  have hne : Q ≠ ⊥ := by
    intro he
    have hh := source_frattini_ne_bot c hm
    have hsub : Subsingleton Q := by rw [he]; infer_instance
    let := hsub
    exact hh (Subsingleton.elim _ _)
  refine ⟨htight, hpQ, hne, le_inf le_top inf_le_right, ?_, c.T.isPGroup',
    le_top, inf_le_left.trans c.sylow_lt.le⟩
  intro R hpR hRK hQR
  have hRK' : R ≤ K := hRK.trans inf_le_right
  have hp : IsPGroup 2 (R.subgroupOf K) := hpR.of_equiv (subgroupOfEquivOfLe hRK').symm
  have hPR : (P : Subgroup K) ≤ R.subgroupOf K := by
    intro x hx
    have hxY : (x : G) ∈ Y := by
      have hh : x ∈ Y.subgroupOf K := hP ▸ hx
      exact hh
    exact hQR ⟨hxY, x.property⟩
  have he := P.is_maximal' hp hPR
  intro r hr
  have hh : (⟨r, hRK' hr⟩ : K) ∈ (P : Subgroup K) := by
    rw [← he]
    exact hr
  have hhY : (⟨r, hRK' hr⟩ : K) ∈ Y.subgroupOf K := hP ▸ hh
  exact ⟨hhY, hRK' hr⟩

private theorem primeToResidual_eq_top_of_simple_three
    (L : Subgroup G) [IsSimpleGroup L] (hd : 3 ∣ Nat.card L) :
    primeToResidual 3 L = ⊤ := by
  rcases (inferInstance : (primeToResidual 3 L).Normal).eq_bot_or_eq_top with he | he
  · have hc := primeToResidual_index_coprime (G := L) 3
    rw [he, index_bot] at hc
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) (dvd_refl 3) hd hc).elim
  · exact he

omit [Finite G] in
private theorem embedded_residual_le (L C : Subgroup G)
    (hL : primeToResidual 3 L = ⊤) (hLC : L ≤ C) :
    L ≤ (primeToResidual 3 C).map C.subtype := by
  have hh := embedded_primeToResidual_mono 3 hLC
  rw [hL, ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh

omit [Finite G] in
private theorem conjugate_residual_top (L : Subgroup G)
    (hL : primeToResidual 3 L = ⊤) (g : G) :
    primeToResidual 3 (conjSubgroup L g) = ⊤ := by
  let e := (MulAut.conj g).subgroupMap L
  have hh := map_primeToResidual (p := 3) e
  rw [hL, map_top_of_surjective _ e.surjective] at hh
  exact hh.symm

omit [Finite G] in
private theorem residual_at_conjugate (P L : Subgroup G)
    (hres : ∀ i ∈ P, orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = L)
    (g i : G) (hi : i ∈ conjSubgroup P g) (hi2 : orderOf i = 2) :
    (primeToResidual 3 (centralizer ({i} : Set G))).map
      (centralizer ({i} : Set G)).subtype = conjSubgroup L g := by
  obtain ⟨j, hj, rfl⟩ := hi
  have hj2 : orderOf j = 2 := ((MulAut.conj g).orderOf_eq j).symm.trans hi2
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (hres j hj hj2)
  rw [map_embedded_primeToResidual, map_centralizer_singleton] at hh
  exact hh

/-- The original component Sylow has exactly its two prescribed conjugates
inside the ambient Sylow. The pointwise Frattini action excludes a third. -/
public theorem returning_sylow_eq_or_eq_conjugate
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.conjBy u : Set G))
    (htight : IsTightlyEmbedded K)
    (hres : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G), orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = K.conjBy u)
    (g : G) (hg : (((S : Subgroup H).map H.subtype ⊓ K).conjBy g) ≤ c.T) :
    (((S : Subgroup H).map H.subtype ⊓ K).conjBy g) =
        ((S : Subgroup H).map H.subtype ⊓ K) ∨
      (((S : Subgroup H).map H.subtype ⊓ K).conjBy g) =
        (((S : Subgroup H).map H.subtype ⊓ K).conjBy u) := by
  let Y := (S : Subgroup H).map H.subtype
  let P := Y ⊓ K
  let C := conjSubgroup K u
  let Pu := conjSubgroup P u
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  let : IsSimpleGroup K := MathieuSourceSetup.component_simple c hG hempty hgen
  have hKgen := primeToResidual_eq_top_of_simple_three K hm.three_dvd_card
  have d := source_tight_setup c hm htight
  have hphi := source_frattini_ne_bot c hm
  have huT : u ∈ c.T := c.sylow_lt.le hu
  have hPuT : Pu ≤ c.T := by
    exact (conjSubgroup_mono d.hQS u).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((c.T : Subgroup G).le_normalizer huT))
  have du := d.conjugate (mem_top u) c.T.isPGroup' le_top hPuT
  by_cases he : conjSubgroup P g = P
  · exact Or.inl he
  right
  let R := conjSubgroup P g
  have hRP : R ≤ centralizer (P : Set G) :=
    (lemma_I_7_5_commuting d hphi ⟨hg, g, mem_top _, rfl⟩ d.mem_family he).2
  have hRN : R ≤ normalizer (K : Set G) := hRP.trans
    ((Subgroup.centralizer_le_normalizer _).trans (htight.normalizer_le d.hQp d.hQne inf_le_right))
  have hpR : IsPGroup 2 R := d.hQp.map _
  have hphiC := MathieuSourceSetup.nonnormal_sylow_fixer_frattini
    c hG hempty hgen hb hn R hpR hRN hRP
  have hphiR : frattini R ≠ ⊥ := by
    intro he
    let e := (MulAut.conj g).subgroupMap P
    have hh := frattini_map_equiv e
    change (frattini P).map e.toMonoidHom = frattini R at hh
    rw [he] at hh
    exact hphi ((map_eq_bot_iff_of_injective (frattini P) e.injective).mp hh)
  let : Nontrivial (frattini R) := (Subgroup.nontrivial_iff_ne_bot _).mpr hphiR
  have hd : 2 ∣ Nat.card (frattini R) :=
    ((hpR.to_subgroup (frattini R)).card_eq_or_dvd.resolve_left
      (by have := Finite.one_lt_card (α := frattini R); omega))
  obtain ⟨i, hi2⟩ := exists_prime_orderOf_dvd_card' (G := frattini R) 2 hd
  let iG : G := ((i : R) : G)
  have hiG2 : orderOf iG = 2 := by
    simpa only [iG, Subgroup.orderOf_coe] using hi2
  have hiC : iG ∈ centralizer (K : Set G) := hphiC (mem_map_of_mem _ i.property)
  have hKCi : K ≤ centralizer ({iG} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hiC k hk)
  have hKCg : K ≤ conjSubgroup C g := by
    rw [← residual_at_conjugate P C hres g iG (i : R).property hiG2]
    exact embedded_residual_le K _ hKgen hKCi
  have hKeq : K = conjSubgroup C g := eq_of_le_of_card_ge hKCg (by
    dsimp [C]
    rw [card_conjSubgroup, card_conjSubgroup])
  have hKgK : conjSubgroup K g ≤ centralizer (K : Set G) := by
    have hh : conjSubgroup K g ≤ centralizer (conjSubgroup C g : Set G) :=
      (map_mono hc).trans (map_centralizer_le_centralizer_image _ _)
    simpa only [← hKeq] using hh
  have hpP : IsPGroup 2 P := d.hQp
  have hP2 : 2 ∣ Nat.card P := hpP.card_eq_or_dvd.resolve_left (by
    have hh : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr d.hQne
    let := hh
    have := Finite.one_lt_card (α := P)
    omega)
  obtain ⟨jP, hjP2⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hP2
  have hjG2 : orderOf (jP : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hjP2
  have hKgCj : conjSubgroup K g ≤ centralizer ({(jP : G)} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hKgK hk jP jP.property.2).symm)
  have hKgC : conjSubgroup K g ≤ C := by
    change conjSubgroup K g ≤ K.conjBy u
    rw [← hres jP jP.property hjG2]
    exact embedded_residual_le _ _ (conjugate_residual_top K hKgen g) hKgCj
  have hKgEq : conjSubgroup K g = C := eq_of_le_of_card_ge hKgC (by
    dsimp [C]
    rw [card_conjSubgroup, card_conjSubgroup])
  have hRC : R ≤ C := (conjSubgroup_mono (show P ≤ K from inf_le_right) g).trans_eq hKgEq
  have hRPu : R ≤ Pu := (le_inf hg hRC).trans_eq du.intersection_eq
  exact eq_of_le_of_card_ge hRPu (by
    change Nat.card (conjSubgroup P u) ≤ Nat.card (conjSubgroup P g)
    rw [card_conjSubgroup, card_conjSubgroup])

/-- The two returning Sylow conjugates force the ambient Sylow to normalize
the actual component orbit. -/
public theorem ambient_conjugate_eq_or_eq_conjugate
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.conjBy u : Set G))
    (_horbit : ∀ a ∈ (S : Subgroup H).map H.subtype,
      K.conjBy a = K ∨ K.conjBy a = K.conjBy u)
    (htight : IsTightlyEmbedded K)
    (hres : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G), orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = K.conjBy u)
    (t : G) (ht : t ∈ c.T) :
    conjSubgroup K t = K ∨ conjSubgroup K t = conjSubgroup K u := by
  let Y := (S : Subgroup H).map H.subtype
  let P := Y ⊓ K
  let C := conjSubgroup K u
  let Pu := conjSubgroup P u
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  have d := source_tight_setup c hm htight
  have huT : u ∈ c.T := c.sylow_lt.le hu
  have hfamily (g : G) (hg : conjSubgroup P g ≤ c.T) :
      conjSubgroup P g = P ∨ conjSubgroup P g = Pu :=
    returning_sylow_eq_or_eq_conjugate c hG hempty hgen hb hn u hu hc htight hres g hg
  have hPt : conjSubgroup P t ≤ c.T := (conjSubgroup_mono d.hQS t).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((c.T : Subgroup G).le_normalizer ht))
  rcases hfamily t hPt with he | he
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp
      (htight.normalizer_le d.hQp d.hQne inf_le_right
        (mem_normalizer_iff_map_conj_eq.mpr he)))
  · have hPN : conjSubgroup P (u⁻¹ * t) = P := by
      have hh := congrArg (fun Q => conjSubgroup Q u⁻¹) he
      simpa only [conjSubgroup_conjSubgroup, Pu, inv_mul_cancel,
        conjSubgroup_one] using hh
    have hKN : conjSubgroup K (u⁻¹ * t) = K := mem_normalizer_iff_map_conj_eq.mp
      (htight.normalizer_le d.hQp d.hQne inf_le_right
        (mem_normalizer_iff_map_conj_eq.mpr hPN))
    have hh := congrArg (fun Q => conjSubgroup Q u) hKN
    exact Or.inr (by simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel_left] using hh)

private theorem two_orbit_normalizes (K Y T : Subgroup G) (hYT : Y ≤ T)
    (u : G) (hu : u ∈ Y)
    (hY : ∀ a ∈ Y, K.conjBy a = K ∨ K.conjBy a = K.conjBy u)
    (hT : ∀ a ∈ T, K.conjBy a = K ∨ K.conjBy a = K.conjBy u) :
    T ≤ normalizer (componentOrbit K Y : Set G) := by
  have hD : componentOrbit K Y = K ⊔ K.conjBy u := by
    apply le_antisymm
    · change (⨆ a : Y, K.map (MulAut.conj (a : G)).toMonoidHom) ≤ K ⊔ K.conjBy u
      apply iSup_le
      intro a
      change K.conjBy (a : G) ≤ K ⊔ K.conjBy u
      rcases hY a a.property with he | he
      · rw [he]
        exact le_sup_left
      · rw [he]
        exact le_sup_right
    · exact sup_le (le_componentOrbit K Y) (le_iSup_of_le (⟨u, hu⟩ : Y) le_rfl)
  rw [hD]
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [Subgroup.map_sup]
    apply sup_le
    · change K.conjBy t ≤ K ⊔ K.conjBy u
      rcases hT t ht with he | he
      · rw [he]
        exact le_sup_left
      · rw [he]
        exact le_sup_right
    · change (K.conjBy u).conjBy t ≤ K ⊔ K.conjBy u
      rw [conjBy_conjBy]
      rcases hT (t * u) (T.mul_mem ht (hYT hu)) with he | he
      · rw [he]
        exact le_sup_left
      · rw [he]
        exact le_sup_right
  · rw [card_map_of_injective (MulAut.conj t).injective]

public theorem ambient_sylow_normalizes_orbit
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.conjBy u : Set G))
    (horbit : ∀ a ∈ (S : Subgroup H).map H.subtype,
      K.conjBy a = K ∨ K.conjBy a = K.conjBy u)
    (htight : IsTightlyEmbedded K)
    (hres : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G), orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = K.conjBy u) :
    (c.T : Subgroup G) ≤ normalizer
      (componentOrbit K ((S : Subgroup H).map H.subtype) : Set G) := by
  apply two_orbit_normalizes K ((S : Subgroup H).map H.subtype) (c.T : Subgroup G)
    c.sylow_lt.le u hu horbit
  intro t ht
  exact ambient_conjugate_eq_or_eq_conjugate c hG hempty hgen hb hn
    u hu hc horbit htight hres t ht

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Normality
