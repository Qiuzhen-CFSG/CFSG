module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallFourExistence
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.SylowElementConjugacy
/-!
# Tight embedding from the original paired involution residual

The literal identity O^{3′}(C_G(i))=Kᵘ on involutions of the original
component Sylow extends to all involutions of K by conjugating into that
Sylow. Cubic generation then identifies O^{3′}(C_G(K))=Kᵘ and the reverse
identity. These force equality of the two component normalizers. An
involution in an intersection with a conjugate would identify the two
residuals and put the conjugator in the original normalizer, proving
tight embedding.

Source: Aschbacher–Smith 2.5.20, printed p.564. The earlier paired residual
calculation remains explicit; tightness is a conclusion. NormalitySource
uses this result on the original two-component orbit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ComponentSelection ComponentRefinement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_conj (X : Subgroup G) (g : G) :
    ((primeToResidual 3 X).map X.subtype).conjBy g =
      (primeToResidual 3 (X.conjBy g)).map (X.conjBy g).subtype :=
  map_embedded_primeToResidual 3 X (MulAut.conj g)

omit [Finite G] in
private theorem centralizer_conj (X : Subgroup G) (g : G) :
    (centralizer (X : Set G)).conjBy g = centralizer (X.conjBy g : Set G) :=
  map_centralizer_equiv (X : Set G) (MulAut.conj g)

omit [Finite G] in
private theorem involution_residual_conj (i g : G) :
    ((primeToResidual 3 (centralizer ({i} : Set G))).map
      (centralizer ({i} : Set G)).subtype).conjBy g =
    (primeToResidual 3 (centralizer ({MulAut.conj g i} : Set G))).map
      (centralizer ({MulAut.conj g i} : Set G)).subtype := by
  rw [residual_conj]
  have he : (centralizer ({i} : Set G)).conjBy g =
      centralizer ({MulAut.conj g i} : Set G) := by
    change (centralizer ({i} : Set G)).map (MulAut.conj g).toMonoidHom = _
    simpa only [Set.image_singleton] using
      map_centralizer_equiv ({i} : Set G) (MulAut.conj g)
  exact congrArg (fun C : Subgroup G => (primeToResidual 3 C).map C.subtype) he

private theorem tightlyEmbedded_of_residual (K C : Subgroup G)
    (heven : Even (Nat.card K))
    (hn : normalizer (C : Set G) ≤ normalizer (K : Set G))
    (hres : ∀ i : G, i ∈ K → orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = C) : IsTightlyEmbedded K := by
  refine ⟨heven, ?_⟩
  intro g hg
  apply Nat.not_even_iff_odd.mp
  intro hi
  obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card'
    (G := (K ⊓ K.map (MulAut.conj g).toMonoidHom : Subgroup G)) 2 (even_iff_two_dvd.mp hi)
  have hi2 : orderOf (i : G) = 2 := (orderOf_coe i).trans hi
  obtain ⟨j, hj, hji⟩ := i.property.2
  change MulAut.conj g j = (i : G) at hji
  have hj2 : orderOf j = 2 := by
    rw [← (MulAut.conj g).orderOf_eq j, hji]
    exact hi2
  have he := involution_residual_conj j g
  rw [hres j hj hj2, hji, hres i i.property.1 hi2] at he
  exact hg (hn (mem_normalizer_iff_map_conj_eq.mpr he))

/-- The involution residual on the actual component Sylow forces tight embedding. -/
theorem tightlyEmbedded_of_involution_residual_source
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.conjBy u : Set G))
    (horbit : ∀ a ∈ (S : Subgroup H).map H.subtype,
      K.conjBy a = K ∨ K.conjBy a = K.conjBy u)
    (hres : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G),
      orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = K.conjBy u) : IsTightlyEmbedded K := by
  let Y := (S : Subgroup H).map H.subtype
  let C := K.conjBy u
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  let : IsSimpleGroup K := MathieuSourceSetup.component_simple c hG hempty hgen
  have hz := MathieuSourceSetup.component_center_eq_bot c hG hempty hgen
  have hKr : primeToResidual 3 K = ⊤ := by
    rcases (inferInstance : (primeToResidual 3 K).Normal).eq_bot_or_eq_top with he | he
    · have hcop := primeToResidual_index_coprime (G := K) 3
      rw [he, index_bot] at hcop
      exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3)
        (dvd_refl 3) hm.three_dvd_card hcop).elim
    · exact he
  obtain ⟨F, hF, _⟩ := hm.exists_symmetric_four
  have hKeven : Even (Nat.card K) := by
    apply even_iff_two_dvd.mpr
    exact (show 2 ∣ Nat.card F by rw [hF.card_four]; decide).trans F.card_subgroup_dvd_card
  have hCne : C ≠ K := by
    intro he
    have hself : K ≤ centralizer (K : Set G) := by
      have hh : K ≤ centralizer (C : Set G) := hc
      rwa [he] at hh
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    have hxc : x ∈ center K := mem_center_iff.mpr (fun y =>
      Subtype.ext (hself x.property y y.property))
    rw [hz, mem_bot] at hxc
    exact hx hxc
  have hswap : C.conjBy u = K := by
    rcases horbit (u * u) (Y.mul_mem hu hu) with he | he
    · simpa only [conjBy_mul] using he
    · have he' : C.conjBy u = K.conjBy u := by simpa only [conjBy_mul] using he
      exact (hCne (map_injective (MulAut.conj u).injective he')).elim
  have hNC : K ≤ normalizer (C : Set G) := hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨P, hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  have hall : ∀ i : G, i ∈ K → orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = C := by
    intro i hi hi2
    let iK : K := ⟨i, hi⟩
    obtain ⟨j, hj⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (x := iK) (n := 1)
      (by simpa only [iK, Subgroup.orderOf_mk, pow_one] using hi2)
    obtain ⟨a, ha⟩ := isConj_iff.mp hj
    have hai : MulAut.conj (a : G) i = ((j : K) : G) := congrArg Subtype.val ha
    have hjY : ((j : K) : G) ∈ Y := by
      have hjP : (j : K) ∈ (P : Subgroup K) := j.property
      rw [hP] at hjP
      exact hjP
    have hj2 : orderOf ((j : K) : G) = 2 := by
      rw [← hai, (MulAut.conj (a : G)).orderOf_eq]
      exact hi2
    have hh := involution_residual_conj i (a : G)
    rw [hai, hres j ⟨hjY, (j : K).property⟩ hj2] at hh
    have hfix : C.conjBy (a : G) = C := mem_normalizer_iff_map_conj_eq.mp (hNC a.property)
    exact map_injective (MulAut.conj (a : G)).injective (hh.trans hfix.symm)
  have hCr : (primeToResidual 3 C).map C.subtype = C := by
    have he := map_embedded_primeToResidual 3 K (MulAut.conj u)
    rw [hKr, ← MonoidHom.range_eq_map, range_subtype] at he
    exact he.symm
  have hwhole : (primeToResidual 3 (centralizer (K : Set G))).map
      (centralizer (K : Set G)).subtype = C := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
        (even_iff_two_dvd.mp hKeven)
      have hi2 : orderOf (i : G) = 2 := (orderOf_coe i).trans hi
      have he := embedded_primeToResidual_mono 3
        (centralizer_le (Set.singleton_subset_iff.mpr i.property))
      exact he.trans (hall i i.property hi2).le
    · have he := embedded_primeToResidual_mono 3 (le_centralizer_iff.mp hc)
      rw [hCr] at he
      exact he
  have hreverse : (primeToResidual 3 (centralizer (C : Set G))).map
      (centralizer (C : Set G)).subtype = K := by
    have he := congrArg (fun X : Subgroup G => X.conjBy u) hwhole
    rw [residual_conj, centralizer_conj, hswap] at he
    exact he
  apply tightlyEmbedded_of_residual K C hKeven _ hall
  rw [← hreverse]
  exact (normalizer_le_normalizer_centralizer C).trans
    (normalizer_le_normalizer_characteristic_image (centralizer (C : Set G))
      (primeToResidual 3 (centralizer (C : Set G))))

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
