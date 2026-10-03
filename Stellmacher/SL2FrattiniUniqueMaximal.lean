module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Mathlib.GroupTheory.Frattini

/-!
# The unique maximal overgroup in a nested SL₂(2) Frattini lift

In a finite group whose quotient by the two-core, followed by the Frattini
quotient, is `SL₂(2)`, every Sylow two-subgroup lies in a unique maximal
subgroup. The conclusion uses the existing `IsUniqueMaximalContaining`
predicate inside the native top subgroup. No solvability assumption is needed.

The Sylow image in the final quotient has order two in a group of order six,
so it has prime index three and is maximal. Its inverse image under the
composite quotient map is a maximal subgroup containing the original Sylow.
Any other maximal overgroup contains the two-core. Its image in the final
quotient is proper: otherwise the Frattini nongeneration property would make
its image in the first quotient the whole group, and containment of the
two-core would make the original subgroup the whole group. Maximality of the
final Sylow image then places this overgroup inside the chosen inverse image,
forcing equality. A final subgroup equivalence expresses the result in the
native top subgroup without changing the given Sylow.

This finite-group consequence of the nested quotient hypothesis supplies the
unique-maximal input for local factors in Stellmacher's (4.6) and (6.1).
The `SL₂(2)` cardinality computation is imported from the Section 1 development;
the quotient itself is kept nested throughout.
-/

namespace Stellmacher

private theorem sylow_coatom_of_card_six {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (hH : Nat.card H = 6) : IsCoatom (P : Subgroup H) := by
  have hP : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hH]
    have hf : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hf]
  have hindex : (P : Subgroup H).index = 3 := by
    have := (P : Subgroup H).card_mul_index
    rw [hP, hH] at this
    omega
  refine ⟨?_, ?_⟩
  · intro heq
    rw [heq, Subgroup.index_top] at hindex
    omega
  · intro K hPK
    have hdvd := Subgroup.index_dvd_of_le hPK.le
    rw [hindex] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.index_eq_one.mp h1
    · have := Subgroup.index_strictAnti hPK
      omega

public theorem isUniqueMaximalContaining_of_sl2Two_frattini
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hA : IsSL2Two ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G) := by
  let Q := pCore 2 G
  let X := G ⧸ Q
  let qQ : G →* X := QuotientGroup.mk' Q
  let Φ : Subgroup X := frattini X
  let Y := X ⧸ Φ
  let qΦ : X →* Y := QuotientGroup.mk' Φ
  let q : G →* Y := qΦ.comp qQ
  have hqQ : Function.Surjective qQ := QuotientGroup.mk'_surjective Q
  have hqΦ : Function.Surjective qΦ := QuotientGroup.mk'_surjective Φ
  have hq : Function.Surjective q := hqΦ.comp hqQ
  have hkerQ : qQ.ker = Q := QuotientGroup.ker_mk' Q
  have hkerΦ : qΦ.ker = Φ := QuotientGroup.ker_mk' Φ
  let P : Sylow 2 Y := S.mapSurjective hq
  have hPmap : (P : Subgroup Y) = (S : Subgroup G).map q :=
    Sylow.coe_mapSurjective hq S
  have hPmax : IsCoatom (P : Subgroup Y) :=
    sylow_coatom_of_card_six P (SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hA)
  let K := (P : Subgroup Y).comap q
  have hKmax : IsCoatom K := Subgroup.isCoatom_comap_of_surjective hq hPmax
  have hSK : (S : Subgroup G) ≤ K := by
    intro s hs
    change q s ∈ (P : Subgroup Y)
    rw [hPmap]
    exact Subgroup.mem_map_of_mem q hs
  have hQ : Q ≤ (S : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S
  have huniq (L : Subgroup G) (hL : IsCoatom L) (hSL : (S : Subgroup G) ≤ L) : L = K := by
    have hkerL : qQ.ker ≤ L := by
      simpa only [hkerQ] using hQ.trans hSL
    have hLmap : L.map q ≠ ⊤ := by
      intro htop
      have hΦ : L.map qQ ⊔ Φ = ⊤ := by
        have hc := congrArg (Subgroup.comap qΦ) htop
        simpa only [q, ← Subgroup.map_map, Subgroup.comap_map_eq,
          hkerΦ, Subgroup.comap_top] using hc
      have hLX : L.map qQ = ⊤ := frattini_nongenerating hΦ
      apply hL.1
      have hc := congrArg (Subgroup.comap qQ) hLX
      simpa only [Subgroup.comap_map_eq, sup_eq_left.mpr hkerL,
        Subgroup.comap_top] using hc
    have hPL : (P : Subgroup Y) ≤ L.map q := hPmap ▸ Subgroup.map_mono hSL
    have hLP : L.map q = (P : Subgroup Y) :=
      (hPmax.le_iff_eq hLmap).mp hPL
    have hLK : L ≤ K := by
      intro l hl
      change q l ∈ (P : Subgroup Y)
      rw [← hLP]
      exact Subgroup.mem_map_of_mem q hl
    exact ((hL.le_iff_eq hKmax.1).mp hLK).symm
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  refine ⟨K.comap e.toMonoidHom, (Subgroup.isCoatom_comap e).mpr hKmax, ?_, ?_⟩
  · change (S : Subgroup G) ≤ (K.comap e.toMonoidHom).map e.toMonoidHom
    rwa [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
  · intro L hL hSL
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
    exact huniq (L.map e.toMonoidHom) ((OrderIso.isCoatom_iff e.mapSubgroup L).mpr hL) hSL
end Stellmacher
