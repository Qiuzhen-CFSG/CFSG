module

public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupTheory.CComponent.SolvableQuotient
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# Two-components under odd normal quotients

A surjection with kernel of order prime to p identifies the quotients by
the two p-prime cores. Applying this to the restriction of an odd quotient
map gives the literal intrinsic quotient comparison for each subgroup.
The C-component correspondence for solvable kernels then restricts to a
bijection on two-components. In particular, two-components have ordinary
component images modulo the ambient odd core.

Solvability of the odd kernel is explicit at this lower layer; the source
consumer supplies the proved odd order theorem.
Source: GLS II, Proposition 4.7(iii) and Proposition 4.10(v), used in
Aschbacher--Smith I.3.1, printed p.414.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A coprime-kernel surjection induces an isomorphism modulo prime-complement cores. -/
noncomputable def pPrimeCoreQuotientEquiv (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : Nat.Coprime p (Nat.card f.ker)) :
    (G ⧸ pPrimeCore p G) ≃* (H ⧸ pPrimeCore p H) := by
  let q := (QuotientGroup.mk' (pPrimeCore p H)).comp f
  have he : q.ker = pPrimeCore p G := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pPrimeCore_comap_eq_of_surjective_coprime p f hf hk
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q ((QuotientGroup.mk'_surjective _).comp hf))

theorem pPrimeCoreQuotientEquiv_mk (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (hk : Nat.Coprime p (Nat.card f.ker)) (x : G) :
    f.pPrimeCoreQuotientEquiv p hf hk (QuotientGroup.mk' (pPrimeCore p G) x) =
      QuotientGroup.mk' (pPrimeCore p H) (f x) := rfl

end MonoidHom

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem quotient_subgroupMap_ker_coprime {p : ℕ}
    (N : Subgroup G) [N.Normal] (hn : Nat.Coprime p (Nat.card N)) (L : Subgroup G) :
    Nat.Coprime p (Nat.card ((QuotientGroup.mk' N).subgroupMap L).ker) := by
  let f := (QuotientGroup.mk' N).subgroupMap L
  have he : f.ker = N.subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (x : G)
  rw [he]
  exact hn.of_dvd_right (card_comap_dvd_of_injective N L.subtype L.subtype_injective)

/-- Odd normal quotients preserve the intrinsic odd-core quotient of every subgroup. -/
noncomputable def oddCoreQuotientImageEquiv (N : Subgroup G) [N.Normal]
    (hn : Odd (Nat.card N)) (L : Subgroup G) :
    (L ⧸ pPrimeCore 2 L) ≃*
      ((L.map (QuotientGroup.mk' N)) ⧸ pPrimeCore 2 (L.map (QuotientGroup.mk' N))) :=
  ((QuotientGroup.mk' N).subgroupMap L).pPrimeCoreQuotientEquiv 2
    ((QuotientGroup.mk' N).subgroupMap_surjective L)
    (quotient_subgroupMap_ker_coprime N (Nat.coprime_two_left.mpr hn) L)

/-- The preceding comparison uses the restriction of the original quotient map. -/
theorem oddCoreQuotientImageEquiv_mk (N : Subgroup G) [N.Normal]
    (hn : Odd (Nat.card N)) (L : Subgroup G) (x : L) :
    oddCoreQuotientImageEquiv N hn L (QuotientGroup.mk' (pPrimeCore 2 L) x) =
      QuotientGroup.mk' (pPrimeCore 2 (L.map (QuotientGroup.mk' N)))
        ((QuotientGroup.mk' N).subgroupMap L x) := rfl

namespace IsTwoComponent
variable {L : Subgroup G}

theorem map_odd_quotient (hL : L.IsTwoComponent) (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] (hn : Odd (Nat.card N)) :
    (L.map (QuotientGroup.mk' N)).IsTwoComponent := by
  let := hL.2
  exact ⟨hL.1.map_quotient N, IsQuasisimple.of_mulEquiv (oddCoreQuotientImageEquiv N hn L)⟩

theorem exists_map_odd_quotient_eq (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] (hn : Odd (Nat.card N))
    {K : Subgroup (G ⧸ N)} (hK : K.IsTwoComponent) :
    ∃ L : Subgroup G, L.IsTwoComponent ∧ L.map (QuotientGroup.mk' N) = K := by
  obtain ⟨L, hL, he⟩ := hK.1.exists_map_quotient_eq N
  have hq : IsQuasisimple (L.map (QuotientGroup.mk' N) ⧸
      pPrimeCore 2 (L.map (QuotientGroup.mk' N))) := he.symm ▸ hK.2
  let := hq
  exact ⟨L, ⟨hL, IsQuasisimple.of_mulEquiv (oddCoreQuotientImageEquiv N hn L).symm⟩, he⟩

theorem map_oddCore_isComponent (hL : L.IsTwoComponent)
    [Group.IsSolvable (pPrimeCore 2 G)] :
    IsComponent (G ⧸ pPrimeCore 2 G) (L.map (QuotientGroup.mk' (pPrimeCore 2 G))) :=
  (hL.map_odd_quotient (pPrimeCore 2 G) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)).isComponent_of_oddCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))

end IsTwoComponent

/-- Odd solvable normal quotients give a bijection on 2-components. -/
theorem bijOn_isTwoComponent_map_odd_quotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] (hn : Odd (Nat.card N)) :
    Set.BijOn (map (QuotientGroup.mk' N)) {L : Subgroup G | L.IsTwoComponent}
      {K : Subgroup (G ⧸ N) | K.IsTwoComponent} := by
  refine ⟨fun L hL => hL.map_odd_quotient N hn, ?_, ?_⟩
  · intro L hL K hK he
    exact hL.1.eq_of_map_quotient_eq hK.1 N he
  · intro K hK
    exact hK.exists_map_odd_quotient_eq N hn

end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Odd solvable normal quotients carry the whole two-layer onto the quotient two-layer. -/
theorem map_twoComponentLayer_odd_quotient (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] (hn : Odd (Nat.card N)) :
    (twoComponentLayer G).map (QuotientGroup.mk' N) = twoComponentLayer (G ⧸ N) := by
  rw [twoComponentLayer, sSup_eq_iSup', map_iSup]
  apply le_antisymm
  · exact iSup_le fun L => (L.property.map_odd_quotient N hn).le_twoComponentLayer
  · refine sSup_le fun K hK => ?_
    obtain ⟨L, hL, rfl⟩ := hK.exists_map_odd_quotient_eq N hn
    exact le_iSup (fun M : {L : Subgroup G // L.IsTwoComponent} =>
      M.1.map (QuotientGroup.mk' N)) ⟨L, hL⟩

end Subgroup
