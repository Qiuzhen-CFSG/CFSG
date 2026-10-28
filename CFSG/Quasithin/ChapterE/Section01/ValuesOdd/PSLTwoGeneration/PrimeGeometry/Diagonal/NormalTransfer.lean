module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import BenderSuzuki.External.Hall.Basic
public import Theory.ElementaryAbelian.Quotient

/-!
# Transport of concrete local geometry

Injective maps preserve the actual local models, including nonnormality of
the S₄ actor. They preserve the local Sylow intersection when the ambient
two-subgroup pulls back to the original one.

For a normal subgroup N supplementing T, suppose every family member in T
lies in N. Restrict the family by the literal subtype map and prove that its
weak closure maps onto the ambient weak closure. Geometry in N then escapes
the intersection of any proper Sylow overgroup with N, hence also escapes
that ambient overgroup. The final equivalence lemmas transfer the entire
concrete contract to an isomorphic group.

Source: the normal-subgroup and isomorphism transport in the prime-field
calculation for Aschbacher--Smith E.1.2, E.1.5 and E.1.14(6), pp.210 and 214.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

open Subgroup

variable {G K : Type*} [Group G] [Group K] [Finite G] [Finite K]

omit [Finite G] [Finite K] in
theorem localModel_map_injective {A H : Subgroup G} (h : LocalModel A H)
    (f : G →* K) (hf : Function.Injective f) : LocalModel (A.map f) (H.map f) := by
  let e := H.equivMapOfInjective f hf
  rcases h with ⟨he, hn⟩ | ⟨r, hr, hro, he⟩
  · refine Or.inl ⟨⟨e.symm.trans he.some⟩, ?_⟩
    intro hh
    apply hn
    have hm : ((A.subgroupOf H).map e.toMonoidHom).Normal := by
      rwa [intrinsic_subgroupOf_map f hf A H]
    exact (MulEquiv.normal_map_iff (f := e)).mp hm
  · exact Or.inr ⟨r, hr, hro, ⟨e.symm.trans he.some⟩⟩

omit [Finite K] in
theorem localSylow_map_of_comap (f : G →* K) (hf : Function.Injective f)
    (T H : Subgroup G) (U : Subgroup K) (hU : U.comap f = T)
    (hS : ∃ S : Sylow 2 H, (S : Subgroup H) = T.subgroupOf H) :
    ∃ S : Sylow 2 (H.map f), (S : Subgroup (H.map f)) = U.subgroupOf (H.map f) := by
  obtain ⟨S, hS⟩ := hS
  let e := H.equivMapOfInjective f hf
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup H).map e.toMonoidHom = _
  rw [hS, intrinsic_subgroupOf_map f hf T H]
  ext x
  obtain ⟨y, hy, he⟩ := x.property
  change x.val ∈ T.map f ↔ x.val ∈ U
  rw [← he, mem_map_iff_mem hf, ← hU]
  rfl

omit [Finite G] [Finite K] in
private theorem kleinFour_map_injective (A : Subgroup G) (hA : IsKleinFour A)
    (f : G →* K) (hf : Function.Injective f) : IsKleinFour (A.map f) := by
  let e := A.equivMapOfInjective f hf
  exact ⟨(Nat.card_congr e.toEquiv).symm.trans hA.card_four,
    (Monoid.exponent_eq_of_mulEquiv e.symm).trans hA.exponent_two⟩

/-- Concrete placement in a normal subgroup supplies the ambient inner
branch when every family member in T lies in that subgroup. The source
weak closure and Sylow intersections are transported literally. -/
theorem inner_escape_of_normal_geometry
    (N : Subgroup G) [N.Normal] (T : Sylow 2 G)
    (hgen : (T : Subgroup G) ⊔ N = ⊤)
    (hgeometry : ∀ Q : Sylow 2 N, ConcreteLocalGeometryAt Q)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A)
    (hinner : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≤ N)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (hM : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ IsKleinFour A ∧
      ∃ H : Subgroup G, A ≤ H ∧
        (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H) ∧
        LocalModel A H ∧ ¬ H ≤ M := by
  let Q := BenderSuzuki.External.hallSylowSubgroupOfNormal T N
  have hQ : (Q : Subgroup N) = (T : Subgroup G).subgroupOf N :=
    BenderSuzuki.External.hallSylowSubgroupOfNormal_coe T N
  let ΩN : Set (Subgroup N) := {B | B.map N.subtype ∈ Ω}
  have hΩN : IsElementaryFamily ΩN := by
    constructor
    · intro B hB
      let : IsElementaryAbelian 2 (B.map N.subtype) := hΩ.1 _ hB
      let e := (B.equivMapOfInjective N.subtype N.subtype_injective).symm
      exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
    · intro g B hB
      have he : (B.map (MulAut.conj g).toMonoidHom).map N.subtype =
          (B.map N.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
        rw [map_map, map_map]
        rfl
      change (B.map (MulAut.conj g).toMonoidHom).map N.subtype ∈ Ω
      rw [he]
      exact hΩ.2 g _ hB
  have hW : (weakClosure (Q : Subgroup N) ΩN).map N.subtype =
      weakClosure (T : Subgroup G) Ω := by
    rw [hQ]
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      rintro B ⟨hB, hBT⟩
      apply map_le_iff_le_comap.mp
      exact le_sSup ⟨hB, map_le_iff_le_comap.mpr hBT⟩
    · apply sSup_le
      rintro A ⟨hA, hAT⟩
      have hAN := hinner A hA hAT
      rw [← map_subgroupOf_eq_of_le hAN]
      apply map_mono
      apply le_sSup
      refine ⟨?_, comap_mono hAT⟩
      change (A.subgroupOf N).map N.subtype ∈ Ω
      rwa [map_subgroupOf_eq_of_le hAN]
  have hMN : M.subgroupOf N ≠ ⊤ := by
    intro h
    have hNM' : N ≤ M := by
      intro x hx
      exact (show (⟨x, hx⟩ : N) ∈ M.subgroupOf N from h ▸ mem_top _)
    exact hM (top_unique (hgen ▸ sup_le hTM hNM'))
  obtain ⟨M', hM', hMM'⟩ := (eq_top_or_exists_le_coatom (M.subgroupOf N)).resolve_left hMN
  have hQM' : (Q : Subgroup N) ≤ M' := by
    rw [hQ]
    exact (comap_mono hTM).trans hMM'
  have hWM' : normalizer (weakClosure (Q : Subgroup N) ΩN : Set N) ≤ M' := by
    apply le_trans _ hMM'
    apply map_le_iff_le_comap.mp
    exact (le_normalizer_map N.subtype).trans (hW ▸ hNM)
  have hlargeN : ∀ A ∈ ΩN, A ≤ (Q : Subgroup N) → A ≠ ⊥ → 1 < Group.rank A := by
    intro A hA hAT hAb
    have hATG : A.map N.subtype ≤ (T : Subgroup G) := by
      apply map_le_iff_le_comap.mpr
      change A ≤ (T : Subgroup G).subgroupOf N
      rwa [← hQ]
    have hAbG : A.map N.subtype ≠ ⊥ := by
      intro h
      exact hAb ((map_eq_bot_iff_of_injective A N.subtype_injective).mp h)
    have hr := hlarge _ hA hATG hAbG
    rwa [← Group.rank_congr (A.equivMapOfInjective N.subtype N.subtype_injective)] at hr
  obtain ⟨A, hA, hAQ, hAF, H, hAH, hS, hmodel, hHM'⟩ :=
    hgeometry Q ΩN hΩN hlargeN M' hM' hQM' hWM'
  refine ⟨A.map N.subtype, hA, ?_, kleinFour_map_injective A hAF N.subtype
    N.subtype_injective, H.map N.subtype, map_mono hAH, ?_,
    localModel_map_injective hmodel N.subtype N.subtype_injective, ?_⟩
  · apply map_le_iff_le_comap.mpr
    change A ≤ (T : Subgroup G).subgroupOf N
    rwa [← hQ]
  · exact localSylow_map_of_comap N.subtype N.subtype_injective Q H T hQ.symm hS
  · intro hHM
    exact hHM' ((map_le_iff_le_comap.mp hHM).trans hMM')

/-- Concrete placement is preserved by an actual group isomorphism. -/
theorem concreteGeometry_map_equiv {T : Sylow 2 G}
    (h : ConcreteLocalGeometryAt T) (e : G ≃* K) :
    ConcreteLocalGeometryAt (T.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  intro Ω hΩ hlarge M hM hTM hNM
  have hTM' : (T : Subgroup G) ≤ M.comap e.toMonoidHom :=
    map_le_iff_le_comap.mp hTM
  have hM' : IsCoatom (M.comap e.toMonoidHom) :=
    Subgroup.isCoatom_comap_of_surjective e.surjective hM
  have hNM' : normalizer (weakClosure (T : Subgroup G)
      {A | A.map e.toMonoidHom ∈ Ω} : Set G) ≤ M.comap e.toMonoidHom := by
    apply map_le_iff_le_comap.mp
    rw [map_normalizer_eq_of_bijective _ e.bijective, map_weakClosure_equiv]
    exact hNM
  have hlarge' : ∀ A ∈ {A : Subgroup G | A.map e.toMonoidHom ∈ Ω},
      A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A := by
    intro A hA hAT hne
    have hne' : A.map e.toMonoidHom ≠ ⊥ := by
      intro heq
      exact hne ((map_eq_bot_iff_of_injective A e.injective).mp heq)
    have hr := hlarge (A.map e.toMonoidHom) hA (map_mono hAT) hne'
    rwa [← Group.rank_congr (A.equivMapOfInjective e.toMonoidHom e.injective)] at hr
  obtain ⟨A, hA, hAT, hAF, H, hAH, hS, hmodel, hHM⟩ :=
    h _ (hΩ.comap_equiv e) hlarge' _ hM' hTM' hNM'
  refine ⟨A.map e.toMonoidHom, hA, map_mono hAT,
    kleinFour_map_injective A hAF e.toMonoidHom e.injective,
    H.map e.toMonoidHom, map_mono hAH, ?_,
    localModel_map_injective hmodel e.toMonoidHom e.injective, ?_⟩
  · apply localSylow_map_of_comap e.toMonoidHom e.injective T H _ _ hS
    exact comap_map_eq_self (by
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
      exact bot_le)
  · exact fun hm => hHM (map_le_iff_le_comap.mp hm)

/-- Transport model geometry to an arbitrary isomorphic ambient group. -/
theorem concreteGeometry_of_equiv (e : G ≃* K)
    (h : ∀ T : Sylow 2 G, ConcreteLocalGeometryAt T) :
    ∀ T : Sylow 2 K, ConcreteLocalGeometryAt T := by
  intro T
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective (f := e.toMonoidHom) e.surjective 2 T
  exact concreteGeometry_map_equiv (h S) e

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
