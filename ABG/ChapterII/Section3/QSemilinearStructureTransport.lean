module
public import ABG.ChapterII.Section3.QSemilinearStructureStatement

/-!
# Transport of the complete Q-group semilinear conclusion

The full conclusion of ABG II.3 Proposition 3 is preserved by an ambient group
isomorphism and a field isomorphism, including a change of universes. The two
subgroup factors and the specified initial constituent move by the ambient
isomorphism. The linear alternative uses entrywise coefficient transport on
GL2 together with conjugation of field automorphisms; this identifies each
exact determinant level and carries pure coefficient elements to pure
coefficient elements. The unitary alternative retains its canonical Galois
field and uses only equality of the cardinalities of the supplied fields.

The final clause keeps the original Sylow subgroup: restrict the ambient
isomorphism to the normal constituent, map that Sylow subgroup, and identify
the ambient centralizers. Invariance of the odd core under isomorphism then
transports the exact complement equality. This separates transport from the
construction over a canonical finite field without adding any hypothesis on
the semilinear action.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp24--28;
the complete shared statement is in `QSemilinearStructureStatement.lean`.
-/

namespace ABG
open Matrix.GeneralLinearGroup GorensteinWalter
universe u v

private def ringAutTransport {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    (F ≃+* F) ≃* (K ≃+* K) where
  toFun σ := (e.symm.trans σ).trans e
  invFun τ := (e.trans τ).trans e.symm
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp
  map_mul' σ τ := by ext x; simp

private def gammaL2Transport {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    GammaL2 F ≃* GammaL2 K :=
  SemidirectProduct.congr (coefficientEquiv e) (ringAutTransport e) (by
    intro σ
    ext A i j
    change e (σ (A i j)) = e (σ (e.symm (e (A i j))))
    rw [e.symm_apply_apply])

private theorem gammaL2Transport_inl {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (A : GL (Fin 2) F) :
    gammaL2Transport e (SemidirectProduct.inl A) =
      SemidirectProduct.inl (coefficientEquiv e A) := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one (ringAutTransport e)

private theorem gammaL2Transport_inr {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (σ : F ≃+* F) :
    gammaL2Transport e (SemidirectProduct.inr σ) =
      SemidirectProduct.inr (ringAutTransport e σ) := by
  apply SemidirectProduct.ext
  · exact map_one (coefficientEquiv e)
  · rfl

private theorem gammaL2Transport_level {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (m : ℕ) :
    ((determinantTwoPower F m).map (SemidirectProduct.inl : _ →* GammaL2 F)).map
      (gammaL2Transport e).toMonoidHom =
        (determinantTwoPower K m).map SemidirectProduct.inl := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨coefficientEquiv e A, (determinantTwoPower_mem_map_iff e m A).mpr hA,
      (gammaL2Transport_inl e A).symm⟩
  · rintro _ ⟨A, hA, rfl⟩
    refine ⟨SemidirectProduct.inl ((coefficientEquiv e).symm A), ?_, ?_⟩
    · refine ⟨(coefficientEquiv e).symm A, ?_, rfl⟩
      exact (determinantTwoPower_mem_map_iff e m _).mp (by
        change coefficientEquiv e ((coefficientEquiv e).symm A) ∈ _
        simpa only [MulEquiv.apply_symm_apply, SetLike.mem_coe] using hA)
    · change gammaL2Transport e (SemidirectProduct.inl ((coefficientEquiv e).symm A)) = _
      rw [gammaL2Transport_inl, MulEquiv.apply_symm_apply]

private theorem subgroup_map_comp_equiv_symm
    {G G' K : Type*} [Group G] [Group G'] [Group K]
    (e : G ≃* G') (f : G →* K) (U : Subgroup G) :
    (U.map e.toMonoidHom).map (f.comp e.symm.toMonoidHom) = U.map f := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem centralizer_map_equiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (P : Subgroup G) :
    (Subgroup.centralizer (P : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (P.map e.toMonoidHom : Set G') := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    obtain ⟨g, hg, rfl⟩ := hy
    change e g * x = x * e g
    simpa only [map_mul, e.apply_symm_apply] using congrArg e (hx g hg)
  · intro hx y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hx (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)

private theorem ambient_core_map {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (C : Subgroup G) :
    ((pPrimeCore 2 C).map C.subtype).map e.toMonoidHom =
      (pPrimeCore 2 (C.map e.toMonoidHom)).map (C.map e.toMonoidHom).subtype := by
  let eC : C ≃* C.map e.toMonoidHom := e.subgroupMap C
  have he : (pPrimeCore 2 C).map eC.toMonoidHom =
      pPrimeCore 2 (C.map e.toMonoidHom) := pPrimeCore_map_iso 2 eC
  rw [← he]
  simp only [Subgroup.map_map]
  rfl

private theorem sylow_centralizer_core_transport
    {G G' : Type*} [Group G] [Finite G] [Group G']
    (e : G ≃* G') (L E : Subgroup G)
    (h : ∃ S : Sylow 2 L,
      let C := Subgroup.centralizer (((S : Subgroup L).map L.subtype) : Set G)
      E = (pPrimeCore 2 C).map C.subtype) :
    ∃ S : Sylow 2 (L.map e.toMonoidHom),
      let C := Subgroup.centralizer
        (((S : Subgroup (L.map e.toMonoidHom)).map (L.map e.toMonoidHom).subtype) : Set G')
      E.map e.toMonoidHom = (pPrimeCore 2 C).map C.subtype := by
  obtain ⟨S, hS⟩ := h
  let eL : L ≃* L.map e.toMonoidHom := e.subgroupMap L
  let S' := S.mapSurjective (f := eL.toMonoidHom) eL.surjective
  refine ⟨S', ?_⟩
  have hmap : (S' : Subgroup (L.map e.toMonoidHom)).map (L.map e.toMonoidHom).subtype =
      ((S : Subgroup L).map L.subtype).map e.toMonoidHom := by
    change ((S : Subgroup L).map eL.toMonoidHom).map _ = _
    simp only [Subgroup.map_map]
    rfl
  dsimp only
  rw [hmap, ← centralizer_map_equiv, hS, ambient_core_map]

private theorem complement_transport
    {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') (L E : Subgroup G) (h : L.IsComplement' E) :
    (L.map e.toMonoidHom).IsComplement' (E.map e.toMonoidHom) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · have hL : Nat.card L = Nat.card (L.map e.toMonoidHom) :=
      Nat.card_congr (e.subgroupMap L).toEquiv
    have hE : Nat.card E = Nat.card (E.map e.toMonoidHom) :=
      Nat.card_congr (e.subgroupMap E).toEquiv
    rw [← hL, ← hE, ← Nat.card_congr e.toEquiv]
    exact h.card_mul_card
  · exact Subgroup.disjoint_map e.injective h.disjoint

/-- The complete Q-group structure conclusion is invariant under group and field isomorphisms. -/
public theorem qSemilinearStructureConclusion_transport
    {H F : Type u} {H' F' : Type v}
    [Group H] [Finite H] [Field F] [Finite F]
    [Group H'] [Finite H'] [Field F'] [Finite F']
    {L0 : Subgroup H} (eH : H ≃* H') (eF : F ≃+* F')
    (h : qSemilinearStructureConclusion L0 F) :
    qSemilinearStructureConclusion (L0.map eH.toMonoidHom) F' := by
  obtain ⟨L, E, hLn, hL0, hLE, hEc, hEo, hmodel, hcore⟩ := h
  refine ⟨L.map eH.toMonoidHom, E.map eH.toMonoidHom,
    hLn.map eH.toMonoidHom eH.surjective, Subgroup.map_mono hL0,
    complement_transport eH L E hLE, (eH.subgroupMap E).isCyclic.mp hEc, ?_, ?_,
    sylow_centralizer_core_transport eH L E hcore⟩
  · have hE : Nat.card E = Nat.card (E.map eH.toMonoidHom) :=
      Nat.card_congr (eH.subgroupMap E).toEquiv
    rwa [← hE]
  · rcases hmodel with hlin | hunit
    · obtain ⟨m, φ, hφ, hm, hL, hE⟩ := hlin
      let φ' := (gammaL2Transport eF).toMonoidHom.comp (φ.comp eH.symm.toMonoidHom)
      refine Or.inl ⟨m, φ', (gammaL2Transport eF).injective.comp
        (hφ.comp eH.symm.injective), ?_, ?_, ?_⟩
      · simpa only [← Nat.card_congr eF.toEquiv] using hm
      · change (L.map eH.toMonoidHom).map
          ((gammaL2Transport eF).toMonoidHom.comp (φ.comp eH.symm.toMonoidHom)) = _
        rw [← Subgroup.map_map, subgroup_map_comp_equiv_symm, hL,
          gammaL2Transport_level]
      · change (E.map eH.toMonoidHom).map
          ((gammaL2Transport eF).toMonoidHom.comp (φ.comp eH.symm.toMonoidHom)) ≤ _
        rw [← Subgroup.map_map, subgroup_map_comp_equiv_symm]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨σ, rfl⟩ := hE hx
        exact ⟨ringAutTransport eF σ, (gammaL2Transport_inr eF σ).symm⟩
    · obtain ⟨p, d, hp, hpodd, hd, hcard, m, φ, hφ, hm, hL, hE⟩ := hunit
      let : Fact p.Prime := ⟨hp⟩
      refine Or.inr ⟨p, d, hp, hpodd, hd, ?_, m, φ.comp eH.symm.toMonoidHom,
        hφ.comp eH.symm.injective, hm, ?_, ?_⟩
      · exact (Nat.card_congr eF.toEquiv).symm.trans hcard
      · rw [subgroup_map_comp_equiv_symm]
        exact hL
      · rw [subgroup_map_comp_equiv_symm]
        exact hE

end ABG
