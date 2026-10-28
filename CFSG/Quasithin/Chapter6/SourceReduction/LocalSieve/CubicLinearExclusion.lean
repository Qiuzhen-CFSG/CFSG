module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.CubicContainers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# Prime and twenty-five containing rows with an escaping cubic

The proper seed image in Y/O₂(Y) is A₅ in the odd-prime row. In the
PSL₂(25) row the quadratic embedding theorem gives PSL₂(5), and its
actual icosahedral isomorphism gives A₅. The two-group quotient kernel
then identifies the intrinsic seed quotient, without confusing the seed
with the whole residual.

An escaping cubic excludes the paired seed by the original Hall-plane
argument. It therefore makes that seed the residual, and the preceding
quotient-action theorem eliminates both normal containing rows. No
A₅ marking or field degree is assumed by these final applications.

Source: Aschbacher–Smith A.3.12(8) and 5.1.13, printed pp.47–48,636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem five_core_eq_bot : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply (inferInstance : (pCore 2 (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top.resolve_right
  intro ht
  let : Group.IsNilpotent (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
    ht ▸ pCore_isNilpotent (p := 2) (G := alternatingGroup (Fin 5))
  let : Group.IsSolvable (alternatingGroup (Fin 5)) := Group.isSolvable_of_surjective
    (f := (topEquiv (G := alternatingGroup (Fin 5))).toMonoidHom) topEquiv.surjective
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

private theorem core_quotient_A5_of_image {K Y : Subgroup G} (hKY : K ≤ Y)
    (e : (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) ≃* alternatingGroup (Fin 5)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  let f := e.toMonoidHom.comp (q.subgroupMap (K.subgroupOf Y))
  have hf : Function.Surjective f := e.surjective.comp (q.subgroupMap_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = _ from rfl,MonoidHom.ker_comp_of_injective _ _ e.injective,
      ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let ek := (subgroupOfEquivOfLe hKY).symm
  exact ⟨(QuotientGroup.congr _ _ ek (pCore_map_iso 2 ek)).trans
    ((MonoidHom.quotientPCoreEquivOfSurjective f hf hk).trans
      ((QuotientGroup.quotientMulEquivOfEq five_core_eq_bot).trans QuotientGroup.quotientBot))⟩

/-- The actual prime container identifies the intrinsic seed quotient and both prime congruences. -/
theorem seed_quotient_A5_of_prime_container
    {T : Sylow 2 G} {K H A Y : Subgroup G} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) :
    Chapter1.Section02.A312ExceptionalPrime p ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  let S := T.subtype (hTH.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let := pCore_isNilpotent (p := 2) (G := Y)
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlq : (K.subgroupOf Y).map q ∈ ChapterA.Section03.localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) : Subgroup (Y ⧸ pCore 2 Y)) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  obtain ⟨hprime,⟨e⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))) hlq
    (hC.map_quotient _) hlt.le hlt.ne hp ho
    (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm)
  exact ⟨hprime,core_quotient_A5_of_image (hKH.trans hY.2) e⟩

/-- The actual quadratic container identifies the intrinsic seed quotient as A₅. -/
theorem seed_quotient_A5_of_twentyFive_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  let S := T.subtype (hTH.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let := pCore_isNilpotent (p := 2) (G := Y)
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlq : (K.subgroupOf Y).map q ∈ ChapterA.Section03.localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) : Subgroup (Y ⧸ pCore 2 Y)) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  obtain ⟨_,F,_,_,hF,⟨e⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_models
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))) hlq
    (hC.map_quotient _) hlt.le hlt.ne (by decide : Nat.Prime 5) (by decide : Odd 5)
    (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  exact core_quotient_A5_of_image (hKH.trans hY.2)
    ((e.trans (GorensteinWalter.psl2RingEquiv eF)).trans
      Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some)

/-- A cubic escaping the residual excludes every normal odd prime-field PSL₂ container. -/
theorem cubic_escape_not_prime_container
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hXY : X ≤ Y) (hX : (X.subgroupOf Y).IsCComponent)
    (hXn : (X.subgroupOf Y).Normal) (hKX : residual H ≤ X)
    (hDA : D ≤ A) (hDY : D ≤ Y) (hDc : Nat.card D = 3)
    (hD : ¬ D ≤ normalizer (residual H : Set G))
    (hp : p.Prime) (ho : Odd p) : ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 p := by
  intro hm
  obtain ⟨_,_,hKL,_⟩ := localCartan_cubic_escape_residual_component h hH hgen c
    hY hescape hDA hDc hD
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  let e := subgroupOfEquivOfLe hXY
  have hmC : ClassicalGroup.IsPSL ((X.subgroupOf Y) ⧸ pCore 2 (X.subgroupOf Y)) 2 p :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hKC : residual H ≤ (X.subgroupOf Y).map Y.subtype := by
    rwa [map_subgroupOf_eq_of_le hXY]
  have hA5 := (seed_quotient_A5_of_prime_container h.qtke (map_subtype_le _) hH.1.1.2
    hKL horbit hY hescape (X.subgroupOf Y) hX hKC hp ho hmC).2
  exact hD (cubic_normalizes_of_prime_container h hH hgen c hY.2 hXY hXn hKX
    hA5 hp ho hm hDA hDY hDc)

/-- A cubic escaping the residual excludes a normal PSL₂(25) container. -/
theorem cubic_escape_not_twentyFive_container
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hXY : X ≤ Y) (hX : (X.subgroupOf Y).IsCComponent)
    (hXn : (X.subgroupOf Y).Normal) (hKX : residual H ≤ X)
    (hDA : D ≤ A) (hDY : D ≤ Y) (hDc : Nat.card D = 3)
    (hD : ¬ D ≤ normalizer (residual H : Set G))
    : ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 25 := by
  intro hm
  obtain ⟨_,_,hKL,_⟩ := localCartan_cubic_escape_residual_component h hH hgen c
    hY hescape hDA hDc hD
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  let e := subgroupOfEquivOfLe hXY
  have hmC : ClassicalGroup.IsPSL ((X.subgroupOf Y) ⧸ pCore 2 (X.subgroupOf Y)) 2 25 :=
    hm.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hKC : residual H ≤ (X.subgroupOf Y).map Y.subtype := by
    rwa [map_subgroupOf_eq_of_le hXY]
  have hA5 := seed_quotient_A5_of_twentyFive_container h.qtke (map_subtype_le _) hH.1.1.2
    hKL horbit hY hescape (X.subgroupOf Y) hX hKC hmC
  exact hD (cubic_normalizes_of_twentyFive_container h hH hgen c hY.2 hXY hXn hKX
    hA5 hm hDA hDY hDc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
