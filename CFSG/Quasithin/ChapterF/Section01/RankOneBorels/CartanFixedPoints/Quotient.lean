module
public import Theory.GroupAction.CartanPanelFixedPoints
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import Mathlib.GroupTheory.IsPerfect

/-!
# Literal local-panel transport through the two-core quotient

For the original local Sylow T = S ∩ L, the intrinsic Borel is N_L(T).
Its cosets are identified with the cosets of the quotient Sylow normalizer,
then with those of a chosen concrete model. All maps retain their formulas
on representatives and intertwine the actual left actions. In particular
the two-core acts trivially. A supplied odd complement maps to an odd
complement with both disjointness and the full join preserved.

The final lifting lemmas are conditional on the concrete model calculation;
model-specific source applications discharge that premise separately.
Source: Aschbacher--Smith, printed pp.259--260, F.1.1 and F.1.3(1).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Source
open Theory.CartanPanel
variable {G M : Type*} [Group G] [Group M]

/-- The actual intrinsic Borel cosets identify with the actual quotient-normalizer cosets. -/
noncomputable def localBorelCosetEquiv (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    L ⧸ (borel L S).subgroupOf L ≃
      (L ⧸ pCore 2 L) ⧸ sylowNormalizer (quotientSylow T) :=
  cosetEquiv (QuotientGroup.mk' (pCore 2 L)) (QuotientGroup.mk'_surjective _)
    _ _ ((quotientSylow_normalizer_comap T).trans
      (borel_subgroupOf_eq_sylowNormalizer L S T hT).symm)

@[simp] theorem localBorelCosetEquiv_mk (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L) (l : L) :
    localBorelCosetEquiv L S T hT (QuotientGroup.mk l) =
      QuotientGroup.mk (QuotientGroup.mk' (pCore 2 L) l) := rfl

/-- The representative formula after the actual quotient-model isomorphism. -/
noncomputable def localBorelModelCosetEquiv (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (e : (L ⧸ pCore 2 L) ≃* M) :
    L ⧸ (borel L S).subgroupOf L ≃ M ⧸
      sylowNormalizer ((quotientSylow T).mapSurjective (f := e.toMonoidHom) e.surjective) := by
  let C := sylowNormalizer ((quotientSylow T).mapSurjective (f := e.toMonoidHom) e.surjective)
  have hC : C.comap e.toMonoidHom = sylowNormalizer (quotientSylow T) := by
    have he : (sylowNormalizer (quotientSylow T)).map e.toMonoidHom = C :=
      Subgroup.map_equiv_normalizer_eq
        (quotientSylow T : Subgroup (L ⧸ pCore 2 L)) e
    change C.comap e.toMonoidHom = _
    rw [← he]
    exact Subgroup.comap_map_eq_self_of_injective e.injective _
  exact (localBorelCosetEquiv L S T hT).trans
    (cosetEquiv e.toMonoidHom e.surjective _ C hC)

@[simp] theorem localBorelModelCosetEquiv_mk (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (e : (L ⧸ pCore 2 L) ≃* M) (l : L) :
    localBorelModelCosetEquiv L S T hT e (QuotientGroup.mk l) =
      QuotientGroup.mk (e (QuotientGroup.mk' (pCore 2 L) l)) := rfl

theorem localBorelCosetEquiv_smul (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (l : L) (ω : L ⧸ (borel L S).subgroupOf L) :
    localBorelCosetEquiv L S T hT (l • ω) =
      QuotientGroup.mk' (pCore 2 L) l • localBorelCosetEquiv L S T hT ω :=
  cosetEquiv_smul _ _ _ _ _ l ω

theorem localBorelModelCosetEquiv_smul (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (e : (L ⧸ pCore 2 L) ≃* M) (l : L)
    (ω : L ⧸ (borel L S).subgroupOf L) :
    localBorelModelCosetEquiv L S T hT e (l • ω) =
      e (QuotientGroup.mk' (pCore 2 L) l) • localBorelModelCosetEquiv L S T hT e ω := by
  induction ω using Quotient.inductionOn with | h ω =>
    change QuotientGroup.mk (e (QuotientGroup.mk' (pCore 2 L) (l * ω))) =
      QuotientGroup.mk (e (QuotientGroup.mk' (pCore 2 L) l) *
        e (QuotientGroup.mk' (pCore 2 L) ω))
    rw [map_mul, map_mul]

/-- The local two-core acts trivially on every original Borel coset. -/
theorem twoCore_smul_localBorelCoset (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (l : L) (hl : l ∈ pCore 2 L) (ω : L ⧸ (borel L S).subgroupOf L) : l • ω = ω := by
  apply (localBorelCosetEquiv L S T hT).injective
  rw [localBorelCosetEquiv_smul]
  have he : QuotientGroup.mk' (pCore 2 L) l = 1 := by
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hl
  rw [he, one_smul]

variable {H : Type*} [Group H] [Finite H]

/-- An arbitrary odd complement survives the two-core projection, including
its disjointness and full join. -/
theorem quotientSylow_complement (T : Sylow 2 H) (D : Subgroup H)
    (hD : D ≤ sylowNormalizer T) (hodd : Nat.Coprime 2 (Nat.card D))
    (hdis : Disjoint (T : Subgroup H) D)
    (hsup : (T : Subgroup H) ⊔ D = sylowNormalizer T) :
    let E := D.map (QuotientGroup.mk' (pCore 2 H))
    E ≤ sylowNormalizer (quotientSylow T) ∧ Nat.Coprime 2 (Nat.card E) ∧
      Disjoint (quotientSylow T : Subgroup (H ⧸ pCore 2 H)) E ∧
      (quotientSylow T : Subgroup (H ⧸ pCore 2 H)) ⊔ E =
        sylowNormalizer (quotientSylow T) := by
  dsimp only
  refine ⟨?_, hodd.of_dvd_right (D.card_map_dvd _), ?_, ?_⟩
  · have he : (sylowNormalizer T).map (QuotientGroup.mk' (pCore 2 H)) =
        sylowNormalizer (quotientSylow T) := quotientSylow_normalizer_map T
    rw [← he]
    exact Subgroup.map_mono hD
  · apply Subgroup.disjoint_def.mpr
    rintro x hx ⟨d, hd, rfl⟩
    have hdT : d ∈ (T : Subgroup H) := by
      rw [← quotientSylow_comap T]
      exact hx
    rw [(Subgroup.disjoint_def.mp hdis) hdT hd, map_one]
  · change (T : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) ⊔ _ = _
    rw [← Subgroup.map_sup, hsup, quotientSylow_normalizer_map T]

/-- Lift the quotient-model fixed-pair calculation to the literal original local Borel. -/
theorem localBorel_two_fixed_of_quotient (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (hmodel : SylowHasTwoFixedCosets (quotientSylow T))
    (D : Subgroup L) (hD : D ≤ (borel L S).subgroupOf L)
    (hodd : Nat.Coprime 2 (Nat.card D)) (hdis : Disjoint (T : Subgroup L) D)
    (hsup : (T : Subgroup L) ⊔ D = (borel L S).subgroupOf L) :
    HasTwoFixedCosets ((borel L S).subgroupOf L) D := by
  have hB := borel_subgroupOf_eq_sylowNormalizer L S T hT
  obtain ⟨hDn, hDo, hDd, hDs⟩ := quotientSylow_complement T D (hB ▸ hD) hodd hdis
    (hsup.trans hB)
  exact two_fixed_pullback (QuotientGroup.mk' (pCore 2 L)) (QuotientGroup.mk'_surjective _)
    _ _ ((quotientSylow_normalizer_comap T).trans hB.symm) D
    (hmodel _ hDn hDo hDd hDs)

/-- Use an actual model isomorphism and its marked image Sylow, then lift to the source Borel. -/
theorem localBorel_two_fixed_of_model (L S : Subgroup G) [Finite L]
    (T : Sylow 2 L) (hT : (T : Subgroup L).map L.subtype = S ⊓ L)
    (e : (L ⧸ pCore 2 L) ≃* M)
    (hmodel : SylowHasTwoFixedCosets
      ((quotientSylow T).mapSurjective (f := e.toMonoidHom) e.surjective))
    (D : Subgroup L) (hD : D ≤ (borel L S).subgroupOf L)
    (hodd : Nat.Coprime 2 (Nat.card D)) (hdis : Disjoint (T : Subgroup L) D)
    (hsup : (T : Subgroup L) ⊔ D = (borel L S).subgroupOf L) :
    HasTwoFixedCosets ((borel L S).subgroupOf L) D := by
  apply localBorel_two_fixed_of_quotient L S T hT _ D hD hodd hdis hsup
  apply sylow_transport e.symm _ _ _ hmodel
  exact (Subgroup.map_symm_eq_iff_map_eq _).mpr rfl
end CFSG.Quasithin.ChapterF.Source
