module

public import CFSG.Quasithin.ChapterF.Section01.SourceBasic

/-!
# The quotient geometry of the local Borel in F.1.3(1)

Source: Aschbacher–Smith, printed pp.259–260. Since the two-core lies in
every Sylow two-subgroup, the inverse image of the quotient Sylow subgroup
is the original Sylow subgroup. Normalizers therefore commute with this
quotient. Properness and uniqueness of the proper Sylow overgroup lift
through the subgroup correspondence. The two-core of a Sylow normalizer
is the Sylow subgroup itself, independently of the rank-one hypothesis.

These are reduction lemmas: the concrete model statements still have to be
proved before they establish F.1.3(1).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source

variable {H : Type*} [Group H] [Finite H]

/-- The actual image Sylow subgroup in the quotient by the two-core. -/
def quotientSylow (T : Sylow 2 H) : Sylow 2 (H ⧸ pCore 2 H) :=
  T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))

/-- Taking the image and inverse image recovers the original Sylow subgroup. -/
theorem quotientSylow_comap (T : Sylow 2 H) :
    (quotientSylow T : Subgroup (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) = (T : Subgroup H) := by
  apply Subgroup.comap_map_eq_self
  simpa only [QuotientGroup.ker_mk'] using pCore_isPGroup.le_sylow_of_normal T

/-- The local Borel is precisely the inverse image of the quotient normalizer. -/
theorem quotientSylow_normalizer_comap (T : Sylow 2 H) :
    (Subgroup.normalizer ((quotientSylow T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H))).comap
      (QuotientGroup.mk' (pCore 2 H)) = Subgroup.normalizer ((T : Subgroup H) : Set H) := by
  rw [Subgroup.comap_normalizer_eq_of_surjective _
    (QuotientGroup.mk'_surjective _), quotientSylow_comap]

/-- Projection maps the local Borel onto the actual quotient Sylow normalizer. -/
theorem quotientSylow_normalizer_map (T : Sylow 2 H) :
    (Subgroup.normalizer ((T : Subgroup H) : Set H)).map (QuotientGroup.mk' (pCore 2 H)) =
      Subgroup.normalizer ((quotientSylow T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
  rw [← quotientSylow_normalizer_comap T]
  exact Subgroup.map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top)

omit [Finite H] in
/-- The two-core clause of F.1.3(1) holds for every Sylow normalizer. -/
theorem twoCore_sylow_normalizer (T : Sylow 2 H) :
    twoCore (Subgroup.normalizer ((T : Subgroup H) : Set H)) = (T : Subgroup H) := by
  have hsub : IsPGroup 2 ((T : Subgroup H).subgroupOf
      (Subgroup.normalizer ((T : Subgroup H) : Set H))) :=
    T.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe
      (T : Subgroup H).le_normalizer).symm
  have hle : (T : Subgroup H).subgroupOf (Subgroup.normalizer ((T : Subgroup H) : Set H)) ≤
      pCore 2 (Subgroup.normalizer ((T : Subgroup H) : Set H)) := le_sSup ⟨inferInstance, hsub⟩
  have hle' : (T : Subgroup H) ≤ twoCore (Subgroup.normalizer ((T : Subgroup H) : Set H)) := by
    simpa only [twoCore, Subgroup.map_subgroupOf_eq_of_le
      (T : Subgroup H).le_normalizer] using
      Subgroup.map_mono (f := (Subgroup.normalizer ((T : Subgroup H) : Set H)).subtype) hle
  exact T.is_maximal' (pCore_isPGroup.map _) hle'

/-- Properness of the quotient Borel lifts through the two-core. -/
theorem sylow_normalizer_proper_of_quotient (T : Sylow 2 H)
    (hproper : Subgroup.normalizer ((quotientSylow T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)) < ⊤) :
    Subgroup.normalizer ((T : Subgroup H) : Set H) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro heq
  apply hproper.ne
  rw [← quotientSylow_normalizer_map T, heq, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pCore 2 H))

/-- Every proper overgroup of the original Sylow maps to a proper overgroup
in the quotient, so the quotient uniqueness assertion lifts. -/
theorem sylow_normalizer_unique_of_quotient (T : Sylow 2 H)
    (hunique : ∀ M : Subgroup (H ⧸ pCore 2 H),
      (quotientSylow T : Subgroup (H ⧸ pCore 2 H)) ≤ M → M < ⊤ →
        M ≤ Subgroup.normalizer ((quotientSylow T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)))
    (M : Subgroup H) (hTM : (T : Subgroup H) ≤ M) (hM : M < ⊤) :
    M ≤ Subgroup.normalizer ((T : Subgroup H) : Set H) := by
  have hker : (QuotientGroup.mk' (pCore 2 H)).ker ≤ M := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal T).trans hTM
  have hproper : M.map (QuotientGroup.mk' (pCore 2 H)) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    apply hM.ne
    rw [← Subgroup.comap_map_eq_self hker, heq, Subgroup.comap_top]
  rw [← quotientSylow_normalizer_comap T]
  apply Subgroup.map_le_iff_le_comap.mp
  exact hunique _ (Subgroup.map_mono hTM) hproper

end CFSG.Quasithin.ChapterF.Source
