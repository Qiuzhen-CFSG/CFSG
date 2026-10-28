module
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Candidate

/-!
# The elementary two-core of the native standard sextet stabilizer

Coordinate conjugation identifies the literal native sextet stabilizer with
the proved hexacode affine group. Its translation kernel is exactly its
intrinsic two-core, elementary abelian of order 64. This module transports
that equality, the genuine quotient, and the action on the six tetrads back
to the native Witt-design group.

Every native two-subgroup fixing the individual tetrads consists of
translations, since the remaining column kernel has order three. The
transported six-generator Sylow candidate has at least 64 elements and fixes
the tetrads; equality of orders therefore identifies it with the core.
The same native conjugator places the whole Sylow group in the standard
sextet and incident octad stabilizers. Sylow conjugacy gives transport to
any native Sylow two-subgroup.

Source: Aschbacher–Smith H.14.1(1–2), printed pp.396–397, specifically the
assertion that the sextet kernel is E₆₄. The uniqueness of the two E₆₄
subgroups and the natural-module assertion require their further arguments;
neither is asserted here. The coordinate construction and ATLAS attribution
are documented in the imported `Comparison` and `Hexacode` modules.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SextetCore
open scoped Pointwise
open MathieuCode

/-- The native affine quotient, obtained from actual point-coordinate conjugation. -/
noncomputable def quotientHom : sextetStabilizer standardSextet →* Atlas.Codes.HexAutomorphisms :=
  Atlas.Codes.sextetQuotient.comp sextetEquiv.toMonoidHom

theorem quotientHom_surjective : Function.Surjective quotientHom :=
  Atlas.Codes.sextetQuotient_surjective.comp sextetEquiv.surjective

theorem core_elementary : IsElementaryAbelian 2 (pCore 2 (sextetStabilizer standardSextet)) := by
  let : IsElementaryAbelian 2 (pCore 2 Atlas.Codes.SextetStabilizer) :=
    atlas_core_eq_kernel.symm ▸ atlas_kernel_elementary
  have h := IsElementaryAbelian.map (p := 2)
    (A := pCore 2 Atlas.Codes.SextetStabilizer) sextetEquiv.symm.toMonoidHom
  rwa [pCore_map_iso] at h

theorem core_card : Nat.card (pCore 2 (sextetStabilizer standardSextet)) = 64 := by
  calc
    Nat.card (pCore 2 (sextetStabilizer standardSextet)) =
        Nat.card ((pCore 2 (sextetStabilizer standardSextet)).map sextetEquiv.toMonoidHom) :=
      (Subgroup.card_map_of_injective sextetEquiv.injective).symm
    _ = 64 := by
      rw [pCore_map_iso, atlas_core_eq_kernel, Atlas.Codes.sextetQuotient_kernel_card]

theorem quotientHom_ker : quotientHom.ker = pCore 2 (sextetStabilizer standardSextet) := by
  have h := sextetEquiv.toMonoidHom.comap_pCore_of_ker_isPGroup (p := 2) sextetEquiv.surjective
    (IsPGroup.ker_isPGroup_of_injective sextetEquiv.injective)
  rw [atlas_core_eq_kernel] at h
  exact h

/-- The genuine quotient identification, induced by the native affine action. -/
noncomputable def coreQuotientEquiv :
    (sextetStabilizer standardSextet ⧸ pCore 2 (sextetStabilizer standardSextet)) ≃*
      Atlas.Codes.HexAutomorphisms :=
  (QuotientGroup.quotientMulEquivOfEq quotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective quotientHom quotientHom_surjective)

/-- The intrinsic two-core included in the native ambient M₂₄. -/
noncomputable def core : Subgroup M24 :=
  (pCore 2 (sextetStabilizer standardSextet)).map (sextetStabilizer standardSextet).subtype

theorem core_le_stabilizer : core ≤ sextetStabilizer standardSextet :=
  Subgroup.map_subtype_le _

theorem core_ambient_elementary : IsElementaryAbelian 2 core := by
  let := core_elementary
  exact IsElementaryAbelian.map_subtype

theorem core_ambient_card : Nat.card core = 64 := by
  rw [core, Subgroup.card_map_of_injective (sextetStabilizer standardSextet).subtype_injective,
    core_card]

/-- The order of the actual native sextet stabilizer. -/
theorem stabilizer_card : Nat.card (sextetStabilizer standardSextet) = 138240 :=
  (Nat.card_congr sextetEquiv.toEquiv).trans Atlas.Codes.sextetStabilizer_card

/-- The action on the six tetrads, ordered by the hexacode coordinates. -/
noncomputable def columnHom : sextetStabilizer standardSextet →* Equiv.Perm (Fin 6) :=
  Atlas.Codes.sextetCoordinateHom.comp sextetEquiv.toMonoidHom

theorem columnHom_surjective : Function.Surjective columnHom :=
  (Atlas.Codes.hexCoordinateSix_surjective.comp Atlas.Codes.sextetQuotient_surjective).comp
    sextetEquiv.surjective

theorem columnHom_kernel_card : Nat.card columnHom.ker = 192 := by
  have he : columnHom.ker.map sextetEquiv.toMonoidHom =
      Atlas.Codes.sextetCoordinateHom.ker := by
    rw [columnHom, ← MonoidHom.comap_ker]
    apply Subgroup.map_comap_eq_self
    rw [sextetEquiv.toMonoidHom.range_eq_top_of_surjective sextetEquiv.surjective]
    exact le_top
  calc
    Nat.card columnHom.ker = Nat.card (columnHom.ker.map sextetEquiv.toMonoidHom) :=
      (Subgroup.card_map_of_injective sextetEquiv.injective).symm
    _ = 192 := by rw [he, Atlas.Codes.sextetCoordinate_kernel_card]

/-- The coordinate action retains the first coordinate of each native point image. -/
theorem columnHom_apply (g : sextetStabilizer standardSextet)
    (i : Atlas.Codes.HexIndex) (k : Fin 4) :
    columnHom g (Atlas.Codes.hexIndexEquiv i) =
      Atlas.Codes.hexIndexEquiv
        ((atlasPointEquiv.symm (g.val.val (atlasPointEquiv (i,k)))).1) := by
  let x := Atlas.Codes.sextetAffineEquiv.symm (sextetEquiv g)
  have h := Atlas.Codes.sextetAffineEquiv_coordinates x i k
  rw [Atlas.Codes.sextetAffineEquiv.apply_symm_apply] at h
  have he := congrArg (fun p : Atlas.Codes.Omega => Atlas.Codes.hexIndexEquiv p.1) h
  change Atlas.Codes.hexIndexEquiv
    ((atlasPointEquiv.symm (g.val.val (atlasPointEquiv (i,k)))).1) =
    Atlas.Codes.hexIndexEquiv (x.right.val.perm i) at he
  change Atlas.Codes.hexIndexEquiv
    (x.right.val.perm (Atlas.Codes.hexIndexEquiv.symm (Atlas.Codes.hexIndexEquiv i))) = _
  rw [Atlas.Codes.hexIndexEquiv.symm_apply_apply]
  exact he.symm

private def tetradIndex (i : Atlas.Codes.HexIndex) : Fin 6 :=
  ![0,4,3,2,1,5] (Atlas.Codes.hexIndexEquiv i)

private theorem point_mem_tetrad_iff : ∀ (i : Atlas.Codes.HexIndex) (p : Atlas.Codes.Omega),
    atlasPointEquiv p ∈ standardTetrad (tetradIndex i) ↔ p.1 = i := by decide +kernel

/-- Any two-subgroup fixing the six native tetrads lies in the actual two-core. -/
theorem two_subgroup_le_core (P : Subgroup M24) (hp : IsPGroup 2 P)
    (hPH : P ≤ sextetStabilizer standardSextet) (hfix : P ≤ partFixers) : P ≤ core := by
  let A := P.subgroupOf (sextetStabilizer standardSextet)
  have ha : IsPGroup 2 A := hp.comap_subtype
  have hcol : A.map sextetEquiv.toMonoidHom ≤ Atlas.Codes.sextetCoordinateHom.ker := by
    rintro _ ⟨g, hg, rfl⟩
    apply Equiv.ext
    intro j
    obtain ⟨i, rfl⟩ := Atlas.Codes.hexIndexEquiv.surjective j
    change columnHom g (Atlas.Codes.hexIndexEquiv i) = Atlas.Codes.hexIndexEquiv i
    rw [columnHom_apply g i 0]
    congr 1
    apply (point_mem_tetrad_iff i _).mp
    rw [atlasPointEquiv.apply_symm_apply]
    have ht := (Subgroup.mem_iInf.mp (hfix hg)) (tetradIndex i)
    exact (MulAction.mem_stabilizer_finset'.mp ht)
      ((point_mem_tetrad_iff i (i,0)).mpr rfl)
  have hle := atlas_two_subgroup_le_kernel _ (ha.map sextetEquiv.toMonoidHom) hcol
  intro g hg
  refine ⟨⟨g,hPH hg⟩, ?_, rfl⟩
  rw [← quotientHom_ker]
  exact hle ⟨⟨g,hPH hg⟩, hg, rfl⟩

/-- The concrete Sylow sextet candidate is exactly the native intrinsic core. -/
theorem standardCandidate_eq_core : standardCandidate = core := by
  have hle := two_subgroup_le_core standardCandidate
    (standardCandidate_elementary.isPGroup 2 _) standardCandidate_le_stabilizer
    standardCandidate_le_partFixers
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [core_ambient_card]; exact standardCandidate_card_lower)

/-- Native conjugacy identifies the catalogue's six-generator subgroup with this core. -/
theorem candidate_conjugate_core :
    candidate.map (MulAut.conj transport).toMonoidHom = core := standardCandidate_eq_core

theorem candidate_card : Nat.card candidate = 64 := by
  have h := core_ambient_card
  rw [← standardCandidate_eq_core, standardCandidate,
    Subgroup.card_map_of_injective (MulAut.conj transport).injective] at h
  exact h

theorem core_le_standardSylow : core ≤ standardSylow.toSubgroup := by
  rw [← standardCandidate_eq_core]
  exact standardCandidate_le_standardSylow

/-- Every native Sylow two-subgroup contains a conjugate of the standard sextet core. -/
theorem exists_core_conjugate_le (S : Sylow 2 M24) :
    ∃ g : M24, core.map (MulAut.conj g).toMonoidHom ≤ S.toSubgroup := by
  obtain ⟨g, hg⟩ := exists_conjugate_standardSylow S
  exact ⟨g, hg ▸ Subgroup.map_mono core_le_standardSylow⟩

end Sporadic.Mathieu.M24LocalGeometry.SextetCore
