module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import Theory.GroupTheory.CommutatorPreimageTransport

/-!
# Representatives and quotient meaning of the local flag layers

The flag geometry uses actual left parabolic cosets in M. Right multiplying
a representative by its parabolic preserves incidence and each conjugated
local kernel, actor, and Z-layer. The supplied natural-section action proves
the same representative independence for the first flag layer. Reindexing
the incident fixed preimages proves it for the second flag layer.

Both flag layers contain Z_alpha and lie in V_alpha. Restriction to the
M-vertex stabilizer identifies each fixed preimage with an actual quotient
centralizer in G_alpha/Z_alpha. The denominator is normal only in that
stabilizer; none of these calculations assumes normality in the free amalgam.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), local flag notation on printed p.905 and its use on pp.906--908.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The local conjugation uses the same product as the original embedding. -/
theorem localConjugate_mul (H : Subgroup (FreeAmalgam R)) (g h : M) :
    localConjugate H (g * h) = localConjugate (localConjugate H h) g := by
  unfold localConjugate
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change embedM R (g * h) * x * (embedM R (g * h))⁻¹ =
    embedM R g * (embedM R h * x * (embedM R h)⁻¹) * (embedM R g)⁻¹
  rw [map_mul, _root_.mul_inv_rev]
  group

/-- Right multiplication by a normalizing parabolic element preserves the conjugate. -/
theorem localConjugate_right_mul (H : Subgroup (FreeAmalgam R)) (P : Subgroup M)
    (hn : P.map (embedM R) ≤ normalizer H) (g p : M) (hp : p ∈ P) :
    localConjugate H (g * p) = localConjugate H g := by
  rw [localConjugate_mul]
  have hh : localConjugate H p = H :=
    mem_normalizer_iff_map_conj_eq.mp (hn (mem_map_of_mem _ hp))
  rw [hh]

/-- Incidence is independent of the representative of the first parabolic coset. -/
theorem flagIncident_right_first (source : LocalSource L R) (i : Bool)
    (g h p : M) (hp : p ∈ parabolic source.projection source.flag i) :
    flagIncident source i (g * p) h ↔ flagIncident source i g h := by
  constructor
  · rintro ⟨m, hm, hn⟩
    refine ⟨m, ?_, hn⟩
    have hh := (parabolic source.projection source.flag i).mul_mem hp hm
    simpa only [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] using hh
  · rintro ⟨m, hm, hn⟩
    refine ⟨m, ?_, hn⟩
    simpa only [_root_.mul_inv_rev, mul_assoc] using
      (parabolic source.projection source.flag i).mul_mem
        ((parabolic source.projection source.flag i).inv_mem hp) hm

/-- Incidence is independent of the representative of the second parabolic coset. -/
theorem flagIncident_right_second (source : LocalSource L R) (i : Bool)
    (g h p : M) (hp : p ∈ parabolic source.projection source.flag (!i)) :
    flagIncident source i g (h * p) ↔ flagIncident source i g h := by
  constructor
  · rintro ⟨m, hm, hn⟩
    refine ⟨m, hm, ?_⟩
    have hh := (parabolic source.projection source.flag (!i)).mul_mem hp hn
    simpa only [_root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] using hh
  · rintro ⟨m, hm, hn⟩
    refine ⟨m, hm, ?_⟩
    simpa only [_root_.mul_inv_rev, mul_assoc] using
      (parabolic source.projection source.flag (!i)).mul_mem
        ((parabolic source.projection source.flag (!i)).inv_mem hp) hn

/-- The local core is independent of its parabolic coset representative. -/
theorem localFlagKernel_right_mul (source : LocalSource L R) (j : Bool)
    (g p : M) (hp : p ∈ parabolic source.projection source.flag j) :
    localFlagKernel source j (g * p) = localFlagKernel source j g :=
  localConjugate_right_mul _ _ (flagKernel_normalized source j) g p hp

/-- The full local actor is independent of its parabolic coset representative. -/
theorem localFlagActor_right_mul (source : LocalSource L R) (j : Bool)
    (g p : M) (hp : p ∈ parabolic source.projection source.flag j) :
    localFlagActor source j (g * p) = localFlagActor source j g :=
  localConjugate_right_mul _ _ (flagParabolic source j).le_normalizer g p hp

/-- The tilded residual is independent of its parabolic coset representative. -/
theorem localFlagResidual_right_mul [Finite M] (source : LocalSource L R) (j : Bool)
    (g p : M) (hp : p ∈ parabolic source.projection source.flag j) :
    localFlagResidual source j (g * p) = localFlagResidual source j g :=
  localConjugate_right_mul _ _ (flagResidual_normalized source j) g p hp

/-- The fixed Z-layer is independent of its parabolic coset representative. -/
theorem localFlagZ_right_mul (source : LocalSource L R) (j : Bool)
    (g p : M) (hp : p ∈ parabolic source.projection source.flag j) :
    localFlagZ source j (g * p) = localFlagZ source j g := by
  rw [localFlagZ, localFlagZ, localFlagKernel_right_mul source j g p hp]

/-- The supplied genuine natural action makes the first layer independent of representatives. -/
theorem firstFlagLayer_right_mul (source : LocalSource L R) (i : Bool)
    (natural : FlagNaturalSection source i)
    (g p : M) (hp : p ∈ parabolic source.projection source.flag i) :
    firstFlagLayer (R := R) (g * p) = firstFlagLayer (R := R) g :=
  localConjugate_right_mul _ _ natural.normalized g p hp

/-- The incident fixed span is independent of the second coset representative. -/
theorem secondFlagLayer_right_mul (source : LocalSource L R) (i : Bool)
    (h p : M) (hp : p ∈ parabolic source.projection source.flag (!i)) :
    secondFlagLayer source i (h * p) = secondFlagLayer source i h := by
  unfold secondFlagLayer
  simp only [flagIncident_right_second source i _ h p hp,
    localFlagKernel_right_mul source (!i) h p hp]

/-- Every incident second-color coset has a representative in the first parabolic. -/
theorem flagIncident_one_iff (source : LocalSource L R) (i : Bool) (h : M) :
    flagIncident source i 1 h ↔
      ∃ m ∈ parabolic source.projection source.flag i,
        h⁻¹ * m ∈ parabolic source.projection source.flag (!i) := by
  simp only [flagIncident, inv_one, one_mul]


/-- Conjugating an ambient subgroup of G_alpha by an embedded M-element stays in G_alpha. -/
theorem localConjugate_le_stabilizer (H : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R (alpha R)) (g : M) :
    localConjugate H g ≤ stabilizer R (alpha R) := by
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  exact (map_mono hH).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((stabilizer R (alpha R)).le_normalizer hg))

/-- Every source local core is in the same finite M-vertex stabilizer. -/
theorem localFlagKernel_le_stabilizer (source : LocalSource L R) (j : Bool) (g : M) :
    localFlagKernel source j g ≤ stabilizer R (alpha R) :=
  localConjugate_le_stabilizer _ ((flagKernel_le source j).trans (flagParabolic_le source j)) g

/-- The full local actor stays in the original M-vertex stabilizer. -/
theorem localFlagActor_le_stabilizer (source : LocalSource L R) (j : Bool) (g : M) :
    localFlagActor source j g ≤ stabilizer R (alpha R) :=
  localConjugate_le_stabilizer _ (flagParabolic_le source j) g

/-- Each first-color layer lies in V_alpha through the original conjugation map. -/
theorem firstFlagLayer_le_radius (g : M) : firstFlagLayer (R := R) g ≤ V R (alpha R) := by
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  exact (map_mono (edgeRadius_le_radius (alpha R) (beta R) rfl (base_adjacent R))).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized R _ hg))

/-- Every first-color layer contains Z_alpha, which is fixed as a subgroup by M. -/
theorem Z_le_firstFlagLayer (g : M) : Z R (alpha R) ≤ firstFlagLayer (R := R) g := by
  have hZ : Z R (alpha R) ≤ V R (beta R) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le (alpha R)
      (le_iSup_of_le (adjacent_symm R (base_adjacent R)) le_rfl)
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  have he := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hg)
  exact he.symm.le.trans (map_mono hZ)

/-- The fixed preimages defining the second layer also stay in V_alpha. -/
theorem secondFlagLayer_le_radius (source : LocalSource L R) (i : Bool) (h : M) :
    secondFlagLayer source i h ≤ V R (alpha R) := by
  apply iSup_le
  intro g
  apply iSup_le
  intro _
  exact (commutatorPreimage_le _ _ _).trans (firstFlagLayer_le_radius g)

/-- All second-color layers contain the same actual quotient denominator. -/
theorem Z_le_secondFlagLayer (source : LocalSource L R) (i : Bool) (h : M) :
    Z R (alpha R) ≤ secondFlagLayer source i h := by
  have hi : flagIncident source i h h :=
    ⟨h, by simp only [inv_mul_cancel]; exact one_mem _,
      by simp only [inv_mul_cancel]; exact one_mem _⟩
  apply le_iSup_of_le h
  apply le_iSup_of_le hi
  exact le_commutatorPreimage (Z_le_firstFlagLayer h)
    (le_normalizer_iff_commutator_le_left.mp
      ((localFlagKernel_le_stabilizer source (!i) h).trans (Z_normalized R _)))

/-- A summand in the second layer is the literal centralizer preimage in G_alpha/Z_alpha.
Only relative normality is used; no normality in the free amalgam is asserted. -/
theorem flag_fixedPreimage_quotient (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (g h : M) :
    letI := geometry.Z_normal (alpha R)
    (commutatorPreimage (firstFlagLayer (R := R) g) (localFlagKernel source (!i) h)
      (Z R (alpha R))).subgroupOf (stabilizer R (alpha R)) =
    (firstFlagLayer (R := R) g).subgroupOf (stabilizer R (alpha R)) ⊓
      (centralizer (((localFlagKernel source (!i) h).subgroupOf (stabilizer R (alpha R))).map
        (QuotientGroup.mk' ((Z R (alpha R)).subgroupOf (stabilizer R (alpha R)))) :
          Set ((stabilizer R (alpha R)) ⧸
            (Z R (alpha R)).subgroupOf (stabilizer R (alpha R))))).comap
        (QuotientGroup.mk' ((Z R (alpha R)).subgroupOf (stabilizer R (alpha R)))) := by
  let := geometry.Z_normal (alpha R)
  rw [commutatorPreimage_subgroupOf _ _ _ _
    ((firstFlagLayer_le_radius g).trans (geometry.V_local _ rfl hlarge))
    (localFlagKernel_le_stabilizer source (!i) h) (Z_normalized R _)]
  exact commutatorPreimage_eq_inf_comap_centralizer _ _ _

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
