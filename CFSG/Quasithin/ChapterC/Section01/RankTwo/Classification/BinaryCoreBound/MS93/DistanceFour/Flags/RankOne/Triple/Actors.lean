module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing


/-!
# Section 1 actors in the selected binary flag

The specified quotient has two-group kernel. Its extension core is therefore
the kernel itself, its odd core is trivial, and the original extension
hypotheses (A) hold. The full inverse image of the flag Borel is the common
Sylow subgroup. These facts construct the actual `RankOnePairing.Extension`.
The proved Section 1 local-normalizer theorem then identifies M_delta with
the marked parabolic. Its untilded prime-to-two residual is the full
parabolic, while its tilded residual remains `flagResidual`.

The elementary edge layer and EarlyFacts also put the triple commutator in
Z_alpha. The stronger bound by the intrinsic center of G_alpha is still the
missing source argument, not a consequence asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (A), p.828; local notation,
p.832; (1.7), pp.847--848; and (4.6.8), pp.905--908.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem kernel_pcore_top (source : LocalSource L R) :
    pCore 2 source.projection.ker = ⊤ := by
  have hp : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  exact top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)

omit [Finite M] in
/-- The extension core in Section 1 is the actual kernel in this binary setup. -/
theorem pairing_core (source : LocalSource L R) :
    extensionCore source.projection = source.projection.ker := by
  rw [extensionCore, kernel_pcore_top, ← MonoidHom.range_eq_map, range_subtype]

/-- The actual Section 1 extension, with the given quotient, flag and full Borel Sylow. -/
@[expose] noncomputable def pairingExtension (source : LocalSource L R) : Extension (M := M) := by
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  let B := borelPreimage source.projection source.flag
  have hb : IsPGroup 2 B := by
    have h := (modelBorelSylow source.flag).isPGroup'
    rw [coe_modelBorelSylow] at h
    exact h.comap_of_ker_isPGroup source.projection hk
  refine {
    base := {
      projection := source.projection
      surjective := source.projection_surjective
      flag := source.flag
      weakBN := source.weakBN
      odd_core := ?_
      odd_index := ?_
      no_supplement := ?_ }
    borel := B
    borel_eq := rfl
    sylow := (hb.to_subgroup ⊤).toSylow (by simp) }
  · apply eq_bot_of_card_eq
    rcases (hk.to_subgroup (pPrimeCore 2 source.projection.ker)).card_eq_or_dvd with h | h
    · exact h
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := 2) (G := source.projection.ker))) h)
  · have ht : pCore 2 source.projection.ker = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, hk.to_subgroup ⊤⟩)
    rw [ht, index_top]
    decide
  · intro F _
    rw [pairing_core]
    exact le_sup_right

/-- The construction retains the supplied projection literally. -/
@[simp] theorem pairingExtension_projection (source : LocalSource L R) :
    (pairingExtension source).projection = source.projection := rfl

/-- The construction retains the supplied flag literally. -/
@[simp] theorem pairingExtension_flag (source : LocalSource L R) :
    (pairingExtension source).flag = source.flag := rfl

/-- The common Section 1 Sylow is the entire preimage of the same marked Borel. -/
theorem pairingExtension_commonSylow (source : LocalSource L R) :
    commonSylow (pairingExtension source) = borelPreimage source.projection source.flag := by
  change (⊤ : Subgroup (borelPreimage source.projection source.flag)).map
    (borelPreimage source.projection source.flag).subtype = _
  rw [← MonoidHom.range_eq_map, range_subtype]

/-- The Section 1 local normalizer is the full marked parabolic. -/
theorem pairing_parabolic (source : LocalSource L R) (i : Bool) :
    localParabolic (pairingExtension source) i = parabolic source.projection source.flag i := by
  exact localParabolic_eq_parabolic (pairingExtension source)
    (by change IsPGroup 2 source.projection.ker; rw [source.projection_kernel]; exact pCore_isPGroup) i

/-- The Section 1 selected core has exactly the prescribed amalgam image. -/
theorem pairing_selectedCore (source : LocalSource L R) (i : Bool) :
    (selectedCore (pairingExtension source) i).map (embedM R) = flagKernel source i := by
  rw [selectedCore_eq_localCore, pairing_parabolic]
  rfl

/-- The untilded actor in (1.7) is the full parabolic in the binary specialization. -/
theorem pairing_untilded (source : LocalSource L R) (i : Bool) :
    (localResidual (localParabolic (pairingExtension source) i)).map (embedM R) =
      flagParabolic source i := by
  rw [pairing_parabolic, localResidual,
    primeToResidual_parabolic_eq_top source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup),
    ← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- The tilded actor in (4.6.8) retains its actual ordered residual and embedding. -/
theorem pairing_tilded (source : LocalSource L R) (i : Bool) :
    (rankOne (localParabolic (pairingExtension source) i)).map (embedM R) =
      flagResidual source i := by
  rw [pairing_parabolic]
  rfl

/-- The earlier central commutator bound already places the flag triple in Z_alpha. -/
theorem flag_triple_le_Z (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hi : flagKernel source i = Q R (beta R)) :
    ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤ Z R (alpha R) := by
  have hab : Adjacent R (alpha R) (beta R) :=
    (adjacent_iff_exists_common R _ _).mpr ⟨1, Or.inl ⟨rfl, rfl⟩⟩
  exact (commutator_mono
    ((flag_commutator_le_edgeRadius source geometry common.large_distance i hi).trans
      (edgeRadius_le_radius _ _ rfl hab))
    (V_le_Q geometry common.large_distance _ rfl)).trans (early.commutator_le_Z _ rfl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
