module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Carriers
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The original SL3(2) action on a single orbit quotient

Conjugation by the M-vertex stabilizer acts on the literal relative quotient.
The preceding (4.5.3)(ii) bound kills Q_a. The exact source projection kernel
then descends this action to the original SL3(2), retaining its conjugation
formula. Finite elementarity comes from the actual subgroup carriers.

`OrbitModule` is constructed here; it assumes no faithfulness, movement,
dimension, coordinates or orientation. Those are the remaining source steps.
The abelianness and commutator inputs are precisely the earlier orbit-geometry
and early-layer producers' conclusions.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(ii), pp.897--898,
and the proof of (4.5.4)(iii), p.899.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open NormalizerTransfer
variable {M : Type*} [Group M] {R L : Subgroup M}

/-- The literal relative quotient, independent of any chosen coordinates. -/
abbrev OrbitSpace (p : Higher.SourcePath (alpha R)) (v : Vertex R) :=
  orbitFactor p v ⧸ (hatV R (alpha R) (p.walk.getVert 6)).subgroupOf (orbitFactor p v)

/-- Constructed data on the actual quotient. Faithfulness, moving generation
and small displacement are subsequent source obligations. -/
structure OrbitModule (source : LocalSource L R) (p : Higher.SourcePath (alpha R))
    (v : Vertex R) where
  normal : ((hatV R (alpha R) (p.walk.getVert 6)).subgroupOf (orbitFactor p v)).Normal
  finite : Finite (OrbitSpace p v)
  elementary : let := normal; IsElementaryAbelian 2 (OrbitSpace p v)
  action : let := normal; SL →* MulAut (OrbitSpace p v)
  conjugation : let := normal
    ∀ (m : M) (x y : orbitFactor p v),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      action (source.projection m) (QuotientGroup.mk x) = QuotientGroup.mk y

/-- The only extra inputs are literal (4.5.3)(ii) and (4.5.4)(ii).
No quotient action, dimension or kernel is an assumed hypothesis. -/
theorem orbitModule [Finite M] (source : LocalSource L R) {geometry : Geometry R}
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    {v : Vertex R} (hv : Z R v ≤ hatV R (p.walk.getVert 6) (p.walk.getVert 8))
    (hcolor : color R v = false)
    (hab : IsMulCommutative (conjugatesIn (Z R v) (stabilizer R (alpha R))))
    (hcomm : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R)) : Nonempty (OrbitModule source p v) := by
  let A := orbitFactor p v
  let N := hatV R (alpha R) (p.walk.getVert 6)
  have hlocal : A ≤ Mbar R := by
    exact (orbitFactor_le_Q earlier p hv).trans (by
      simpa only [alpha, stabilizer_m_base] using
        (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1))
  have hA : Mbar R ≤ normalizer A := by
    simpa only [alpha, stabilizer_m_base] using orbitFactor_normalized p v
  have hN : Mbar R ≤ normalizer N := by
    change Mbar R ≤ normalizer (hatV R (alpha R) (p.walk.getVert 6))
    simpa only [alpha, stabilizer_m_base] using hatV_normalized R (alpha R) (p.walk.getVert 6)
  let hnormal : (N.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer (hlocal.trans hN)
  let : Finite (Mbar R) := Finite.of_surjective (embedM R).rangeRestrict
    (embedM R).rangeRestrict_surjective
  let : Finite A := Finite.of_injective (inclusion hlocal) (inclusion_injective _)
  let := orbitFactor_elementary earlier p hv hcolor hab
  let : IsElementaryAbelian 2 (OrbitSpace p v) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' (N.subgroupOf A))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ, hρ⟩ := exists_quotient_conjugation_action (Mbar R) A N hA hN hnormal
  have hZN : Z R (alpha R) ≤ N := Early.Z_le_hatV (R := R) rfl
    (by simpa only [p.center_eq] using p.dist (i := 4) (j := 6) (by decide) (by decide))
  have hkill := quotient_conjugation_action_kills_commutator_layer (Mbar R) A N
    (Q R (alpha R)) hnormal hA
    ((commutator_mono (orbitFactor_le_second p hv) le_rfl).trans (hcomm.trans hZN)) ρ hρ
  let μ : M →* MulAut (OrbitSpace p v) := ρ.comp (embedM R).rangeRestrict
  have hk : source.projection.ker ≤ μ.ker := by
    intro m hm
    rw [source.projection_kernel] at hm
    apply hkill
    change embedM R m ∈ Q R (alpha R)
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ hm
  let σ : SL →* MulAut (OrbitSpace p v) :=
    source.projection.liftOfSurjective source.projection_surjective ⟨μ, hk⟩
  refine ⟨⟨hnormal, inferInstance, inferInstance, σ, ?_⟩⟩
  dsimp only
  intro m x y hy
  change σ (source.projection m) (QuotientGroup.mk' (N.subgroupOf A) x) = _
  dsimp only [σ]
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  change ρ ((embedM R).rangeRestrict m) (QuotientGroup.mk' (N.subgroupOf A) x) = _
  exact (hρ ⟨embedM R m, ⟨m, rfl⟩⟩ x).trans
    (congrArg (QuotientGroup.mk' (N.subgroupOf A)) (Subtype.ext hy.symm))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
