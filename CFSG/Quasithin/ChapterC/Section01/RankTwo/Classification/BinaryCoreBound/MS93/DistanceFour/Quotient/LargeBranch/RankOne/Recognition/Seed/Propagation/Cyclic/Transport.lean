module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic

/-!
# A cyclic generator in the literal orbit quotient

The inclusion of one ambient layer in another induces an injective linear map
between their genuine relative Z_alpha quotients. This map intertwines the
given SL3(2) actions and preserves the images and dimensions of subgroups.

Apply this to the full midpoint orbit span inside V_alpha. The local midpoint
line gives a nonzero vector fixed by the first full parabolic. Its second
parabolic orbit spans the local seed plane, and its full group orbit spans the
entire quotient. The actors here retain the original incident frame.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation p.905 and (4.6.12)(3), pp.910--911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

namespace QuotientTransfer
variable {S T : Subgroup (FreeAmalgam R)}
  (dS : LayerModule source S) (dT : LayerModule source T) (hST : S ≤ T)

private noncomputable def hom : Multiplicative dS.Space →* Multiplicative dT.Space :=
  dS.projection.liftOfSurjective dS.onto
    ⟨dT.projection.comp (inclusion hST), by
      intro x hx
      rw [dS.kernel] at hx
      change inclusion hST x ∈ dT.projection.ker
      rw [dT.kernel]
      exact hx⟩

private theorem hom_projection (x : S) :
    hom dS dT hST (dS.projection x) = dT.projection (inclusion hST x) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private noncomputable def linear : dS.Space →ₗ[ZMod 2] dT.Space :=
  (AddMonoidHom.toMultiplicative.symm (hom dS dT hST)).toZModLinearMap 2

private theorem linear_projection (x : S) :
    linear dS dT hST (dS.projection x).toAdd =
      (dT.projection (inclusion hST x)).toAdd :=
  congrArg Multiplicative.toAdd (hom_projection dS dT hST x)

private theorem injective : Function.Injective (linear dS dT hST) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  obtain ⟨x, hx⟩ := dS.onto (Multiplicative.ofAdd v)
  have he : (dT.projection (inclusion hST x)).toAdd = 0 := by
    rw [← linear_projection dS dT hST, hx]
    exact hv
  have hk : inclusion hST x ∈ dT.projection.ker := he
  rw [dT.kernel] at hk
  have hz : x ∈ dS.projection.ker := by rw [dS.kernel]; exact hk
  change v = 0
  exact (congrArg Multiplicative.toAdd hx).symm.trans hz

private theorem equivariant (hSn : stabilizer R (alpha R) ≤ normalizer S)
    (g : SL) (v : dS.Space) :
    linear dS dT hST (dS.representation g v) =
      dT.representation g (linear dS dT hST v) := by
  obtain ⟨m, rfl⟩ := source.projection_surjective g
  obtain ⟨x, hx⟩ := dS.onto (Multiplicative.ofAdd v)
  have hv : v = (dS.projection x).toAdd := (congrArg Multiplicative.toAdd hx).symm
  rw [hv]
  have hm : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  let y : S := ⟨embedM R m * x * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (hSn hm) x).mp x.property⟩
  rw [← dS.action m x y rfl, linear_projection, linear_projection]
  exact dT.action m (inclusion hST x) (inclusion hST y) rfl

private theorem map_subspace (A : Subgroup (FreeAmalgam R)) (hA : A ≤ S) :
    (dS.subspace A).map (linear dS dT hST) = dT.subspace A := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (dS.mem_subspace_iff A w).mp hw
    exact (dT.mem_subspace_iff A _).mpr
      ⟨inclusion hST x, hx, (linear_projection dS dT hST x).symm⟩
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (dT.mem_subspace_iff A v).mp hv
    let y : S := ⟨x, hA hx⟩
    refine ⟨(dS.projection y).toAdd,
      (dS.mem_subspace_iff A _).mpr ⟨y, hx, rfl⟩, ?_⟩
    exact linear_projection dS dT hST y

include hST in
private theorem subspace_finrank (A : Subgroup (FreeAmalgam R)) (hA : A ≤ S) :
    Module.finrank (ZMod 2) (dS.subspace A) =
      Module.finrank (ZMod 2) (dT.subspace A) := by
  have h1 := dS.subspace_relIndex A hA
  have h2 := dT.subspace_relIndex A (hA.trans hST)
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (h1.symm.trans h2)

end QuotientTransfer

private theorem orbitSpace_line {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL W) (H : Subgroup SL) (v : W) :
    orbitSpace ρ H (Submodule.span (ZMod 2) {v}) =
      BinaryLinearThree.ParabolicCyclic.orbitSpan ρ H v := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul]
    exact Submodule.smul_mem _ a
      (BinaryLinearThree.ParabolicCyclic.orbit_mem ρ H v g hg)
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact Submodule.subset_span ⟨g, hg, v, Submodule.subset_span rfl, rfl⟩

private theorem subspace_self {S : Subgroup (FreeAmalgam R)}
    (d : LayerModule source S) : d.subspace S = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  exact (d.mem_subspace_iff S v).mpr ⟨x, x.property, congrArg Multiplicative.toAdd hx⟩

private theorem orbitSpan_conjugateSpan (c : Vertex R) :
    orbitSpan c = conjugateSpanBy (Z R c) ((⊤ : Subgroup M).map (embedM R)) := by
  have hm : (⊤ : Subgroup M).map (embedM R) = stabilizer R (alpha R) := by
    rw [← MonoidHom.range_eq_map]
    exact (stabilizer_m_base R).symm
  rw [hm]
  apply le_antisymm
  · exact orbitSpan_le_of_normalized c _ (le_conjugateSpanBy _ _)
      (le_normalizer_conjugateSpanBy _ _)
  · exact conjugateSpanBy_le (Z_le_orbitSpan c) (orbitSpan_normalized c)

/-- The local line and plane give an actual cyclic generator in every realization
of the full orbit quotient. The parabolic actors still use the original frame. -/
theorem exists_frame_cyclic_seed [Finite M]
    {d : LayerModule source (V R (alpha R))} {f : Frame source}
    (s : CriticalSegment geometry) {x : Input (geometry := geometry) d f s.middle}
    (hlocal : LocalConsequences d f s.middle x)
    (dO : LayerModule source (orbitSpan s.middle)) :
    ∃ v : dO.Space, v ≠ 0 ∧
      (∀ g ∈ (f.parabolic false).map source.projection, dO.representation g v = v) ∧
      BinaryLinearThree.ParabolicCyclic.orbitSpan dO.representation ⊤ v = ⊤ ∧
      Module.finrank (ZMod 2) (BinaryLinearThree.ParabolicCyclic.orbitSpan
        dO.representation ((f.parabolic true).map source.projection) v) = 2 := by
  have hOV : orbitSpan s.middle ≤ V R (alpha R) :=
    orbitSpan_le_radius _ ((cosetGraph R).dist_comm.trans s.first_distance).le
  have hline : Module.finrank (ZMod 2) (dO.subspace (Z R s.middle)) = 1 :=
    (QuotientTransfer.subspace_finrank dO d hOV _ (Z_le_orbitSpan _)).trans
      hlocal.line_dimension
  have hn : dO.subspace (Z R s.middle) ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hline
    exact (by decide : (0 : ℕ) ≠ 1) hline
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hline hv hv0
  refine ⟨v, hv0, ?_, ?_, ?_⟩
  · intro g hg
    apply QuotientTransfer.injective dO d hOV
    rw [QuotientTransfer.equivariant dO d hOV (orbitSpan_normalized _)]
    have hvd : QuotientTransfer.linear dO d hOV v ∈ d.subspace (Z R s.middle) := by
      rw [← QuotientTransfer.map_subspace dO d hOV _ (Z_le_orbitSpan _)]
      exact ⟨v, hv, rfl⟩
    apply hlocal.first_fixed hvd ⟨g, ?_⟩
    rwa [f.actor_eq false]
  · have h := dO.subspace_conjugateSpan (Z R s.middle) (Z_le_orbitSpan _)
      (⊤ : Subgroup M) (by
        rw [← MonoidHom.range_eq_map]
        change Mbar R ≤ _
        simpa only [alpha, stabilizer_m_base] using orbitSpan_normalized s.middle)
    rw [← orbitSpan_conjugateSpan, subspace_self,
      map_top_of_surjective _ source.projection_surjective, hspan, orbitSpace_line] at h
    exact h.symm
  · let A := conjugateSpanBy (Z R s.middle) (f.ambient true)
    have hAO : A ≤ orbitSpan s.middle :=
      conjugateSpanBy_le (Z_le_orbitSpan _)
        ((f.ambient_le true).trans (orbitSpan_normalized _))
    have hd : Module.finrank (ZMod 2) (dO.subspace A) = 2 := by
      rw [QuotientTransfer.subspace_finrank dO d hOV A hAO]
      exact hlocal.conjugate_span ▸ hlocal.seed_dimension
    have he := dO.subspace_conjugateSpan (Z R s.middle) (Z_le_orbitSpan _)
      (f.parabolic true) ((f.ambient_le true).trans (orbitSpan_normalized _))
    rw [hspan, orbitSpace_line] at he
    exact he ▸ hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
