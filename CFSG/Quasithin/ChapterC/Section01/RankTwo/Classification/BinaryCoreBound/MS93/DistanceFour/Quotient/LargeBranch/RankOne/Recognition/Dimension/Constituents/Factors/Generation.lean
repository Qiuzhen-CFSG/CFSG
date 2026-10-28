module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Parabolics

public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# Full commutator generation from the literal Y-fixation estimates

The earlier section calculation places the actual edge star in Y. The
Estimates fields Y_fixed and span_fixed make its image fixed by the first
ordered residual and the second intrinsic core. Their projected join is
the full first parabolic for the supplied frame. This parabolic has index
seven in the literal SL3(2) quotient.

Averaging a parabolic-fixed vector over those seven cosets gives a globally
fixed vector congruent to it modulo the commutator subspace. The starred
fixed space is zero, so the edge image lies in that commutator subspace.
Its actual stabilizer conjugates generate the star, proving fullness.
All preimages retain the supplied quotient projection and its Z_alpha kernel.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(1)--(2) and (5), printed pp.910--911, with the incident
actor generation on p.910. This is a direct alternative to the FF route
for the intermediate, unoriented constituent conclusion.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension

private theorem fixed_le_moved_of_odd_index {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (P : Subgroup G)
    (hindex : Odd P.index) (hzero : fixedSpace ρ ⊤ = ⊥) :
    fixedSpace ρ P ≤ subspaceCommutator ρ ⊤ ⊤ := by
  classical
  let : P.FiniteIndex := ⟨by obtain ⟨n, hn⟩ := hindex; omega⟩
  let := Fintype.ofFinite (G ⧸ P)
  intro u hu
  change ∀ b : P, ρ b u = u at hu
  let f : G ⧸ P → W := fun q => ρ q.out u
  have hf (g : G) : f (QuotientGroup.mk g) = ρ g u := by
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul P g
    change ρ (QuotientGroup.mk g : G ⧸ P).out u = _
    rw [hb, map_mul, Module.End.mul_apply, hu b]
  have hcov (g : G) (q : G ⧸ P) : f (g • q) = ρ g (f q) := by
    induction q using Quotient.inductionOn with
    | h a =>
      change f (QuotientGroup.mk (g * a)) = _
      rw [hf, hf, map_mul, Module.End.mul_apply]
  let v : W := ∑ q, f q
  have hv : v = 0 := by
    have hvfix : v ∈ fixedSpace ρ ⊤ := by
      intro g
      change ρ g.val (∑ q, f q) = ∑ q, f q
      rw [map_sum]
      simp_rw [← hcov]
      exact Equiv.sum_comp (MulAction.toPerm g.val) f
    rwa [hzero, Submodule.mem_bot] at hvfix
  have hodd : (Fintype.card (G ⧸ P) : ZMod 2) = 1 := by
    have hc : Odd (Fintype.card (G ⧸ P)) := by
      simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hindex
    obtain ⟨n, hn⟩ := hc
    rw [hn]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  have hsum : (∑ q : G ⧸ P, u) = u := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod 2), hodd, one_smul]
  have hd : v - u ∈ subspaceCommutator ρ ⊤ ⊤ := by
    rw [show v - u = ∑ q : G ⧸ P, (f q - u) by rw [Finset.sum_sub_distrib, hsum]]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.subset_span ⟨q.out, mem_top _, u, Submodule.mem_top, rfl⟩
  simpa only [hv, zero_sub, Submodule.neg_mem_iff] using hd

private theorem fixed_by_join {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL W) (H K : Subgroup SL) (v : W)
    (hH : v ∈ fixedSpace ρ H) (hK : v ∈ fixedSpace ρ K) :
    v ∈ fixedSpace ρ (H ⊔ K) := by
  let F : Subgroup SL := {
    carrier := {a | ρ a v = v}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change ρ (a * b) v = v
      change ρ a v = v at ha
      change ρ b v = v at hb
      rw [map_mul, Module.End.mul_apply, hb, ha]
    inv_mem' := by
      intro a ha
      change ρ a⁻¹ v = v
      change ρ a v = v at ha
      simpa only [ρ.inv_self_apply] using (congrArg (ρ a⁻¹) ha).symm }
  have h : H ⊔ K ≤ F := sup_le (fun a ha => hH ⟨a, ha⟩) (fun a ha => hK ⟨a, ha⟩)
  exact fun g => h g.property

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem star_subspace_fixed_of_commutator
    (d : LayerModule source (VStar R geometry (alpha R) (beta R)))
    (T : Subgroup (FreeAmalgam R)) (H : Subgroup M)
    (hc : ⁅T, H.map (embedM R)⁆ ≤ Z R (alpha R)) :
    d.subspace T ≤ fixedSpace d.representation (H.map source.projection) := by
  rw [commutator_comm] at hc
  intro v hv g
  obtain ⟨x, hx, rfl⟩ := (d.mem_subspace_iff T v).mp hv
  obtain ⟨m, hm, he⟩ := g.property
  change d.representation (g : SL) (d.projection x).toAdd = (d.projection x).toAdd
  rw [← he]
  have hnorm : embedM R m ∈ normalizer (VStar R geometry (alpha R) (beta R)) := by
    apply Flags.star_normalized geometry
    rw [alpha, stabilizer_m_base]
    exact ⟨m,rfl⟩
  exact (d.fixed_iff_commutator_mem m hnorm x).mpr
    (hc (commutator_mem_commutator (mem_map_of_mem _ hm) hx))

private theorem first_actor_odd_index (f : Seed.Frame source) :
    Odd ((f.actor false).map source.projection).index := by
  rw [f.actor_eq]
  have he : (f.parabolic false).map source.projection = modelParabolic f.flag f.first :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  rw [he]
  have hc := (modelParabolic f.flag f.first).index_mul_card
  rw [card_modelParabolic, Matrix.PSL3Two.card_SL] at hc
  have hi : (modelParabolic f.flag f.first).index = 7 := by omega
  rw [hi]
  decide

/-- The actual starred action is generated by its full-group commutators,
using the radius/section geometry and the supplied Y-fixation estimates. -/
theorem star_full_of_estimates (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hest : Estimates d f s) :
    subspaceCommutator (starRepresentation (geometry := geometry) d).toRepresentation ⊤ ⊤ = ⊤ := by
  let ds := starLayer (geometry := geometry) d
  let C := subspaceCommutator ds.representation ⊤ ⊤
  have hYfixed : ds.subspace (Sections.fixedPreimage s.middle) ≤
      fixedSpace ds.representation ((f.actor false).map source.projection) := by
    rw [Seed.actor_image_generation]
    intro v hv
    exact fixed_by_join ds.representation _ _ v
      (star_subspace_fixed_of_commutator ds _ _ hest.Y_fixed hv)
      (star_subspace_fixed_of_commutator ds _ _
        ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans hest.span_fixed) hv)
  have hE : edgeStar R geometry (alpha R) (beta R) ≤ ds.preimage C := by
    intro x hx
    have hxS := Flags.edgeStar_le_star geometry (alpha R) (beta R) hx
    apply (ds.mem_preimage_iff C x).mpr
    refine ⟨hxS, ?_⟩
    apply fixed_le_moved_of_odd_index ds.representation _ (first_actor_odd_index f)
      (star_fixed_eq_bot common radius d)
    apply hYfixed
    exact (ds.mem_subspace_iff _ _).mpr ⟨⟨x,hxS⟩,
      Escape.edgeStar_le_fixedPreimage common radius hb s hbc d hx, rfl⟩
  have hnorm : stabilizer R (alpha R) ≤ normalizer (ds.preimage C) := by
    have hS : (⊤ : Subgroup M).map (embedM R) ≤ normalizer
        (VStar R geometry (alpha R) (beta R)) := by
      rw [← MonoidHom.range_eq_map]
      simpa only [alpha, stabilizer_m_base, Mbar] using
        Flags.star_normalized geometry (alpha R) (beta R)
    have hn := ds.preimage_normalized C ⊤ hS (fun m _ v hv =>
      (subspaceCommutator_invariant ds.representation ⊤ ⊤ (mem_top (source.projection m)) v).mpr hv)
    simpa only [← MonoidHom.range_eq_map, alpha, stabilizer_m_base, Mbar] using hn
  have hSC : VStar R geometry (alpha R) (beta R) ≤ ds.preimage C :=
    iSup_conjugates_le_of_le_normalizer _ _ _ hE hnorm
  apply top_unique
  intro v _
  obtain ⟨x, rfl⟩ := ds.onto (Multiplicative.ofAdd v)
  exact ((ds.mem_preimage_iff C x).mp (hSC x.property)).2
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
