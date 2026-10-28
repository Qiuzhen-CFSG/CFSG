module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Preliminary.NaturalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import Theory.GroupTheory.SylowKernelCore

/-!
# Quotient lines and their full radical fixed spaces

Every binary line is transported to the first coordinate axis. The actual
point-parabolic radical fixes exactly that axis. Natural-factor coordinates
then preserve subgroup order, parabolic normalization and commutator-fixedness.
These transports keep the original coordinate kernel and arbitrary natural
marking; they are used in the adjacent source parabolic comparison.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.898.
-/

@[expose] public section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.LineModel
open Escape.Propagation.Backward.Products.Selection.Choices
open FiniteGeometry
private def line : Subgroup Space where
  carrier := {v | v.toAdd 1 = 0 ∧ v.toAdd 2 = 0}
  one_mem' := by simp
  mul_mem' := by intro x y hx hy; exact ⟨by change x.toAdd 1 + y.toAdd 1 = 0; rw [hx.1,hy.1,add_zero], by change x.toAdd 2 + y.toAdd 2 = 0; rw [hx.2,hy.2,add_zero]⟩
  inv_mem' := by intro x hx; exact ⟨by change -x.toAdd 1 = 0; rw [hx.1,neg_zero], by change -x.toAdd 2 = 0; rw [hx.2,neg_zero]⟩

private theorem line_shape (v : Space) : v ∈ line ↔ v = 1 ∨ v = e0 := by
  have h : ∀ v : Space, (v.toAdd 1 = 0 ∧ v.toAdd 2 = 0) ↔ v = 1 ∨ v = e0 := by decide
  exact h v

private instance : DecidablePred (· ∈ line) := fun v =>
  inferInstanceAs (Decidable (v.toAdd 1 = 0 ∧ v.toAdd 2 = 0))

private theorem line_card : Nat.card line = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem line_stabilizer : planeStabilizer line = PSL3Two.pointParabolicSL := by
  ext g
  rw [mem_planeStabilizer_iff, PSL3Two.mem_pointParabolicSL_iff]
  constructor
  · intro h
    have h0 := h e0 ((line_shape _).mpr (Or.inr rfl))
    have he : ∀ i, (modelAction g e0).toAdd i = g.val i 0 := by
      intro i; simp [e0, mulVec, dotProduct, Fin.sum_univ_three]
    exact ⟨(he 1).symm.trans h0.1, (he 2).symm.trans h0.2⟩
  · intro h v hv
    rcases (line_shape v).mp hv with rfl | rfl
    · rw [map_one]; exact line.one_mem
    · constructor
      · simpa [e0, mulVec, dotProduct, Fin.sum_univ_three] using h.1
      · simpa [e0, mulVec, dotProduct, Fin.sum_univ_three] using h.2

private theorem line_transitive (E : Subgroup Space) (hE : Nat.card E = 2) :
    ∃ g : SL, move g line = E := by
  obtain ⟨u, hune, hunique⟩ := (Nat.card_eq_two_iff' (1 : E)).mp hE
  have hu0 : u.val.toAdd ≠ 0 := fun h => hune (Subtype.ext h)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq PSL3Two.PSL
    PSL3Two.flagPoint (⟨u.val.toAdd, hu0⟩ : PSL3Two.Fano.Point)
  obtain ⟨g, rfl⟩ := PSL3Two.project_surjective k
  rw [PSL3Two.Fano.project_smul_point] at hk
  have hg : modelAction g e0 = u.val := congrArg Subtype.val hk
  refine ⟨g, eq_of_le_of_card_ge ?_ ?_⟩
  · rintro v ⟨w, hw, rfl⟩
    rcases (line_shape w).mp hw with rfl | rfl
    · simpa only [MonoidHom.coe_coe, map_one] using E.one_mem
    · exact hg ▸ u.property
  · rw [move_card, line_card, hE]

theorem line_stabilizer_ne_top (E : Subgroup Space) (hE : Nat.card E = 2) :
    planeStabilizer E ≠ ⊤ := by
  obtain ⟨g, rfl⟩ := line_transitive E hE
  rw [planeStabilizer_move, line_stabilizer]
  intro h
  have he := congrArg (Subgroup.comap (MulAut.conj g).toMonoidHom) h
  rw [comap_map_eq_self_of_injective (MulAut.conj g).injective, comap_top] at he
  exact PSL3Two.pointParabolicSL_ne_top he


/-- The complete two-core of a line stabilizer fixes exactly that line. -/
theorem fixed_core_line (A : Subgroup Space) (hA : Nat.card A = 2) :
    fixedSpace ((planeStabilizer A).pCoreIn 2) = A := by
  obtain ⟨g, rfl⟩ := line_transitive A hA
  rw [planeStabilizer_move, ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    line_stabilizer, Matrix.PSL3Two.MarkedProduct.pointParabolic_core,
    fixedSpace_conjugate]
  apply congrArg (move g)
  exact RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.fixed_pointCore


variable {G : Type*} [Group G] {π : G →* SL} {W N : Subgroup G}

noncomputable def coordinateImage (n : RankOnePairing.NaturalFactor π ⊤ W N)
    (A : Subgroup G) : Subgroup Space := (A.subgroupOf W).map n.coordinates

theorem coordinateImage_card (n : RankOnePairing.NaturalFactor π ⊤ W N)
    (A : Subgroup G) (hAW : A ≤ W) :
    Nat.card (coordinateImage n A) = N.relIndex A := by
  rw [coordinateImage, ← relIndex_ker,n.kernel,relIndex_subgroupOf hAW]

theorem coordinateImage_normalized (n : RankOnePairing.NaturalFactor π ⊤ W N)
    (A P : Subgroup G) (hPA : P ≤ normalizer A) :
    P.map (n.marking.toMonoidHom.comp π) ≤ planeStabilizer (coordinateImage n A) := by
  rintro g ⟨g,hg,rfl⟩
  apply (mem_planeStabilizer_iff _ _).mpr
  rintro v ⟨x,hx,rfl⟩
  let y : W := ⟨g*x*g⁻¹,le_normalizer_iff.mp n.normalized g (mem_top _) x x.property⟩
  have hy : y ∈ A.subgroupOf W := le_normalizer_iff.mp hPA g hg x hx
  have he : n.coordinates y = modelAction ((n.marking.toMonoidHom.comp π) g) (n.coordinates x) :=
    congrArg Multiplicative.ofAdd (n.action g (mem_top _) x y rfl)
  rw [← he]
  exact mem_map_of_mem _ hy

/-- A maximal actual actor preserving a quotient line is its full stabilizer. -/
theorem coordinateImage_stabilizer (n : RankOnePairing.NaturalFactor π ⊤ W N)
    (hπ : Function.Surjective π) (A P : Subgroup G)
    (hP : IsCoatom P) (hPA : P ≤ normalizer A)
    (hcard : Nat.card (coordinateImage n A) = 2) :
    P.map (n.marking.toMonoidHom.comp π) = planeStabilizer (coordinateImage n A) := by
  let q := n.marking.toMonoidHom.comp π
  have hq : Function.Surjective q := n.marking.surjective.comp hπ
  have hle : P ≤ (planeStabilizer (coordinateImage n A)).comap q :=
    map_le_iff_le_comap.mp (coordinateImage_normalized n A P hPA)
  have hproper : (planeStabilizer (coordinateImage n A)).comap q ≠ ⊤ := by
    intro hh
    have hm := congrArg (Subgroup.map q) hh
    rw [map_comap_eq_self_of_surjective hq,map_top_of_surjective _ hq] at hm
    exact line_stabilizer_ne_top _ hcard hm
  have he : P = (planeStabilizer (coordinateImage n A)).comap q := by
    by_contra hn
    exact hproper (hP.2 _ (lt_of_le_of_ne hle hn))
  rw [he,map_comap_eq_self_of_surjective hq]

/-- The literal commutator-kernel bound makes the coordinate image fixed. -/
theorem coordinateImage_fixed_of_commutator
    (n : RankOnePairing.NaturalFactor π ⊤ W N)
    (A P : Subgroup G) (hc : ⁅A,P⁆ ≤ N) :
    coordinateImage n A ≤ fixedSpace (P.map (n.marking.toMonoidHom.comp π)) := by
  rintro v ⟨x,hx,rfl⟩ g ⟨g,hg,rfl⟩
  let y : W := ⟨g*x*g⁻¹,le_normalizer_iff.mp n.normalized g (mem_top _) x x.property⟩
  have he : n.coordinates y = modelAction ((n.marking.toMonoidHom.comp π) g) (n.coordinates x) :=
    congrArg Multiplicative.ofAdd (n.action g (mem_top _) x y rfl)
  rw [← he]
  have hk : y*x⁻¹ ∈ n.coordinates.ker := by
    rw [n.kernel]
    change g*(x:G)*g⁻¹*(x:G)⁻¹ ∈ N
    exact hc ((commutator_comm P A).le (commutator_mem_commutator hg hx))
  have hz : n.coordinates y * (n.coordinates x)⁻¹ = 1 := by
    simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hk
  exact mul_inv_eq_one.mp hz

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Third.LineModel
