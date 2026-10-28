module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Basic

/-!
# Natural coordinates on the incident local span

The given flag section has an onto natural-plane coordinate map whose exact
kernel is the fixed preimage for the tilded residual. Its intersection with
D_alpha lies in that kernel, since D_alpha centralizes the global tilded
residual. The coordinate map therefore descends through the actual D_alpha
quotient. Faithfulness of the natural plane also makes the actor projection
descend, preserving its surjectivity and the conjugation equation.

The local span contains the displacement of the whole first actor. Every
vector of the binary natural plane is one conjugation difference, so restricting
the descended coordinates to that span remains onto. The denominator is the
transported flag fixed preimage; comparison with the global fixed preimage is
kept separate.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8)(1), (3), printed pp.905--906, and (1.7)(i), pp.847--848.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Coordinates

-- Every natural-plane vector is a single displacement. This checks only the
-- four binary vectors and the six elements of the literal SL₂(2).
private theorem plane_displacement : ∀ v : Fin 2 → ZMod 2,
    ∃ a : SL2, ∃ w : Fin 2 → ZMod 2, a.val.mulVec w - w = v := by decide

variable {G G' : Type*} [Group G] [Group G'] {K H N : Subgroup G}

-- The quotient kernel acts trivially on the coordinate quotient. Since those
-- coordinates are onto, faithfulness forces its actor projection to be trivial.
private theorem projection_kills (n : RankOnePairing.RankOneFactor K H N)
    (f : G →* G') (hk : H ⊓ f.ker ≤ N) :
    (f.subgroupMap K).ker ≤ n.projection.ker := by
  intro g hg
  have hg0 : f (g : G) = 1 := congrArg Subtype.val hg
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x, hx⟩ := n.coordinates_surjective (Multiplicative.ofAdd v)
  have hy : (g : G) * (x : G) * (g : G)⁻¹ ∈ H :=
    (mem_normalizer_iff.mp (n.normalized g.property) _).mp x.property
  let y : H := ⟨_, hy⟩
  have hd : y * x⁻¹ ∈ n.coordinates.ker := by
    rw [n.kernel]
    apply hk
    refine ⟨H.mul_mem hy (H.inv_mem x.property), ?_⟩
    change f ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) = 1
    simp only [map_mul, map_inv, hg0, one_mul, inv_one, mul_one, mul_inv_cancel]
  have he : n.coordinates y = n.coordinates x := by
    have hh := MonoidHom.mem_ker.mp hd
    rw [map_mul, map_inv, mul_inv_eq_one] at hh
    exact hh
  have ha := n.action g x y rfl
  rw [he, hx] at ha
  simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, toAdd_ofAdd] using ha.symm

-- Descend both homomorphisms, retaining the literal image of the denominator.
private noncomputable def mapFactor (n : RankOnePairing.RankOneFactor K H N)
    (f : G →* G') (hNH : N ≤ H) (hk : H ⊓ f.ker ≤ N) :
    RankOnePairing.RankOneFactor (K.map f) (H.map f) (N.map f) := by
  let p := (f.subgroupMap K).liftOfSurjective (f.subgroupMap_surjective K)
    ⟨n.projection, projection_kills n f hk⟩
  have hc : (f.subgroupMap H).ker ≤ n.coordinates.ker := by
    intro x hx
    rw [n.kernel]
    exact hk ⟨x.property, congrArg Subtype.val hx⟩
  let c := (f.subgroupMap H).liftOfSurjective (f.subgroupMap_surjective H)
    ⟨n.coordinates, hc⟩
  have hp (x : K) : p (f.subgroupMap K x) = n.projection x := by
    exact MonoidHom.liftOfRightInverse_comp_apply ..
  have hc' (x : H) : c (f.subgroupMap H x) = n.coordinates x := by
    exact MonoidHom.liftOfRightInverse_comp_apply ..
  refine {
    projection := p
    surjective := ?_
    coordinates := c
    coordinates_surjective := ?_
    kernel := ?_
    normalized := (map_mono n.normalized).trans (le_normalizer_map f)
    action := ?_ }
  · intro a
    obtain ⟨x, rfl⟩ := n.surjective a
    exact ⟨_, hp x⟩
  · intro a
    obtain ⟨x, rfl⟩ := n.coordinates_surjective a
    exact ⟨_, hc' x⟩
  · ext x
    obtain ⟨y, rfl⟩ := f.subgroupMap_surjective H x
    change c (f.subgroupMap H y) = 1 ↔ f (y : G) ∈ N.map f
    rw [hc']
    constructor
    · intro hy
      have hn : y ∈ n.coordinates.ker := hy
      rw [n.kernel] at hn
      exact mem_map_of_mem f hn
    · rintro ⟨z, hz, he⟩
      have ht : y * (⟨z, hNH hz⟩ : H)⁻¹ ∈ n.coordinates.ker := by
        rw [n.kernel]
        apply hk
        refine ⟨H.mul_mem y.property (H.inv_mem (hNH hz)), ?_⟩
        change f ((y : G) * z⁻¹) = 1
        rw [map_mul, map_inv, he, mul_inv_cancel]
      have hz' : (⟨z, hNH hz⟩ : H) ∈ n.coordinates.ker := by rwa [n.kernel]
      have hh := n.coordinates.ker.mul_mem ht hz'
      exact MonoidHom.mem_ker.mp (by simpa only [inv_mul_cancel_right] using hh)
  · intro g x y hy
    obtain ⟨g₀, rfl⟩ := f.subgroupMap_surjective K g
    obtain ⟨x₀, rfl⟩ := f.subgroupMap_surjective H x
    have hz : (g₀ : G) * (x₀ : G) * (g₀ : G)⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (n.normalized g₀.property) _).mp x₀.property
    let z : H := ⟨_, hz⟩
    have hy' : f.subgroupMap H z = y := by
      apply Subtype.ext
      change f ((g₀ : G) * (x₀ : G) * (g₀ : G)⁻¹) = (y : G')
      rw [map_mul, map_mul, map_inv]
      exact hy.symm
    rw [← hy', hc', hc', hp]
    exact n.action g₀ x₀ z rfl

-- Containing all displacement vectors suffices for the restricted coordinates
-- to be onto; the exact kernel then restricts without changing its denominator.
private noncomputable def restrictFactor (n : RankOnePairing.RankOneFactor K H N)
    (S : Subgroup G) (hSH : S ≤ H) (hKS : K ≤ normalizer S)
    (hmove : ⁅H,K⁆ ≤ S) : RankOnePairing.RankOneFactor K S N := by
  let c := n.coordinates.comp (inclusion hSH)
  refine {
    projection := n.projection
    surjective := n.surjective
    coordinates := c
    coordinates_surjective := ?_
    kernel := ?_
    normalized := hKS
    action := ?_ }
  · intro v
    obtain ⟨a, w, haw⟩ := plane_displacement v.toAdd
    obtain ⟨g, hg⟩ := n.surjective a
    obtain ⟨x, hx⟩ := n.coordinates_surjective (Multiplicative.ofAdd w)
    have hy : (g : G) * (x : G) * (g : G)⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (n.normalized g.property) _).mp x.property
    let y : H := ⟨_, hy⟩
    have hz : (y : G) * (x : G)⁻¹ ∈ S := by
      apply hmove
      rw [commutator_comm]
      exact commutator_mem_commutator g.property x.property
    refine ⟨⟨_, hz⟩, ?_⟩
    change n.coordinates (y * x⁻¹) = v
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv]
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [n.action g x y rfl, hg, hx, toAdd_ofAdd]
    exact haw
  · ext x
    change inclusion hSH x ∈ n.coordinates.ker ↔ _
    rw [n.kernel]
    rfl
  · intro g x y hy
    exact n.action g (inclusion hSH x) (inclusion hSH y) hy

private theorem map_localGenerated (f : G →* G') (P X : Subgroup G) (hXP : X ≤ P) :
    (RankOnePairing.localGenerated P X).map f =
      RankOnePairing.localGenerated (P.map f) (X.map f) := by
  open RankOnePairing RankOnePairing.Incidence in
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply localGenerated_le_of_normalizes
      · exact ((map_le_iff_le_comap.mp (localGenerated_normalized (P.map f) (X.map f))).trans
          (le_normalizer_comap f))
      · exact map_le_iff_le_comap.mp (le_localGenerated _ _ (map_mono hXP))
    · apply localGenerated_le_of_normalizes
      · exact (map_mono (localGenerated_normalized P X)).trans (le_normalizer_map f)
      · exact map_mono (le_localGenerated P X hXP)

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem fixedCore_inf_le_denominator (source : LocalSource L R) (i : Bool) :
    V R (beta R) ⊓ fixedCore R (alpha R) ≤ flagFixedPreimage source i := by
  apply le_commutatorPreimage inf_le_left
  apply le_trans (le_of_eq (commutator_eq_bot_iff_le_centralizer.mpr ?_)) bot_le
  intro x hx y hy
  apply hx.2.2 y
  rw [← flagResidual_sup source]
  cases i
  · exact mem_sup_left hy
  · exact mem_sup_right hy

/-- The incident local span has actual natural coordinates after quotienting
by D_alpha, with the transported flag denominator as its exact kernel. -/
theorem rankOneFactor_nonempty (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (d : M) (hd : flagIncident source i 1 d) :
    let E := Quotient.extension source (representative source i d hd)
    let P := RankOnePairing.localParabolic E i
    Nonempty (RankOnePairing.RankOneFactor (RankOnePairing.localResidual P)
      (RankOnePairing.localGenerated P (Quotient.seed source i d)) (sectionKernel source i)) := by
  let m := representative source i d hd
  let P := RankOnePairing.localParabolic (Transport.extension source) i
  let H := pull m (V R (beta R))
  let N := pull m (flagFixedPreimage source i)
  let S := pull m (Pairing.localSpan source i d)
  let f := Quotient.qmap (R := R) m
  have hV := edgeRadius_le_stabilizer geometry hlarge
  have n : RankOnePairing.RankOneFactor P H N := by
    change RankOnePairing.RankOneFactor P H (pull m (flagFixedPreimage source i))
    rw [flagFixedPreimage, pull_commutatorPreimage m _ _ _ hV
      ((flagResidual_le source i).trans (flagParabolic_le source i))
      (hV.trans (Z_normalized R _)), ← map_first_residual source i d hd, pull_map]
    exact firstNatural source geometry hlarge i natural d hd
  have hNH : N ≤ H := comap_mono (flagFixedPreimage_bounds source i).2
  have hk : H ⊓ f.ker ≤ N := by
    rw [show f.ker = pull m (fixedCore R (alpha R)) from Quotient.qmap_kernel m]
    exact comap_mono (fixedCore_inf_le_denominator source i)
  let nq := mapFactor n f hNH hk
  have hS : S ≤ H := comap_mono (localSpan_le_edgeRadius source geometry hlarge i hkernel d hd)
  have hnorm : P ≤ normalizer S := by
    have hn := pull_normalizes m _ _
      (RankOnePairing.Incidence.localGenerated_normalized (flagParabolic source i)
        (Pairing.seed source i d))
    change pull m (flagParabolic source i) ≤ normalizer S at hn
    rw [← map_first_actor source i d hd, pull_map] at hn
    exact hn
  have hmove : ⁅H,P⁆ ≤ S := by
    have hh := comap_mono (f := embedding R m)
      (actor_moving_le_localSpan source geometry hlarge i hkernel d hd)
    change pull m ⁅V R (beta R), flagParabolic source i⁆ ≤ S at hh
    rw [pull_commutator m _ _ hV (flagParabolic_le source i),
      ← map_first_actor source i d hd, pull_map] at hh
    exact hh
  have hseed : Pairing.seed source i d ≤ flagParabolic source i :=
    (Pairing.seed_le_firstLayer source geometry hlarge i hkernel d hd).trans
      (edgeRadius_le_flagParabolic source geometry hlarge i hkernel)
  have hclosure : RankOnePairing.localGenerated P (pull m (Pairing.seed source i d)) = S := by
    apply map_injective (embedding_injective m)
    have hp : P = pull m (flagParabolic source i) := by
      rw [← map_first_actor source i d hd, pull_map]
    rw [hp, map_pull_localGenerated m _ _ (flagParabolic_le source i) hseed,
      map_pull m _ ((localSpan_le_edgeRadius source geometry hlarge i hkernel d hd).trans hV)]
    rfl
  have himage : S.map f = RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source m) i) (Quotient.seed source i d) := by
    rw [← hclosure, map_localGenerated f P _]
    · rw [show P.map f = RankOnePairing.localParabolic (Quotient.extension source m) i from
          Quotient.map_parabolic source m i, Quotient.map_pull_qmap]
      rfl
    · rw [show P = pull m (flagParabolic source i) by
        rw [← map_first_actor source i d hd, pull_map]]
      exact comap_mono hseed
  have nm := restrictFactor nq (S.map f) (map_mono hS)
    ((map_mono hnorm).trans (le_normalizer_map f))
    (by rw [← map_commutator]; exact map_mono hmove)
  dsimp only at ⊢
  rw [Quotient.localResidual_eq_parabolic]
  change Nonempty (RankOnePairing.RankOneFactor
    (RankOnePairing.localParabolic (Quotient.extension source m) i)
    (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source m) i) (Quotient.seed source i d))
    (Quotient.image (flagFixedPreimage source i)))
  have hp : P.map f = RankOnePairing.localParabolic (Quotient.extension source m) i :=
    Quotient.map_parabolic source m i
  have hn : N.map f = Quotient.image (flagFixedPreimage source i) := Quotient.map_pull_qmap m _
  rw [← himage, ← hp, ← hn]
  exact ⟨nm⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Coordinates
