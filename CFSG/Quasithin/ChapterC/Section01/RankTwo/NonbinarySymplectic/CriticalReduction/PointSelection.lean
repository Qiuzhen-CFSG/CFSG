module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerSelection

/-!
# The full point-mover branch at a critical root

If the actual small-mover join has fixed index above q squared, the
unique-maximum alternative is impossible. The multiple-maximum theorem
then identifies the join with the entire replacement edge and its image
with the full point radical, in one exact natural-index marking.

The critical root calculation in that marking supplies a full long root.
The point radical and a conjugate of this root generate Sp4; perfectness
lifts the conjugator into the original local residual, and the full Q
kernel lifts generation to the whole vertex stabilizer. Every field degree
and central attachment is retained. PointSelectedPaths applies this
one-root selector to the actual replacement graph.

This is the large-movement root subcase of MS93 (5.5)(c), printed
pp.915--917. It does not assert the unequal-neighbor cross-mover clause or
exclude the trapped-root case of (5.7).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers

private theorem quadratic_of_displacement_line {F : Type*} [Field F]
    (A : Subgroup (Sp F)) (hd : Module.finrank F (displacementSpace A) = 1) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
  have hn : displacementSpace A ≠ ⊥ := by
    intro hh
    rw [hh,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  have hperp : displacementSpace A ≤ (form F).orthogonal (displacementSpace A) := by
    intro x hx y hy
    rw [hs] at hx hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [TwoLocalCover.form_alternating.self_eq_zero]
  rw [orthogonal_displacementSpace] at hperp
  intro x hx y hy w
  exact hperp (Coinvariants.sub_mem_ker
    (ρ := (symplecticNatural 2).comp A.subtype) ⟨y,hy⟩ w) x hx

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Above the small fixed-index bound the actual join is the entire edge,
whose image is the full point radical in the same natural-index marking. -/
theorem Input.replacement_large_movement_point_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2) = Q d.radical t ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f =
          (CentralRootGeometry.wing false).map unipotent.subtype := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hglobal,hidx,_⟩ :=
    h.replacement_small_mover_quadratic_coordinates d geometry hb ha hat
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card B.Carrier^2)
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hTi : T.map f ≤ unipotent.subtype.range := by simpa only [range_subtype] using hTf
  rcases Degree.Quotient.maximal_singleton_or_point_radical U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx with ⟨E,hE,hJE⟩ | ⟨hpoint,_,hJT,_⟩
  · have he : E ∈ Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card B.Carrier^2) :=
      hE ▸ Set.mem_singleton E
    have hi := he.1.2.2
    rw [←hJE] at hi
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ J
    rw [hUT,hjoin] at hh
    rw [←hh,hcard] at hi
    exact (hJm.not_ge hi).elim
  · refine ⟨B,hB,f,hf,hfQ,hglobal,?_,?_⟩
    · change J = T at hJT
      rw [←hjoin,hJT,hTT]
    · rw [←Degree.Quotient.coordinates_map f unipotent.subtype T hTi,hpoint]

/-- The large-movement join and the original field-sized critical endpoint
generate the whole vertex stabilizer after one residual conjugation.
The same conjugator works for every neighboring mover: equal orders force
all of them to equal the full edge. -/
theorem Input.replacement_large_movement_root_generator
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ g ∈ Ltilde d.radical a, ∀ c : Vertex d.radical, Adjacent d.radical c t →
      (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom ⊔
          Z d.radical z = stabilizer d.radical a := by
  obtain ⟨B,hB,f,hf,hfQ,hindex,hJT,hpoint⟩ :=
    h.replacement_large_movement_point_coordinates d geometry hb path.start_color hat hJm
  let S := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf S
  let A := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  obtain ⟨hc,hd⟩ := h.replacement_small_critical_image_dimensions d path hb hsmall B hB f hfQ hindex
  obtain ⟨r,hr⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one (A.map f) hc hd
    (quadratic_of_displacement_line (A.map f) hd)
  obtain ⟨g₀,hgen₀⟩ := SelectedGeneration.exists_point_root_generator (T.map f) (A.map f)
    ⟨1,by
      rw [show (MulAut.conj (1 : Sp B.Carrier)).toMonoidHom = MonoidHom.id _ by
        apply MonoidHom.ext
        intro y
        change 1*y*1⁻¹=y
        group,Subgroup.map_id]
      exact hpoint⟩ ⟨r,hr⟩
  have hL : L₀.map f = ⊤ := by
    have he : L₀ = pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two (by
      rw [B.card_eq,hB]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L₀.map f by rw [hL]; trivial)
  have hkT : f.ker ≤ T := by
    intro y hy
    have hyQ : y.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hy
    have ht : color d.radical t = true := by
      have hh := adjacent_color_ne d.radical hat
      rw [path.start_color] at hh
      cases ht : color d.radical t <;> simp_all
    exact Q_le_adjacent_h d.radical ht hat hyQ
  have hkg : f.ker ≤ T.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hkT
    simpa only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq] using hh
  have hgen : T.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
    have hm : (T.map (MulAut.conj g).toMonoidHom ⊔ A).map f = ⊤ := by
      rwa [Subgroup.map_sup,Subgroup.image_conjugate,hfg]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkg.trans le_sup_left),comap_top] at hh
  have hwhole := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.image_conjugate,map_subgroupOf_eq_of_le hTS,
    map_subgroupOf_eq_of_le hzS,←MonoidHom.range_eq_map,range_subtype] at hwhole
  refine ⟨g.val,hg,?_⟩
  intro c hct
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  have hc := small_mover_neighbor_card_eq d.radical hat hct (Nat.card F^2)
  rw [hJT] at hc
  have hJc : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) = Q d.radical t :=
    eq_of_le_of_card_ge (Subgroup.SmallMover.join_le _ _ _ _) hc.le
  rw [hJc]
  exact hwhole

/-- On the actual first edge, the same one-root selector satisfies the
full original edge-layer fixed-subgroup clause for every neighboring mover.
Thus the two source selections may coincide in this point-radical branch. -/
theorem Input.replacement_large_movement_root_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a)) :
    ∃ g ∈ Ltilde d.radical a, ∀ c : Vertex d.radical, Adjacent d.radical c t →
      let Jc := (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom
      Jc ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (Jc : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,hg,hall⟩ := h.replacement_large_movement_root_generator d path hb hat hsmall hJm
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    exact Ne.symm hh
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hfix : Z d.radical t ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y (hzT hy)
  refine ⟨g,hg,?_⟩
  intro c hct
  dsimp only
  have hgen := hall c hct
  refine ⟨hgen,?_⟩
  apply le_antisymm
  · refine le_inf inf_le_left (le_centralizer_iff.mpr ?_)
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hfix))
  · have hle : (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom ≤
          stabilizer d.radical a := le_sup_left.trans_eq hgen
    exact inf_le_inf_left _ (centralizer_le hle)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
