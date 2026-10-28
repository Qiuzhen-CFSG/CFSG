module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusSeedIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalMovers

/-!
# The full seed intersection for equal small movers at distance four

Strict movement relative to the original B-subgroup identifies the fixed
subgroup of the neighboring kernel with that of the common small mover.
The explicit small movement bound places that mover in a maximizing
quadratic plane. The whole-seed decomposition retains every fixed attachment.
At distance four the reverse containment follows from X = Z and the
neighboring core containment. In the same natural marking, a retained
normalizer of the parabolic core therefore normalizes the full seed
intersection, as in the last sentence of MS93 p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem mover_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
        (Q R (act R y t)) q =
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R t) q).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    (centralizer (Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
      (Q R (act R y t)) q : Set (FreeAmalgam R))).relIndex (U R (act R y v)) =
      (centralizer (Subgroup.SmallMover.join (U R v) (Q R v)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R v) := by
  rw [mover_act,U_act,Subgroup.SmallMover.centralizer_index_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_neighbors {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) {a t c : Vertex R} (hat : Adjacent R a t) (hct : Adjacent R c t) :
    (centralizer (Subgroup.SmallMover.join (U R c) (Q R c)
      (Q R t) q : Set (FreeAmalgam R))).relIndex (U R c) =
      (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R a) := by
  obtain ⟨y,hy,hya⟩ := stabilizer_transitive_neighbors R t
    (adjacent_symm R hat) (adjacent_symm R hct)
  have hyt : act R y t=t := hy
  simpa only [hya,hyt] using own_index_act q y a t

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem moving_actor_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2))
    (hmove : Nat.card F < (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a)) :
    U d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
      U d.radical a ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set _) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hAS : A ≤ S := hAJ.trans hJS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ a)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb ha hat
  have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb ha hat E hE f hfQ hTf hindex hmax hJm
  let P := (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype
  let A₀ := A.subgroupOf S
  let J₀ := J.subgroupOf S
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hJf : J₀.map f ≤ P := (map_le_iff_le_comap).mpr hJP
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have bridge (T : Subgroup (Sp E.Carrier)) :
      fixedSpace σ T=(TwoLocalCover.fixedSpace T).restrictScalars (ZMod 2) := by
    ext v
    exact ⟨fun hv x hx => hv ⟨x,hx⟩,fun hv x => hv x.val x.property⟩
  have hAi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) A₀
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS,hindex] at hAi
  have hquot : 2 ^ fixedCodim σ (A₀.map f) =
      Nat.card (Vector E.Carrier ⧸ TwoLocalCover.fixedSpace (A₀.map f)) := by
    change 2 ^ Module.finrank (ZMod 2) (Vector E.Carrier ⧸ fixedSpace σ (A₀.map f)) = _
    rw [bridge]
    have hh := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (TwoLocalCover.fixedSpace (A₀.map f))).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact hh
  have hbig : Nat.card E.Carrier <
      Nat.card (Vector E.Carrier ⧸ TwoLocalCover.fixedSpace (A₀.map f)) := by
    rw [hcard,←hquot]
    exact hAi ▸ hmove
  have hfixed := moving_quadratic_subactor_fixed_eq (A₀.map f) (J₀.map f)
    (map_mono (comap_mono hAJ))
    (fun x hx y hy v => CentralRootGeometry.SmallMovers.Degree.plane_radical_quadratic
      x (hJf hx) y (hJf hy) v) hbig
  have hfixed' : fixedSpace σ (A₀.map f)=fixedSpace σ (J₀.map f) := by
    rw [bridge,bridge,hfixed]
  have hJi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) J₀
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,hindex] at hJi
  have hi : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [hAi,hJi]
    change 2 ^ fixedCodim σ (A₀.map f)=2 ^ fixedCodim σ (J₀.map f)
    unfold fixedCodim
    rw [hfixed']
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (U_le_Z a)) (inclusion_injective _)
  let CA := (centralizer (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  let CJ := (centralizer (J : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  have he : CJ=CA := by
    apply eq_of_le_of_card_ge (comap_mono (centralizer_le hAJ))
    have hCA := CA.card_mul_index
    have hCJ := CJ.card_mul_index
    change CA.index=CJ.index at hi
    rw [hi] at hCA
    exact (Nat.eq_of_mul_eq_mul_right (index_ne_zero_of_finite (H := CJ)).bot_lt
      (hCA.trans hCJ.symm)).le
  apply le_antisymm
  · intro u hu
    exact ⟨hu.1,show (⟨u,hu.1⟩ : U d.radical a) ∈ CJ from he.symm ▸ hu.2⟩
  · exact inf_le_inf_left _ (centralizer_le hAJ)

omit [CharP F 2] in
private theorem core_le_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

/-- The strict original B-index identifies the full intersection of equal
mover seeds with the original mover-fixed seed, including every attachment. -/
theorem Input.replacement_distance_four_equal_small_seed_intersection
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    Z d.radical a ⊓ Z d.radical c = Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hc : color d.radical c=false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  have hJSa : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hJSc : J ≤ stabilizer d.radical c := by
    dsimp only [J]
    rw [←hequal]
    exact (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 c (adjacent_symm _ hct))
  have hQaJ : Q d.radical a ≤ J := core_le_mover h d ha hat
  let C := U d.radical c ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical))
  have hZcV : Z d.radical c ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius hat hct)
  have hCV : C ≤ V d.radical a := inf_le_left.trans ((U_le_Z c).trans hZcV)
  have hCX : C ≤ X d.radical a := by
    let := geometry.Z_elementary (by omega) c hc
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨(hCV.trans (geometry.V_le_Q (by omega) a ha)) hx,
      elemPow_eq_one_of_isElementaryAbelian x (U_le_Z c hx.1),hx.2⟩
  have hCB : C ≤ B d.radical a (geometry.Z_normal a) :=
    radius_le_B_of_commutator geometry (by omega) ha C hCV
      ((commutator_mono hCX le_rfl).trans
        ((h.replacement_X_commutator_eq_U d ha).le.trans (U_le_Z a)))
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (U_le_Z c)) (inclusion_injective _)
  have hm : Nat.card F < (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical c) := by
    have hh := relIndex_le_of_le_left hCB (L := U d.radical c) index_ne_zero_of_finite
    dsimp only [C] at hh
    rw [inf_relIndex_left] at hh
    exact hmove.trans_le hh
  have hfixed : U d.radical c ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical c ⊓ centralizer (J : Set (FreeAmalgam d.radical)) := by
    have hJmc : (centralizer (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical c) ≤ Nat.card F^2 := by
      rw [own_index_neighbors _ hat hct]
      exact hJm
    have hh := moving_actor_fixed h d geometry (by omega) hc hct hJmc (Q d.radical a)
      (by rw [hequal]; exact hQaJ) hm
    simpa only [hequal,J] using hh
  have hZfixed : Z d.radical c ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) ≤
      centralizer (J : Set (FreeAmalgam d.radical)) := by
    let D := Z d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))
    have hDN : D ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans (Z_le_stabilizer _ c)).trans (U_normalized c)
    have hDJ : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
      inf_le_right.trans (centralizer_le hJSc)
    have hDQ : D ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
      hDJ.trans (centralizer_le hQaJ)
    intro z hz
    have hzprod : z ∈ (U d.radical c : Set (FreeAmalgam d.radical)) * (D : Set _) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hDN]
      exact h.replacement_Z_eq_U_sup_fixed d geometry (by omega) hc ▸ hz.1
    obtain ⟨u,hu,e,he,rfl⟩ := hzprod
    have huQ : u ∈ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
      have hh := (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).mul_mem hz.2
        ((centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).inv_mem (hDQ he))
      simpa only [mul_inv_cancel_right] using hh
    exact (centralizer (J : Set (FreeAmalgam d.radical))).mul_mem
      (hfixed ▸ (show u ∈ U d.radical c ⊓ centralizer
        (Q d.radical a : Set (FreeAmalgam d.radical)) from ⟨hu,huQ⟩)).2 (hDJ he)
  apply le_antisymm
  · exact fun x hx => ⟨hx.1,hZfixed ⟨hx.2,
      commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha) hx.1⟩⟩
  · have hQcJ : Q d.radical c ≤ J := by
      dsimp only [J]
      rw [←hequal]
      exact core_le_mover h d hc hct
    have hZaQc : Z d.radical a ≤ Q d.radical c :=
      (le_sup_left.trans (neighbor_seed_join_le_radius hct hat)).trans
        (geometry.V_le_Q (by omega) c hc)
    have hDX : Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) ≤
        X d.radical c := by
      let := geometry.Z_elementary (by omega) a ha
      intro x hx
      exact mem_omegaCenter_iff.mpr ⟨hZaQc hx.1,
        elemPow_eq_one_of_isElementaryAbelian x hx.1,centralizer_le hQcJ hx.2⟩
    exact le_inf inf_le_left
      (hDX.trans (h.replacement_distance_four_X_eq_Z d geometry hb hc).le)

/-- In the same natural marking, every retained stabilizer element normalizing
its full parabolic core normalizes the actual full seed intersection. -/
theorem Input.replacement_distance_four_equal_small_seed_intersection_normalized
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (E : BinaryField) (hE : E.degree = n)
    (f : stabilizer d.radical a →* Sp E.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := E.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hxD : x ∈ normalizer
      (((((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    x ∈ normalizer ((Z d.radical a ⊓ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have he := h.replacement_distance_four_equal_small_seed_intersection d
    geometry hb ha hat hct hequal hmove hJm
  have hfixed := h.replacement_small_mover_parabolic_full_fixed d geometry (by omega)
    ha hat E hE f hf hfQ hindex hJplane
  rw [he,hfixed]
  exact inf_normalizer_le_normalizer_inf
    ⟨Z_normalized d.radical a hx,normalizer_le_normalizer_centralizer _ hxD⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
