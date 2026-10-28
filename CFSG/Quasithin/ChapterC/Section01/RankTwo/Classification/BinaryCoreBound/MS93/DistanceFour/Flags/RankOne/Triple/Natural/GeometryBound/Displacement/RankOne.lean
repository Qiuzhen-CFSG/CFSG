module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Incidence

/-!
# The numerical rank-one step before natural recognition

An index-three subgroup of a finite group with trivial odd-order quotients
and one conjugate generate the group. Intersecting their fixed preimages
therefore bounds the full fixed index by the square of the given fixed
index. All denominators need only be normalized by the acting groups;
normality in the infinite amalgam is never used.

Applied to an actual conjugate parabolic and its elementary first layer,
this gives the bound four from an index-three subgroup whose fixed index
is at most two. The residual fixed preimage is larger than the full-actor
fixed preimage. Conjugation transports the bound back to the original layer.
The geometric construction of the index-three subgroup remains separate.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), numerical consequence of the rank-one recognition step in the proof
of (4.6.8), claim (1), printed p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

private theorem index_three_conjugate_generation {G : Type*} [Group G] [Finite G]
    (hres : primeToResidual 2 G = ⊤) (S : Subgroup G) (hi : S.index = 3) :
    ∃ g : G, S ⊔ S.map (MulAut.conj g).toMonoidHom = ⊤ := by
  have hn : ¬ S.Normal := by
    intro hn
    let := hn
    have h := primeToResidual_le (p := 2) S (by rw [hi]; decide)
    rw [hres] at h
    have he := top_unique h
    rw [he, index_top] at hi
    omega
  obtain ⟨g, hg⟩ : ∃ g : G, S.map (MulAut.conj g).toMonoidHom ≠ S := by
    classical
    by_contra! h
    apply hn
    apply normal_iff_map_conj_eq.mpr
    intro g
    exact h g
  refine ⟨g, ?_⟩
  let T := S ⊔ S.map (MulAut.conj g).toMonoidHom
  have hd : T.index ∣ 3 := hi ▸ index_dvd_of_le (show S ≤ T from le_sup_left)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with ht | ht
  · exact index_eq_one.mp ht
  · have hm := relIndex_mul_index (show S ≤ T from le_sup_left)
    rw [hi, ht] at hm
    have he : S.relIndex T = 1 := by omega
    have hc : S.map (MulAut.conj g).toMonoidHom ≤ S :=
      (show S.map (MulAut.conj g).toMonoidHom ≤ T from le_sup_right).trans
        (relIndex_eq_one.mp he)
    exact (hg (eq_of_le_of_card_ge hc (by rw [card_map_of_injective
      (MulAut.conj g).injective]))).elim

private theorem map_preimage_le {G : Type*} [Group G]
    (W T N : Subgroup G) (f : G →* G) (hWN : W ≤ normalizer N) :
    (commutatorPreimage W T N).map f ≤
      commutatorPreimage (W.map f) (T.map f) (N.map f) := by
  apply le_commutatorPreimage (map_mono (commutatorPreimage_le W T N))
  rw [← map_commutator]
  exact map_mono (commutator_commutatorPreimage_le W T N hWN)

private theorem map_preimage_eq {G : Type*} [Group G]
    (W T N : Subgroup G) (e : G ≃* G) (hWN : W ≤ normalizer N) :
    (commutatorPreimage W T N).map e.toMonoidHom =
      commutatorPreimage (W.map e.toMonoidHom) (T.map e.toMonoidHom)
        (N.map e.toMonoidHom) := by
  refine le_antisymm (map_preimage_le W T N e.toMonoidHom hWN) ?_
  have hn : W.map e.toMonoidHom ≤ normalizer (N.map e.toMonoidHom) :=
    (map_mono hWN).trans (le_normalizer_map e.toMonoidHom)
  have hb := map_preimage_le (W.map e.toMonoidHom) (T.map e.toMonoidHom)
    (N.map e.toMonoidHom) e.symm.toMonoidHom hn
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.symm_apply_apply
  rw [map_map, map_map, map_map, he, map_id, map_id, map_id] at hb
  have hm := map_mono (f := e.toMonoidHom) hb
  have he' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.apply_symm_apply
  rwa [map_map, he', map_id] at hm

private theorem fixed_index_bound_of_index_three {G : Type*} [Group G]
    (P W N T : Subgroup G) [Finite P] [Finite W]
    (hres : primeToResidual 2 P = ⊤)
    (hPW : P ≤ normalizer W) (hPN : P ≤ normalizer N)
    (hWN : W ≤ normalizer N) (hTP : T ≤ P) (hi : T.relIndex P = 3)
    (hfix : (commutatorPreimage W T N).relIndex W ≤ 2) :
    (commutatorPreimage W P N).relIndex W ≤ 4 := by
  obtain ⟨g, hg⟩ := index_three_conjugate_generation hres (T.subgroupOf P) hi
  let e := MulAut.conj (g : G)
  let T' := T.map e.toMonoidHom
  have hgen : T ⊔ T' = P := by
    have hm := congrArg (Subgroup.map P.subtype) hg
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, P.range_subtype, map_subgroupOf_eq_of_le hTP] at hm
    have he : P.subtype.comp (MulAut.conj g).toMonoidHom = e.toMonoidHom.comp P.subtype := by
      ext x
      rfl
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le hTP] at hm
    exact hm
  have hW : W.map e.toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp (hPW g.property)
  have hN : N.map e.toMonoidHom = N := mem_normalizer_iff_map_conj_eq.mp (hPN g.property)
  have hconj : (commutatorPreimage W T' N).relIndex W =
      (commutatorPreimage W T N).relIndex W := by
    have he := map_preimage_eq W T N e hWN
    rw [hW, hN] at he
    calc
      _ = ((commutatorPreimage W T N).map e.toMonoidHom).relIndex
          (W.map e.toMonoidHom) := by rw [he, hW]
      _ = _ := relIndex_map_map_of_injective _ _ e.injective
  let D := commutatorPreimage W T N ⊓ commutatorPreimage W T' N
  have hDT : ⁅D,T⁆ ≤ N := (commutator_mono inf_le_left le_rfl).trans
    (commutator_commutatorPreimage_le W T N hWN)
  have hDT' : ⁅D,T'⁆ ≤ N := (commutator_mono inf_le_right le_rfl).trans
    (commutator_commutatorPreimage_le W T' N hWN)
  have hPD : P ≤ commutatorPreimage P D N := by
    conv_lhs => rw [← hgen]
    apply sup_le
    · exact le_commutatorPreimage hTP (by rwa [commutator_comm])
    · exact le_commutatorPreimage (le_sup_right.trans hgen.le) (by rwa [commutator_comm])
  have hD : D ≤ commutatorPreimage W P N := by
    apply le_commutatorPreimage (inf_le_left.trans (commutatorPreimage_le W T N))
    rw [commutator_comm]
    exact (commutator_mono hPD le_rfl).trans
      (commutator_commutatorPreimage_le P D N hPN)
  have hiD : D.relIndex W ≤ 4 := by
    have hh := relIndex_inf_le (H := commutatorPreimage W T N)
      (K := commutatorPreimage W T' N) (L := W)
    rw [hconj] at hh
    exact hh.trans (by nlinarith)
  exact (relIndex_le_of_le_left hD index_ne_zero_of_finite).trans hiD

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- An index-three subgroup with a fixed preimage of index at most two
bounds the actual residual fixed quotient by four. The subgroup and its
conjugate generate the full parabolic; no natural factor is assumed. -/
theorem flagFixedPreimage_relIndex_le_four_of_local_index_three
    (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (g : M)
    (T : Subgroup (FreeAmalgam R)) (hT : T ≤ localFlagActor source i g)
    (hindex : T.relIndex (localFlagActor source i g) = 3)
    (hfixed : (commutatorPreimage (firstFlagLayer (R := R) g) T
      (Z R (alpha R))).relIndex (firstFlagLayer (R := R) g) ≤ 2) :
    (flagFixedPreimage source i).relIndex (V R (beta R)) ≤ 4 := by
  let P := localFlagActor source i g
  let W := firstFlagLayer (R := R) g
  let N := Z R (alpha R)
  let e := MulAut.conj (embedM R g)
  have hP : P ≤ stabilizer R (alpha R) :=
    localFlagActor_le_stabilizer source i g
  have hW : W ≤ stabilizer R (alpha R) :=
    (firstFlagLayer_le_radius g).trans (geometry.V_local _ rfl hlarge)
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion hP) (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hW) (inclusion_injective _)
  have hres : primeToResidual 2 P = ⊤ := by
    let f := (flagParabolic source i).equivMapOfInjective e.toMonoidHom e.injective
    change primeToResidual 2 ((flagParabolic source i).map e.toMonoidHom) = ⊤
    rw [← map_primeToResidual (p := 2) f, flagParabolic_primeToResidual source i,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr f.surjective]
  have hPW : P ≤ normalizer W :=
    (map_mono (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)).trans
      (le_normalizer_map e.toMonoidHom)
  have hPN : P ≤ normalizer N := hP.trans (Z_normalized R _)
  have hWN : W ≤ normalizer N := hW.trans (Z_normalized R _)
  have hh := fixed_index_bound_of_index_three P W N T hres hPW hPN hWN hT hindex hfixed
  have hK : localFlagResidual source i g ≤ P := map_mono (flagResidual_le source i)
  have hC : commutatorPreimage W P N ≤
      commutatorPreimage W (localFlagResidual source i g) N :=
    le_commutatorPreimage (commutatorPreimage_le W P N)
      ((commutator_mono le_rfl hK).trans (commutator_commutatorPreimage_le W P N hWN))
  have hi := (relIndex_le_of_le_left hC index_ne_zero_of_finite).trans hh
  rwa [localFlagFixedPreimage_relIndex source geometry hlarge i g] at hi

/-- Excessive residual fixed index excludes an index-two fixed space for
any actual index-three subgroup of a conjugate full actor. -/
theorem two_lt_local_fixedIndex_of_index_three
    (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hexcess : 4 < (flagFixedPreimage source i).relIndex (V R (beta R)))
    (g : M) (T : Subgroup (FreeAmalgam R))
    (hT : T ≤ localFlagActor source i g)
    (hindex : T.relIndex (localFlagActor source i g) = 3) :
    2 < (commutatorPreimage (firstFlagLayer (R := R) g) T
      (Z R (alpha R))).relIndex (firstFlagLayer (R := R) g) := by
  by_contra! hsmall
  exact (not_lt_of_ge (flagFixedPreimage_relIndex_le_four_of_local_index_three
    source geometry hlarge i hkernel g T hT hindex hsmall)) hexcess
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
