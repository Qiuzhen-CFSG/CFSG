module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets

/-!
# Transport of the literal binary auxiliary structure

Simultaneous conjugation preserves the greatest commutator preimage, hence
all three source layers Y, D and X. Natural factor coordinates are pulled
back through the actual subgroup equivalences. This preserves surjectivity,
the coordinate kernel, the exact actor kernel and the ambient action equation.
The full first-actor triple and the second-layer decomposition also transport.
Consequently a construction at one local flag supplies every local flag.

These are transport lemmas, not constructors of the p.907 natural factors.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), pp.907--908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
private theorem map_commutatorPreimage_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A B N : Subgroup G) (hn : A ≤ normalizer N) :
    (commutatorPreimage A B N).map f ≤ commutatorPreimage (A.map f) (B.map f) (N.map f) := by
  apply le_commutatorPreimage (map_mono (commutatorPreimage_le A B N))
  rw [← map_commutator]
  exact map_mono (commutator_commutatorPreimage_le A B N hn)

theorem commutatorPreimage_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A B N : Subgroup G) (hn : A ≤ normalizer N) :
    (commutatorPreimage A B N).map e.toMonoidHom =
      commutatorPreimage (A.map e.toMonoidHom) (B.map e.toMonoidHom) (N.map e.toMonoidHom) := by
  apply le_antisymm (map_commutatorPreimage_le e.toMonoidHom A B N hn)
  have h := map_mono (f := e.toMonoidHom)
    (map_commutatorPreimage_le e.symm.toMonoidHom
      (A.map e.toMonoidHom) (B.map e.toMonoidHom) (N.map e.toMonoidHom)
      ((map_mono hn).trans (le_normalizer_map e.toMonoidHom)))
  have h₁ : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  have h₂ : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  simpa only [Subgroup.map_map, h₁, h₂, Subgroup.map_id] using h

noncomputable def factorMap {G H : Type*} [Group G] [Group H]
    {K A N : Subgroup G} (e : G ≃* H) (n : RankOnePairing.RankOneFactor K A N) :
    RankOnePairing.RankOneFactor (K.map e.toMonoidHom) (A.map e.toMonoidHom)
      (N.map e.toMonoidHom) where
  projection := n.projection.comp (e.subgroupMap K).symm.toMonoidHom
  surjective := n.surjective.comp (e.subgroupMap K).symm.surjective
  coordinates := n.coordinates.comp (e.subgroupMap A).symm.toMonoidHom
  coordinates_surjective := n.coordinates_surjective.comp (e.subgroupMap A).symm.surjective
  kernel := by
    ext x
    change n.coordinates ((e.subgroupMap A).symm x) = 1 ↔ (x : H) ∈ N.map e.toMonoidHom
    rw [← MonoidHom.mem_ker, n.kernel, mem_map_equiv]
    rfl
  normalized := (map_mono n.normalized).trans (le_normalizer_map _)
  action := by
    intro l x y he
    exact n.action ((e.subgroupMap K).symm l) ((e.subgroupMap A).symm x)
      ((e.subgroupMap A).symm y) (by
        change e.symm (y : H) = e.symm (l : H) * e.symm (x : H) * (e.symm (l : H))⁻¹
        rw [he, map_mul, map_mul, map_inv])

theorem factorMap_actor_kernel {G H : Type*} [Group G] [Group H]
    {K A N C : Subgroup G} (e : G ≃* H) (n : RankOnePairing.RankOneFactor K A N)
    (hn : n.projection.ker = C.subgroupOf K) :
    (factorMap e n).projection.ker = (C.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) := by
  ext l
  change n.projection ((e.subgroupMap K).symm l) = 1 ↔ (l : H) ∈ C.map e.toMonoidHom
  rw [← MonoidHom.mem_ker, hn, mem_map_equiv]
  rfl

variable {M : Type*} [Group M] {L R : Subgroup M}

theorem second_conjugate (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a d : M) :
    localConjugate (secondFlagLayer source i d) a = secondFlagLayer source i (a * d) := by
  apply le_antisymm (Incident.secondFlagLayer_conjugate_le source geometry hlarge i a d)
  have h := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom)
    (Incident.secondFlagLayer_conjugate_le source geometry hlarge i a⁻¹ (a*d))
  change localConjugate (localConjugate (secondFlagLayer source i (a*d)) a⁻¹) a ≤
    localConjugate (secondFlagLayer source i (a⁻¹*(a*d))) a at h
  simpa only [← localConjugate_mul, mul_inv_cancel, localConjugate_one,
    inv_mul_cancel_left] using h

theorem D_conjugate [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a d : M) :
    localConjugate (D source i d) a = D source i (a*d) := by
  unfold D localConjugate
  rw [commutatorPreimage_map_equiv _ _ _ _
    (Y_normalizes_second source geometry hlarge i d)]
  change commutatorPreimage (localConjugate (Y source i d) a)
    (localConjugate (localConjugate (flagParabolic source (!i)) d) a)
    (localConjugate (secondFlagLayer source i d) a) = _
  rw [Y_conjugate, ← localConjugate_mul, second_conjugate source geometry hlarge]
  rfl

theorem X_conjugate [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a d : M) :
    localConjugate (X source i d) a = X source i (a*d) := by
  unfold X localConjugate
  rw [Subgroup.map_sup, map_commutator]
  change ⁅localConjugate (D source i d) a,
    localConjugate (localConjugate (flagKernel source (!i)) d) a⁆ ⊔
    localConjugate (Z R (alpha R)) a = _
  rw [D_conjugate source geometry hlarge, ← localConjugate_mul, Incident.localConjugate_Z]
  rfl

/-- A natural factor with the prescribed kernel of the full actor map. -/
abbrev MarkedFactor {G : Type*} [Group G] (K A N C : Subgroup G) :=
  {n : RankOnePairing.RankOneFactor K A N // n.projection.ker = C.subgroupOf K}

noncomputable def markedFactorMap {G H : Type*} [Group G] [Group H]
    {K A N C : Subgroup G} (e : G ≃* H) (n : MarkedFactor K A N C) :
    MarkedFactor (K.map e.toMonoidHom) (A.map e.toMonoidHom)
      (N.map e.toMonoidHom) (C.map e.toMonoidHom) :=
  ⟨factorMap e n.val, factorMap_actor_kernel e n.val n.property⟩

abbrev MovingFactor (source : LocalSource L R) (i : Bool) (d : M) :=
  MarkedFactor (localFlagActor source (!i) d)
    (⁅Y source i d, localFlagActor source (!i) d⁆ ⊔ secondFlagLayer source i d)
    (secondFlagLayer source i d) (localFlagKernel source (!i) d)

abbrev XFactor (source : LocalSource L R) (i : Bool) (d : M) :=
  MarkedFactor (localFlagActor source (!i) d) (X source i d)
    (Z R (alpha R)) (localFlagKernel source (!i) d)

theorem movingFactor_conjugate [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a d : M)
    (n : MovingFactor source i d) : Nonempty (MovingFactor source i (a*d)) := by
  have hn := markedFactorMap (MulAut.conj (embedM R a)) n
  have hP : (localFlagActor source (!i) d).map
      (MulAut.conj (embedM R a)).toMonoidHom = localFlagActor source (!i) (a*d) :=
    (localConjugate_mul (flagParabolic source (!i)) a d).symm
  have hQ : (localFlagKernel source (!i) d).map
      (MulAut.conj (embedM R a)).toMonoidHom = localFlagKernel source (!i) (a*d) :=
    (localConjugate_mul (flagKernel source (!i)) a d).symm
  have hU := second_conjugate source geometry hlarge i a d
  have hY := Y_conjugate source i a d
  unfold localConjugate at hU hY
  unfold MovingFactor
  simpa only [Subgroup.map_sup, map_commutator, hP, hQ, hU, hY] using Nonempty.intro hn

theorem XFactor_conjugate [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a d : M)
    (n : XFactor source i d) : Nonempty (XFactor source i (a*d)) := by
  have hn := markedFactorMap (MulAut.conj (embedM R a)) n
  have hP : (localFlagActor source (!i) d).map
      (MulAut.conj (embedM R a)).toMonoidHom = localFlagActor source (!i) (a*d) :=
    (localConjugate_mul (flagParabolic source (!i)) a d).symm
  have hQ : (localFlagKernel source (!i) d).map
      (MulAut.conj (embedM R a)).toMonoidHom = localFlagKernel source (!i) (a*d) :=
    (localConjugate_mul (flagKernel source (!i)) a d).symm
  have hX := X_conjugate source geometry hlarge i a d
  have hZ := Incident.localConjugate_Z (R := R) a
  unfold localConjugate at hX hZ
  unfold XFactor
  simpa only [hP, hQ, hX, hZ] using Nonempty.intro hn

theorem localStructure_conjugate [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (a d : M)
    (s : LocalStructure source i d) : Nonempty (LocalStructure source i (a*d)) := by
  obtain ⟨n⟩ := movingFactor_conjugate source geometry hlarge i a d
    ⟨s.moving, s.moving_actor_kernel⟩
  obtain ⟨x⟩ := XFactor_conjugate source geometry hlarge i a d
    ⟨s.natural, s.natural_actor_kernel⟩
  let f := (MulAut.conj (embedM R a)).toMonoidHom
  have hA (j : Bool) (g : M) : (localFlagActor source j g).map f =
      localFlagActor source j (a*g) := (localConjugate_mul (flagParabolic source j) a g).symm
  have hK (j : Bool) (g : M) : (localFlagKernel source j g).map f =
      localFlagKernel source j (a*g) := (localConjugate_mul (flagKernel source j) a g).symm
  have hU : (secondFlagLayer source i d).map f = secondFlagLayer source i (a*d) :=
    second_conjugate source geometry hlarge i a d
  have hX : (X source i d).map f = X source i (a*d) :=
    X_conjugate source geometry hlarge i a d
  have hZ : (Z R (alpha R)).map f = Z R (alpha R) := Incident.localConjugate_Z a
  refine ⟨⟨n.val, n.property, x.val, x.property, ?_, ?_, ?_⟩⟩
  · intro g hg
    have hi : flagIncident source i (a⁻¹*g) d := by
      have hh := (Incident.flagIncident_left source i a⁻¹ g (a*d)).mpr hg
      simpa only [inv_mul_cancel_left] using hh
    have hh := map_mono (f := f) (s.first_triple (a⁻¹*g) hi)
    simpa only [map_commutator, hX, hK, hA, hZ, mul_inv_cancel_left] using hh
  · have hh := map_mono (f := f) s.second_commutator
    simpa only [map_commutator, hU, hA, hX] using hh
  · intro g hg
    have hi : flagIncident source i (a⁻¹*g) d := by
      have hh := (Incident.flagIncident_left source i a⁻¹ g (a*d)).mpr hg
      simpa only [inv_mul_cancel_left] using hh
    have hh := congrArg (Subgroup.map f) (s.second_decomposition (a⁻¹*g) hi)
    have hF : (firstFlagLayer (R := R) (a⁻¹*g)).map f = firstFlagLayer (R := R) g := by
      exact (localConjugate_mul (V R (beta R)) a (a⁻¹*g)).symm.trans
        (congrArg (localConjugate (V R (beta R))) (mul_inv_cancel_left a g))
    have hnormal : firstFlagLayer (R := R) (a⁻¹*g) ≤ normalizer (Z R (alpha R)) :=
      (firstFlagLayer_le_radius (a⁻¹*g)).trans
        ((geometry.V_local _ rfl hlarge).trans (Z_normalized R _))
    rw [Subgroup.map_sup, commutatorPreimage_map_equiv (MulAut.conj (embedM R a))
      _ _ _ hnormal, hU, hF, hK, hZ, hX] at hh
    exact hh

theorem localStructure_at_iff [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d e : M) :
    Nonempty (LocalStructure source i d) ↔ Nonempty (LocalStructure source i e) := by
  constructor
  · rintro ⟨s⟩
    simpa only [inv_mul_cancel_right] using
      localStructure_conjugate source geometry hlarge i (e*d⁻¹) d s
  · rintro ⟨s⟩
    simpa only [inv_mul_cancel_right] using
      localStructure_conjugate source geometry hlarge i (d*e⁻¹) e s

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
