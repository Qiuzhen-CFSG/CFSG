module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.ModuleStructure
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Local reduction of the binary critical-module calculations

The marked natural matrix action gives the exact local centralizer of U.
Conjugation in the free amalgam transports this kernel and the order eight
calculation to every M-vertex. The perfect SL₃(2) quotient implies that the
local two-residual and Q generate the stabilizer. Consequently the fixed
summand in the supplied natural decomposition of Z is central in the whole
stabilizer.

For a critical pair this removes the fixed summands from both commutators
and relative indices. The actual natural subgroups are mutually normalizing,
noncommuting elementary abelian groups of order eight. The remaining numerical
calculation is a finite binary commutator-pairing problem; it is not assumed
as a source theorem here. The radius-two containment lemma prepares the same
calculation for the class bound when b = 4.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), binary portions of (3.5) and (3.9), printed pp.869--870 and 879.
The natural-module identification and decomposition remain explicit inputs.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem map_inf_centralizer_equiv {G : Type*} [Group G]
    (A B : Subgroup G) (e : G ≃* G) :
    (A ⊓ centralizer (B : Set G)).map e.toMonoidHom =
      A.map e.toMonoidHom ⊓ centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨mem_map_of_mem _ hx, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hc y hy)
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hc (e y) (mem_map_of_mem _ hy)

theorem NaturalU.centralizer_alpha [Finite M] {source : LocalSource L R}
    (natural : NaturalU R source.projection) :
    stabilizer R (alpha R) ⊓ centralizer (U R (alpha R) : Set (FreeAmalgam R)) =
      Q R (alpha R) := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    have hxM : x ∈ Mbar R := (stabilizer_m_base R) ▸ hx
    obtain ⟨m, rfl⟩ := hxM
    have hfix (u : U R (alpha R)) :
        (natural.marking (source.projection m)).val.mulVec
          (Multiplicative.toAdd (natural.equiv u)) =
          Multiplicative.toAdd (natural.equiv u) := by
      apply (natural.action m u u ?_).symm
      rw [← hc u u.property, mul_assoc, mul_inv_cancel, mul_one]
    have hmat : natural.marking (source.projection m) = 1 := by
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      have hh := congrFun (hfix (natural.equiv.symm
        (Multiplicative.ofAdd (Pi.single j 1)))) i
      simp only [MulEquiv.apply_symm_apply] at hh
      change (natural.marking (source.projection m)).val.mulVec (Pi.single j 1) i =
        (Pi.single j 1 : Fin 3 → ZMod 2) i at hh
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using hh
    have hm : m ∈ pCore 2 M := by
      rw [← source.projection_kernel]
      exact natural.marking.map_eq_one_iff.mp hmat
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ hm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact centralizer_le (U_le_Z (alpha R))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R (alpha R) rfl)) hx)

theorem NaturalU.centralizer [Finite M] {source : LocalSource L R}
    (natural : NaturalU R source.projection) (a : Vertex R) (ha : color R a = false) :
    stabilizer R a ⊓ centralizer (U R a : Set (FreeAmalgam R)) = Q R a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hbase := natural.centralizer_alpha
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  rw [map_inf_centralizer_equiv, ← stabilizer_act, ← U_act, ← Q_act] at hh
  simpa only [alpha, act_mVertex, one_mul] using hh

theorem NaturalU.card_at {π : M →* SL} (natural : NaturalU R π)
    (a : Vertex R) (ha : color R a = false) : Nat.card (U R a) = 8 := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hu := U_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hu
  change U R (mVertex R g) = (U R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom at hu
  rw [hu, ← Nat.card_congr ((U R (alpha R)).equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toEquiv]
  exact natural.card

theorem LocalSource.residual_sup_core [Finite M] (source : LocalSource L R) :
    L ⊔ pCore 2 M = ⊤ := by
  have hperfect : IsPPerfect 2 SL := by
    let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
    intro N hN hp
    let := hN
    have hsub : Subsingleton (SL ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (SL ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hmap : L.map source.projection = ⊤ := by
    have hh := map_pResidual_of_surjective 2 source.projection source.projection_surjective
    simpa only [source.residual, (pResidual_eq_top_iff 2 SL).mpr hperfect] using hh
  have h := congrArg (Subgroup.comap source.projection) hmap
  simpa only [comap_map_eq, source.projection_kernel, comap_top] using h

theorem LocalSource.local_generation [Finite M] (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    Ltilde R a ⊔ Q R a = stabilizer R a := by
  have hbase : Ltilde R (alpha R) ⊔ Q R (alpha R) = stabilizer R (alpha R) := by
    rw [Ltilde_alpha, source.residual, Q_alpha R source.two_group source.core_le,
      ← Subgroup.map_sup, source.residual_sup_core, ← MonoidHom.range_eq_map]
    exact (stabilizer_m_base R).symm
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  rw [Subgroup.map_sup, ← Ltilde_act, ← Q_act, ← stabilizer_act] at hh
  simpa only [alpha, act_mVertex, one_mul] using hh

theorem BinaryNaturalStructure.decomposition_at [Finite M] {source : LocalSource L R}
    (structureData : BinaryNaturalStructure source)
    (a : Vertex R) (ha : color R a = false) :
    Z R a = U R a ⊔
      (Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))) := by
  have hsplit : Z R a = U R a ⊔
      (Z R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
    obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
      structureData.decomposition
    rw [Subgroup.map_sup, map_inf_centralizer_equiv, ← Z_act, ← U_act, ← Ltilde_act] at hh
    simpa only [alpha, act_mVertex, one_mul] using hh
  have hfixed : Z R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · intro z hz
      refine ⟨hz.1, ?_⟩
      have hZQ := commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)
      have hn : Ltilde R a ⊔ Q R a ≤ centralizer ({z} : Set (FreeAmalgam R)) := by
        apply sup_le
        · intro x hx
          exact mem_centralizer_singleton_iff.mpr (hz.2 x hx)
        · intro x hx
          exact mem_centralizer_singleton_iff.mpr (hZQ hz.1 x hx)
      intro x hx
      exact (mem_centralizer_singleton_iff.mp (hn ((source.local_generation a ha).ge hx)))
    · exact inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer a))
  rwa [hfixed] at hsplit

theorem LocalSource.critical_Z_le_stabilizer [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Z R a ≤ stabilizer R a' ∧ Z R a' ≤ stabilizer R a := by
  have ha' := critical_endpoint_color R a ha _ hc
  exact ⟨Z_le_stabilizer_of_dist_le a _ hc.1.le,
    Z_le_stabilizer_of_dist_le a' _ (source.critical_reverse geometry a ha a' ha' hc).1.le⟩

theorem BinaryNaturalStructure.commutator_eq_of_mutual_stabilizer [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R) (ha' : color R a' = false)
    (hza : Z R a ≤ stabilizer R a') (hza' : Z R a' ≤ stabilizer R a) :
    ⁅Z R a, Z R a'⁆ = ⁅U R a, U R a'⁆ := by
  have h₁ : ⁅Z R a, U R a'⁆ = ⁅Z R a, Z R a'⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (structureData.decomposition_at a' ha').symm)
      (inf_le_right.trans (centralizer_le hza))
      ((U_le_Z a').trans (hza'.trans (Z_normalized R a)))
  have h₂ : ⁅U R a', U R a⁆ = ⁅U R a', Z R a⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (structureData.decomposition_at a ha).symm)
      (inf_le_right.trans (centralizer_le ((U_le_Z a').trans hza')))
      ((U_le_Z a).trans (hza.trans (U_normalized a')))
  rw [← h₁, commutator_comm, ← h₂, commutator_comm]

theorem BinaryNaturalStructure.critical_commutator_eq [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅Z R a, Z R a'⁆ = ⁅U R a, U R a'⁆ := by
  have ha' := critical_endpoint_color R a ha _ hc
  obtain ⟨hza, hza'⟩ := source.critical_Z_le_stabilizer geometry a ha a' hc
  exact structureData.commutator_eq_of_mutual_stabilizer a ha a' ha' hza hza'

theorem BinaryNaturalStructure.critical_U_index_centralizer [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    (Q R a').relIndex (U R a) =
      (centralizer (U R a' : Set (FreeAmalgam R))).relIndex (U R a) := by
  have ha' := critical_endpoint_color R a ha _ hc
  have hle : U R a ≤ stabilizer R a' :=
    (U_le_Z a).trans (source.critical_Z_le_stabilizer geometry a ha a' hc).1
  rw [← structureData.natural.centralizer a' ha', ← inf_relIndex_right]
  have heq : (stabilizer R a' ⊓ centralizer (U R a' : Set (FreeAmalgam R))) ⊓ U R a =
      centralizer (U R a' : Set (FreeAmalgam R)) ⊓ U R a := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_right
    · exact le_inf (le_inf (inf_le_right.trans hle) inf_le_left) inf_le_right
  rw [heq, inf_relIndex_right]

theorem BinaryNaturalStructure.critical_U_noncommutation [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅U R a, U R a'⁆ ≠ ⊥ := by
  rw [← structureData.critical_commutator_eq geometry a ha a' hc]
  exact source.critical_noncommutation geometry a ha hc

theorem LocalSource.critical_U_mutually_normalize [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    U R a ≤ normalizer (U R a' : Set (FreeAmalgam R)) ∧
      U R a' ≤ normalizer (U R a : Set (FreeAmalgam R)) := by
  obtain ⟨hza, hza'⟩ := source.critical_Z_le_stabilizer geometry a ha a' hc
  exact ⟨(U_le_Z a).trans (hza.trans (U_normalized a')),
    (U_le_Z a').trans (hza'.trans (U_normalized a))⟩

theorem BinaryNaturalStructure.critical_Z_index_eq_U [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    (Q R a').relIndex (Z R a) = (Q R a').relIndex (U R a) := by
  have ha' := critical_endpoint_color R a ha _ hc
  obtain ⟨hza, hza'⟩ := source.critical_Z_le_stabilizer geometry a ha a' hc
  have hD : Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) ≤ Q R a' := by
    rw [← source.C_eq_Q geometry.radical_ne_bot a' ha']
    exact le_inf (inf_le_left.trans hza) (inf_le_right.trans (centralizer_le hza'))
  have hcover : U R a ⊔ (Q R a' ⊓ Z R a) = Z R a := by
    apply le_antisymm (sup_le (U_le_Z a) inf_le_right)
    conv_lhs => rw [structureData.decomposition_at a ha]
    exact sup_le le_sup_left ((le_inf hD inf_le_left).trans le_sup_right)
  let K := (Q R a').subgroupOf (Z R a)
  let A := (U R a).subgroupOf (Z R a)
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hza.trans (Q_normalized R a'))
  have hsup : A ⊔ K = ⊤ := by
    have hh := congrArg (fun B : Subgroup (FreeAmalgam R) => B.subgroupOf (Z R a)) hcover
    simpa only [subgroupOf_sup (U_le_Z a) inf_le_right, inf_subgroupOf_right,
      subgroupOf_self] using hh
  have hh := relIndex_sup_right A K
  rw [hsup, relIndex_top_right, relIndex_subgroupOf (U_le_Z a)] at hh
  exact hh

theorem Geometry.Z_le_stabilizer_of_dist_le_b (geometry : Geometry R)
    (a : Vertex R) (ha : color R a = false) (c : Vertex R)
    (hd : (cosetGraph R).dist a c ≤ geometry.b R) : Z R a ≤ stabilizer R c := by
  apply Z_le_stabilizer_of_dist_le a (geometry.exists_critical a ha)
  rwa [geometry.distance_constant a ha]

theorem Geometry.ball_Z_le_stabilizer (geometry : Geometry R)
    (hb : 4 ≤ geometry.b R) (a c d : Vertex R) (hc : color R c = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hda : (cosetGraph R).dist d a ≤ 2) :
    Z R c ≤ stabilizer R d := by
  apply geometry.Z_le_stabilizer_of_dist_le_b c hc d
  have ht : (cosetGraph R).dist c d ≤
      (cosetGraph R).dist c a + (cosetGraph R).dist a d :=
    (cosetGraph_connected R).dist_triangle
  rw [SimpleGraph.dist_comm (u := a) (v := d)] at ht
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
