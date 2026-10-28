module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Action.Quotient

/-!
# The genuine midpoint and Sylow arrangement on MS93 p.907

Neighbor transitivity supplies an element of G_beta carrying alpha to the
chosen midpoint. Since the graph is a right-coset graph, its conjugation is
by the inverse element. The transported embedding has exactly G_middle as
its image and retains Q, Z, V and the original first edge layer.

The selected U_delta0 pulls back faithfully into the first parabolic core;
its displacement makes its image under the original matrix projection
nontrivial. Two distinct cores in the incident pencil intersect in Q_alpha,
so one transported opposite core is escaped by U_delta0. The full actor/core
quotient has order six; the nontrivial two-group image therefore gives an
actual Sylow two-subgroup U_delta0 Q_lambda0. All normality is relative to
that transported full actor. This supplies the selection preceding the
commutator index comparison; it does not assert that comparison.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), p.907, first paragraph.
The index-six calculation uses the existing public marked S3 projection
from Preparatory/Incident/Pairing/Transport/Natural/Kernel/FixedSummand/Action/Quotient.lean.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- An actual right-action transporter along the two-edge path through beta. -/
structure MiddleTransport (c : Vertex R) where
  element : FreeAmalgam R
  fixes_beta : element ∈ stabilizer R (beta R)
  to_middle : act R element (alpha R) = c

noncomputable def middleTransport [Finite M] {source : LocalSource L R}
    {geometry : Geometry R} {i : Bool} (p : SourceFlagPreparatoryData source geometry i) :
    MiddleTransport p.middle := by
  let h := stabilizer_transitive_neighbors R (beta R)
    (adjacent_symm R (base_adjacent R)) p.middle_neighbor
  exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

namespace MiddleTransport
variable {c : Vertex R} (t : MiddleTransport c)

def conjugation : MulAut (FreeAmalgam R) := MulAut.conj t.element⁻¹

def embedding : M →* FreeAmalgam R := t.conjugation.toMonoidHom.comp (embedM R)

theorem embedding_injective : Function.Injective t.embedding :=
  t.conjugation.injective.comp (embedM_injective R)

theorem embedding_range : t.embedding.range = stabilizer R c := by
  calc
    t.embedding.range = stabilizer R (act R t.element (alpha R)) := by
      rw [embedding, MonoidHom.range_comp, stabilizer_act, alpha, stabilizer_m_base]
      rfl
    _ = stabilizer R c := congrArg (stabilizer R) t.to_middle

theorem map_Q_alpha : (Q R (alpha R)).map t.conjugation.toMonoidHom = Q R c := by
  exact (Q_act R t.element (alpha R)).symm.trans (congrArg (Q R) t.to_middle)

theorem map_Z_alpha : (Z R (alpha R)).map t.conjugation.toMonoidHom = Z R c := by
  exact (Z_act R t.element (alpha R)).symm.trans (congrArg (Z R) t.to_middle)

theorem map_V_alpha : (V R (alpha R)).map t.conjugation.toMonoidHom = V R c := by
  exact (V_act R t.element (alpha R)).symm.trans (congrArg (V R) t.to_middle)

theorem map_Q_beta : (Q R (beta R)).map t.conjugation.toMonoidHom = Q R (beta R) := by
  change (Q R (beta R)).map (MulAut.conj t.element⁻¹).toMonoidHom = _
  rw [← Q_act, show act R t.element (beta R) = beta R from t.fixes_beta]

theorem map_V_beta : (V R (beta R)).map t.conjugation.toMonoidHom = V R (beta R) := by
  change (V R (beta R)).map (MulAut.conj t.element⁻¹).toMonoidHom = _
  rw [← V_act, show act R t.element (beta R) = beta R from t.fixes_beta]

theorem map_first_kernel (source : LocalSource L R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    (flagKernel source i).map t.conjugation.toMonoidHom = Q R (beta R) := by
  rw [hkernel, t.map_Q_beta]

/-- The second layer lies in the actual transported finite vertex group. -/
theorem second_le_range [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M)
    (hc : Adjacent R (beta R) c) : secondFlagLayer source i d ≤ t.embedding.range := by
  rw [t.embedding_range]
  exact (secondFlagLayer_le_radius source i d).trans
    ((V_le_Q geometry hlarge _ rfl).trans
      ((Q_le_adjacent_h R rfl (base_adjacent R)).trans (fun _ hx => hx.2 _ hc)))

end MiddleTransport

theorem second_not_le_middle_core [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    ¬ secondFlagLayer source i p.delta0 ≤ (Q R (alpha R)).map t.conjugation.toMonoidHom := by
  rw [t.map_Q_alpha]
  exact (Incident.displacement_iff source geometry hlarge i p.delta0 p.middle).mp p.displacement

/-- The original selected second layer, expressed in the transported M-copy. -/
noncomputable def middleLayer {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    Subgroup M := (secondFlagLayer source i p.delta0).comap t.embedding

theorem middleLayer_map [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    (middleLayer p t).map t.embedding = secondFlagLayer source i p.delta0 := by
  rw [middleLayer, map_comap_eq]
  exact inf_eq_right.mpr (t.second_le_range source geometry hlarge i p.delta0 p.middle_neighbor)

theorem MiddleTransport.map_core [Finite M] {c : Vertex R} (t : MiddleTransport c)
    (source : LocalSource L R) : (pCore 2 M).map t.embedding = Q R c := by
  rw [MiddleTransport.embedding, ← Subgroup.map_map,
    ← Q_alpha R source.two_group source.core_le]
  exact t.map_Q_alpha

theorem middleLayer_not_le_core [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    ¬ middleLayer p t ≤ pCore 2 M := by
  intro h
  have hh := map_mono (f := t.embedding) h
  rw [middleLayer_map source geometry hlarge i p t, t.map_core source] at hh
  exact (Incident.displacement_iff source geometry hlarge i p.delta0 p.middle).mp p.displacement hh

theorem middleLayer_projection_ne_bot [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    (middleLayer p t).map source.projection ≠ ⊥ := by
  intro h
  have hh := (map_eq_bot_iff (f := source.projection) _).mp h
  rw [source.projection_kernel] at hh
  exact middleLayer_not_le_core source geometry hlarge i p t hh

theorem middleLayer_le_first_core [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    middleLayer p t ≤ (parabolic source.projection source.flag i).pCoreIn 2 := by
  apply (map_le_map_iff_of_injective t.embedding_injective).mp
  rw [middleLayer_map source geometry hlarge i p t, MiddleTransport.embedding,
    ← Subgroup.map_map]
  change secondFlagLayer source i p.delta0 ≤ (flagKernel source i).map t.conjugation.toMonoidHom
  rw [t.map_first_kernel source i hkernel]
  exact (secondFlagLayer_le_radius source i p.delta0).trans
    ((V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R)))

private theorem sylow_join_of_index_six {G : Type*} [Group G] [Finite G]
    (E K : Subgroup G) [K.Normal] (hE : IsPGroup 2 E) (hK : IsPGroup 2 K)
    (hindex : K.index = 6) (hnot : ¬ E ≤ K) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = E ⊔ K := by
  have hd : K.relIndex E ∣ 6 := hindex ▸ K.relIndex_dvd_index_of_normal E
  have hthree : ¬ 3 ∣ K.relIndex E := by
    obtain ⟨n, hn⟩ := hE.exists_card_eq
    intro hh
    have hc := hh.trans (K.relIndex_dvd_card E)
    rw [hn] at hc
    exact (Nat.prime_three.coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 3 2).pow_right n)) hc
  have hne : K.relIndex E ≠ 1 := fun h => hnot (relIndex_eq_one.mp h)
  have hi : K.relIndex E = 2 := by
    have hx : K.relIndex E ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have he : Nat.divisors 6 = {1,2,3,6} := by decide
    rw [he] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · exact False.elim (hne h)
    · exact h
    · exact False.elim (hthree (h ▸ dvd_rfl))
    · exact False.elim (hthree (h ▸ (by decide : 3 ∣ 6)))
  have hj := relIndex_mul_index (show K ≤ E ⊔ K from le_sup_right)
  rw [relIndex_sup_right, hi, hindex] at hj
  have hodd : ¬ 2 ∣ (E ⊔ K).index := by
    have hh : (E ⊔ K).index = 3 := by omega
    rw [hh]
    decide
  exact ⟨(hE.to_sup_of_normal_right hK).toSylow hodd, rfl⟩

private theorem local_kernel_index_six (source : LocalSource L R) [Finite M]
    (i : Bool) (g : M) :
    (localFlagKernel source i g).relIndex (localFlagActor source i g) = 6 := by
  rw [localFlagKernel, localFlagActor]
  change ((flagKernel source i).map _).relIndex ((flagParabolic source i).map _) = 6
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj (embedM R g)).injective]
  obtain ⟨q, hq, hk⟩ := Incident.Pairing.Transport.Natural.Kernel.exists_barProjection source i
  change ((flagKernel source i).subgroupOf (flagParabolic source i)).index = 6
  rw [← hk, index_ker, MonoidHom.range_eq_top.mpr hq,
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  norm_num [Incident.Pairing.Transport.Natural.Kernel.BinaryS3.Actor,
    Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The displacement selects a genuine incident lambda whose transported core
is escaped by the original U_delta0. -/
theorem exists_middle_crossing [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    ∃ e : M, flagIncident source i 1 e ∧
      ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom := by
  obtain ⟨e, hi, _, hm, _⟩ := Incident.exists_incident_core_pencil source i
  by_cases h₀ : secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) (e 0)).map t.conjugation.toMonoidHom
  · refine ⟨e 1, hi 1, ?_⟩
    intro h₁
    apply second_not_le_middle_core source geometry hlarge i p t
    have hh := le_inf h₀ h₁
    rw [← map_inf _ _ _ t.conjugation.injective, hm 0 1 (by decide)] at hh
    exact hh
  · exact ⟨e 0, hi 0, h₀⟩

/-- The source Sylow arrangement at the transported lambda0, inside its full actor. -/
theorem exists_middle_sylow [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    ∃ e : M, flagIncident source i 1 e ∧
      ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom ∧
      ∃ S : Sylow 2 ((localFlagActor source (!i) e).map t.conjugation.toMonoidHom),
        (S : Subgroup ((localFlagActor source (!i) e).map t.conjugation.toMonoidHom)).map
          ((localFlagActor source (!i) e).map t.conjugation.toMonoidHom).subtype =
          secondFlagLayer source i p.delta0 ⊔
            (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom := by
  obtain ⟨e, he, hnot⟩ := exists_middle_crossing source geometry hlarge i p t
  let P := (localFlagActor source (!i) e).map t.conjugation.toMonoidHom
  let K := (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom
  let E := secondFlagLayer source i p.delta0
  have hKP : K ≤ P := map_mono (map_mono (flagKernel_le source (!i)))
  have hEP : E ≤ P := by
    have hEQ : E ≤ Q R (beta R) :=
      (secondFlagLayer_le_radius source i p.delta0).trans
        ((V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R)))
    exact hEQ.trans ((t.map_first_kernel source i hkernel).symm.le.trans
      (map_mono (Incident.flagKernel_le_incidentActor source i e he)))
  have hnorm : P ≤ normalizer K :=
    (map_mono ((map_mono (flagKernel_normalized source (!i))).trans
      (le_normalizer_map (MulAut.conj (embedM R e)).toMonoidHom))).trans
      (le_normalizer_map t.conjugation.toMonoidHom)
  let : (K.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hnorm
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (localFlagActor source (!i) e) :=
    Finite.of_injective (inclusion (localFlagActor_le_stabilizer source (!i) e))
      (inclusion_injective _)
  let : Finite P := Finite.of_equiv (localFlagActor source (!i) e)
    (t.conjugation.subgroupMap (localFlagActor source (!i) e)).toEquiv
  have hpE : IsPGroup 2 E :=
    (Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le
      ((secondFlagLayer_le_radius source i p.delta0).trans (V_le_Q geometry hlarge _ rfl))
  have hpK : IsPGroup 2 K := by
    exact (((pCore_isPGroup (p := 2) (G := parabolic source.projection source.flag (!i))).map
      (parabolic source.projection source.flag (!i)).subtype).map (embedM R)).map
        (MulAut.conj (embedM R e)).toMonoidHom |>.map t.conjugation.toMonoidHom
  have hindex : (K.subgroupOf P).index = 6 := by
    change K.relIndex P = 6
    rw [relIndex_map_map_of_injective _ _ t.conjugation.injective]
    exact local_kernel_index_six source (!i) e
  have hn : ¬ E.subgroupOf P ≤ K.subgroupOf P := by
    intro h
    apply hnot
    intro x hx
    exact h (show (⟨x, hEP hx⟩ : P) ∈ E.subgroupOf P from hx)
  obtain ⟨S, hS⟩ := sylow_join_of_index_six (E.subgroupOf P) (K.subgroupOf P)
    hpE.comap_subtype hpK.comap_subtype hindex hn
  refine ⟨e, he, hnot, S, ?_⟩
  rw [hS, ← subgroupOf_sup hEP hKP, map_subgroupOf_eq_of_le (sup_le hEP hKP)]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
