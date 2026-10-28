module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Escape
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Strict growth of the initial radius commutator

For a contrary critical configuration, R₀ = [V_a,Z_a'] cannot lie in Z_a.
Indeed, such containment makes every G_a-conjugate of Z_a' normalize each
nearby product Z_d Z_a. Critical reversal puts Z_a' outside Q_a. Its local
conjugates generate G_a modulo Q_a, since the actual marked quotient is
SL₃(2). The group Q_a also normalizes Z_d Z_a, so this product would be
normal in G_a, contrary to the earlier critical-path nonnormality theorem
and X_a = Z_a.

Since the critical commutator R = [Z_a,Z_a'] lies in Z_a, this proves
R₀ ≠ R. Initial.Bounds and Initial.Edges turn that strict growth into the
numerical and edge assertions of (4.3.1)(i)--(ii). No natural-section,
normalization-transfer, or later escape conclusion enters the argument.

The printed citation "(3.4)(i)" on p.883 has no matching numbered clause.
The proof here supplies the binary normal-generation argument directly;
it does not invoke (3.3) with an unproved commutator-noncontainment premise.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.2)(iv), (2.3)(b), and (4.3.1)(i)--(ii), pp.856--857, 882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

-- Transport the source quotient along the genuine vertex embedding.
-- This is the local calculation also used in SectionThree.NormalizationTransfer.
private theorem local_projection (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  let S := stabilizer R (mVertex R g)
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective R)
  have hrange : f.range = S := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  let e : M ≃* S := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have he : S.subtype.comp e.toMonoidHom = f := by ext x; rfl
  have hQ : (pCore 2 M).map e.toMonoidHom =
      (Q R (mVertex R g)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map, he, map_subgroupOf_eq_of_le (show Q R (mVertex R g) ≤ S from fun _ hx => hx.1)]
    rw [show f = (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R) from rfl, ← map_map,
      ← Q_alpha R source.two_group source.core_le]
    have hh := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using hh.symm
  refine ⟨source.projection.comp e.symm.toMonoidHom,
    source.projection_surjective.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, source.projection_kernel, ← hQ]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change e.symm (e y) ∈ pCore 2 M
    rw [MulEquiv.symm_apply_apply]
    exact hy

/-- In the actual local SL₃(2) quotient, any subgroup escaping Q_a
normally generates modulo Q_a. All normality is relative to G_a. -/
theorem local_conjugate_generation (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a) (hnot : ¬ A ≤ Q R a) :
    conjugatesIn A (stabilizer R a) ⊔ Q R a = stabilizer R a := by
  let F := stabilizer R a
  let N := conjugatesIn A F
  have hQF : Q R a ≤ F := fun _ hx => hx.1
  have hNF : N ≤ F := conjugatesIn_le A F hA
  have hAN : A ≤ N := by
    intro x hx
    apply le_iSup (fun g : F => rightConjugate A g) (1 : F)
    exact ⟨x, hx, by simp⟩
  let : (N.subgroupOf F).Normal := normal_subgroupOf_of_le_normalizer
    (conjugatesIn_normalized A F)
  obtain ⟨π, hπ, hker⟩ := local_projection source a ha
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : ((N.subgroupOf F).map π).Normal :=
    (inferInstance : (N.subgroupOf F).Normal).map π hπ
  have htop : (N.subgroupOf F).map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with hh | hh
    · have hNker := (Subgroup.map_eq_bot_iff (N.subgroupOf F)).mp hh
      rw [hker] at hNker
      exact (hnot (fun x hx => hNker (show (⟨x, hNF (hAN hx)⟩ : F) ∈
        N.subgroupOf F from hAN hx))).elim
    · exact hh
  have hjoin : N.subgroupOf F ⊔ (Q R a).subgroupOf F = ⊤ := by
    have hh := congrArg (Subgroup.comap π) htop
    simpa only [comap_map_eq, hker, comap_top] using hh
  have hh := congrArg (Subgroup.map F.subtype) hjoin
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hNF,
    map_subgroupOf_eq_of_le hQF, ← MonoidHom.range_eq_map, range_subtype] using hh

private theorem conjugates_normalize_of_commutator_le {G : Type*} [Group G]
    (A F W Z K : Subgroup G)
    (hFW : F ≤ normalizer (W : Set G)) (hFZ : F ≤ normalizer (Z : Set G))
    (hZK : Z ≤ K) (hKW : K ≤ W) (hcomm : ⁅W, A⁆ ≤ Z) :
    conjugatesIn A F ≤ normalizer (K : Set G) := by
  apply iSup_le
  intro g
  have hW := mem_normalizer_iff_map_conj_eq.mp (hFW (F.inv_mem g.property))
  have hZ := mem_normalizer_iff_map_conj_eq.mp (hFZ (F.inv_mem g.property))
  change W.map (MulAut.conj (g : G)⁻¹).toMonoidHom = W at hW
  change Z.map (MulAut.conj (g : G)⁻¹).toMonoidHom = Z at hZ
  have hc : ⁅W, rightConjugate A g⁆ ≤ Z := by
    rw [← hW, rightConjugate, ← map_commutator, ← hZ]
    exact map_mono hcomm
  exact le_normalizer_iff_commutator_le_left.mpr
    ((commutator_mono hKW le_rfl).trans (hc.trans hZK))

/-- The radius commutator escapes the starting Z-layer. The contradiction
uses the earlier nonnormal neighbor, with X_a = Z_a supplied by ModuleFacts. -/
theorem radius_not_le_start_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) : ¬ radiusCommutator p.a p.a' ≤ Z R p.a := by
  intro hcomm
  have hb' : 0 < criticalDistance R p.a (geometry.exists_critical p.a p.color_a) := by
    rw [geometry.distance_constant p.a p.color_a]
    change 0 < geometry.b R
    omega
  obtain ⟨t, hat, _, hta', _⟩ := critical_first_neighbor R geometry p.a p.color_a hb' p.critical
  obtain ⟨d, _, hda, hnot⟩ := CriticalCriterion.exists_nonnormal_neighbor R source geometry hb
    p.a p.color_a p.a' p.critical t hat hta'
  rw [modules.X_eq_Z p.a p.color_a] at hnot
  have hKQ : Q R p.a ≤ normalizer ((Z R d ⊔ Z R p.a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (le_inf ((Q_le_stabilizer_of_dist_two R p.a d p.color_a (by
      rwa [SimpleGraph.dist_comm])).trans (Z_normalized R d))
      ((show Q R p.a ≤ stabilizer R p.a from fun _ hx => hx.1).trans
        (Z_normalized R p.a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hKW : Z R d ⊔ Z R p.a ≤ V R p.a :=
    sup_le (le_iSup_of_le d (le_iSup_of_le hda.le le_rfl)) (Z_le_VBall R p.a 2)
  have hNC := conjugates_normalize_of_commutator_le (Z R p.a') (stabilizer R p.a)
    (V R p.a) (Z R p.a) (Z R d ⊔ Z R p.a) (V_normalized p.a) (Z_normalized R p.a)
    le_sup_right hKW hcomm
  have hgen := local_conjugate_generation source p.a p.color_a (Z R p.a')
    p.end_Z_le_start_stabilizer (source.critical_reverse geometry p.a p.color_a p.a'
      p.end_color p.critical).2
  apply hnot
  apply normal_subgroupOf_of_le_normalizer
  rw [← hgen]
  exact sup_le hNC hKQ

/-- The strict growth needed by the numerical clauses (4.3.1)(i)--(ii),
with exactly the source, geometry, module and contrary-configuration inputs. -/
theorem radius_ne_critical (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) : radiusCommutator p.a p.a' ≠ criticalCommutator p.a p.a' := by
  intro h
  apply radius_not_le_start_Z source hb modules p
  rw [h]
  exact p.critical_le_radius_inf_start.trans inf_le_right

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
