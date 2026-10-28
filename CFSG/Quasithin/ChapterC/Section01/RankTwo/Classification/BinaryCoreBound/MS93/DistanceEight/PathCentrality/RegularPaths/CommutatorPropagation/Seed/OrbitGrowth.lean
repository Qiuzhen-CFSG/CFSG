module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The prescribed P-orbit commutator escapes Z_a

Let P be the normalizer of the forward edge commutator inside G_a, and
W the prescribed P-orbit span of Z_(a+2). The marked natural action makes P
maximal. For any A ≤ G_a outside P, a bound [W,A] ≤ Z_a would make W Z_a
normal in G_a = ⟨P,A⟩. All G_a-conjugates of A would then normalize
Z_(a+2) Z_a. Together with Q_a these conjugates generate G_a, contradicting
the reverse nonnormality assertion of source (2.2)(v).

Transport A = Z_a' back by the prescribed edge conjugator. Covariance of
the actual commutator and normalizers gives R₀ ≰ Z_a, with R₀ exactly the
subgroup in Source.lean. CommonFacts supplies the earlier escape theorem
used by (2.2)(v). No failed-span assumption, regularity, edge equality, or
later index formula is needed for this first assertion. The remaining seed
assembly belongs to Seed.lean and the independent critical-inclusion owner.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.2)(v) and the initial R₀ calculation in (4.4.4), printed pp.856,894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth
open NormalizerTransfer
/-- A relative orbit span cannot be fixed modulo Z by an actor generating the
whole local group if one of its subgroups above Z is locally nonnormal. -/
private theorem orbit_commutator_not_le {G : Type*} [Group G]
    (F P Q Z D A W : Subgroup G)
    (hPF : P ≤ F) (hQF : Q ≤ F) (hAF : A ≤ F)
    (hZF : Z ≤ F) (hWF : W ≤ F) (hDW : D ≤ W)
    (hFZ : F ≤ normalizer (Z : Set G))
    (hPW : P ≤ normalizer (W : Set G))
    (hQD : Q ≤ normalizer (D : Set G))
    (hgen : P ⊔ A = F) (hgen' : conjugatesIn A F ⊔ Q = F)
    (hnot : ¬ F ≤ normalizer (D ⊔ Z : Subgroup G)) :
    ¬ ⁅W, A⁆ ≤ Z := by
  intro hcomm
  let J := W ⊔ Z
  have hJcomm : ⁅J, A⁆ ≤ Z := by
    have hpre : J ≤ commutatorPreimage F A Z :=
      sup_le (le_commutatorPreimage hWF hcomm)
        (le_commutatorPreimage hZF
          (le_normalizer_iff_commutator_le_left.mp (hAF.trans hFZ)))
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le F A Z hFZ)
  have hPJ : P ≤ normalizer (J : Set G) :=
    (le_inf hPW (hPF.trans hFZ)).trans (normalizer_inf_normalizer_le_normalizer_sup W Z)
  have hAJ : A ≤ normalizer (J : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hJcomm.trans le_sup_right)
  have hFJ : F ≤ normalizer (J : Set G) := by
    rw [← hgen]
    exact sup_le hPJ hAJ
  have hNK : conjugatesIn A F ≤ normalizer (D ⊔ Z : Subgroup G) := by
    apply iSup_le
    intro g
    have hJ := mem_normalizer_iff_map_conj_eq.mp (hFJ (F.inv_mem g.property))
    have hZ := mem_normalizer_iff_map_conj_eq.mp (hFZ (F.inv_mem g.property))
    change J.map (MulAut.conj (g : G)⁻¹).toMonoidHom = J at hJ
    change Z.map (MulAut.conj (g : G)⁻¹).toMonoidHom = Z at hZ
    have hc : ⁅J, rightConjugate A g⁆ ≤ Z := by
      rw [← hJ, rightConjugate, ← map_commutator, ← hZ]
      exact map_mono hJcomm
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono (sup_le_sup_right hDW Z) le_rfl).trans
      (hc.trans le_sup_right)
  apply hnot
  rw [← hgen']
  exact sup_le hNK ((le_inf hQD (hQF.trans hFZ)).trans
    (normalizer_inf_normalizer_le_normalizer_sup D Z))


variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The prescribed relative orbit has nontrivial displacement modulo Z_a
under every local actor outside the prescribed edge normalizer. -/
theorem prescribedSpan_commutator_not_le [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a')
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ stabilizer R a)
    (hn : ¬ A ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R))) :
    ¬ ⁅prescribedSpan p, A⁆ ≤ Z R a := by
  have hb := common.large_distance
  have hl := p.length_eq_b
  let P := stabilizer R a ⊓
    normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R))
  have hadj : Adjacent R a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 := p.dist_start (by omega)
  have hQP : Q R a ≤ P := by
    have hEZ := (Escape.EdgeTransfer.edge_commutator_le_natural hb
      (moduleFacts common) a _ p.start_color hadj).trans (U_le_Z R a)
    exact le_inf (fun _ hx => hx.1)
      (((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes a p.start_color))).trans (centralizer_le hEZ)).trans
          (Subgroup.centralizer_le_normalizer _))
  have hnotQ : ¬ A ≤ Q R a := fun h => hn (h.trans hQP)
  have hPW : P ≤ normalizer (prescribedSpan p : Set (FreeAmalgam R)) := by
    have he : prescribedSpan p = conjugatesIn (Z R (p.walk.getVert 2)) P := by
      simp only [prescribedSpan, conjugatesIn, rightConjugate, Z_act, P]
    rw [he]
    exact conjugatesIn_normalized _ _
  have hDW : Z R (p.walk.getVert 2) ≤ prescribedSpan p := by
    have hh := le_iSup (fun g : P =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2))) 1
    simpa only [prescribedSpan, Subgroup.coe_one, act_one, P] using hh
  have hWF : prescribedSpan p ≤ stabilizer R a :=
    ((prescribedSpan_le_radius p (by omega)).trans (V_le_Q R p.start_color hb)).trans
      (fun _ hx => hx.1)
  have hQD : Q R a ≤ normalizer (Z R (p.walk.getVert 2) : Set (FreeAmalgam R)) :=
    (Q_le_stabilizer_of_dist_two R a _ p.start_color hd).trans (Z_normalized R _)
  have hnot : ¬ stabilizer R a ≤
      normalizer (Z R (p.walk.getVert 2) ⊔ Z R a : Subgroup (FreeAmalgam R)) := by
    have hpos : 0 < criticalDistance R a (geometry.exists_critical a p.start_color) := by
      rw [geometry.distance_constant a p.start_color]
      exact lt_trans (by decide : 0 < 2) hb
    have hrev := critical_nonnormal_reverse R geometry common.centralizer common.escape
      a p.start_color hpos p.critical (p.walk.getVert 2) hd (by
        rw [p.dist_end 2, ← p.shortest]
        omega)
    rw [common.X_eq_Z a p.start_color] at hrev
    exact fun h => hrev.2 (normal_subgroupOf_of_le_normalizer h)
  exact orbit_commutator_not_le (stabilizer R a) P (Q R a) (Z R a)
    (Z R (p.walk.getVert 2)) A (prescribedSpan p)
    inf_le_left (fun _ hx => hx.1) hA (Z_le_stabilizer R a) hWF hDW
    (Z_normalized R a) hPW hQD
    (edge_normalizer_sup_eq common p.start_color hadj hA hn)
    (Escape.Initial.local_conjugate_generation source a p.start_color A hA hnotQ) hnot

private theorem map_inverse_conjugate_cancel {G : Type*} [Group G]
    (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [he, Subgroup.map_id]

/-- The first R₀ assertion in MS93 (4.4.4), for the literal transported
prescribed span. Failed escape, regular turns and the later edge equalities
are unnecessary for this initial noncontainment. -/
theorem failedSpanCommutator_not_le_start_Z [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') {t : Vertex R}
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom =
      edgeCommutator R a t) :
    ¬ failedSpanCommutator p g ≤ Z R a := by
  let A := (Z R a').map (MulAut.conj g).toMonoidHom
  have hlocal := (source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical).2
  have hA : A ≤ stabilizer R a := (map_mono hlocal).trans
    (mem_normalizer_iff_map_conj_eq.mp ((stabilizer R a).le_normalizer hg)).le
  have hback : A.map (MulAut.conj g⁻¹).toMonoidHom = Z R a' := by
    simpa only [inv_inv] using map_inverse_conjugate_cancel (Z R a') g⁻¹
  have hnot : ¬ A ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R)) := by
    intro h
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (h.trans inf_le_right)).trans (le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    rw [hback, hge] at hh
    exact hn (le_inf hlocal hh)
  intro h
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h
  have hZmap : (Z R a).map (MulAut.conj g).toMonoidHom = Z R a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hg)
  rw [failedSpanCommutator, map_commutator, map_inverse_conjugate_cancel, hZmap] at hh
  exact prescribedSpan_commutator_not_le common p hA hnot hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth
