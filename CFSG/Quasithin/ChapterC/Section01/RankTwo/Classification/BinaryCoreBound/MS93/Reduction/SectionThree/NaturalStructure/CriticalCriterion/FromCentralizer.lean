module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion

/-!
# Critical-distance four from the actual edge centralizer

This extension exposes exactly the group-independent hypotheses in MS93
(2.3). The edge centralizer equality replaces the SL3-specific source record
in the existing escape and normality proofs. All subgroups, actions and
critical distances remain the original free-holomorph definitions.

The symplectic A6 branch supplies the generation and two commutator controls;
its natural-layer producer supplies the edge centralizer equality. No local
module classification is assumed by this geometric criterion.

Source: Meierfrankenfeld--Stellmacher (1993), (2.3), printed pp.857--859.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion.FromCentralizer
open NormalizerTransfer CriticalCriterion
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- If the nearby Z-layer stays in the kernel two before the endpoint, source
(c) forces the forbidden normalization. This is the algebraic step in (2). -/
theorem normalizes_of_not_critical (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a a' d e : Vertex R} (ha : color R a = false)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (hda : (cosetGraph R).dist d a = 2)
    (he : (cosetGraph R).dist e a' = 2)
    (hpath : (cosetGraph R).dist a e + 2 = (cosetGraph R).dist a a')
    {W : Subgroup (FreeAmalgam R)} (hW : CommutatorWitness R a a' W)
    (hZ : Z R d ≤ Q R e) : W ≤ normalizer (Z R d ⊔ X R a : Subgroup (FreeAmalgam R)) := by
  have ha' := critical_endpoint_color R a ha _ hc
  have hd : color R d = false := (color_eq_of_dist_even R d a (by rw [hda]; decide)).trans ha
  obtain ⟨u, heu, ha'u⟩ := exists_common_neighbor_of_dist_two R e a' he
  have hdu : (cosetGraph R).dist a u + 1 = (cosetGraph R).dist a a' := by
    have heu1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr heu)
    have hua'1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R ha'u))
    have hh := (cosetGraph_connected R).dist_triangle (u := a) (v := e) (w := u)
    have hh' := (cosetGraph_connected R).dist_triangle (u := a) (v := u) (w := a')
    omega
  have hu : color R u = true := by
    have hn := adjacent_color_ne R ha'u
    cases h : color R u <;> simp_all
  have hcomm := hW.bound u ⟨ha'u, hdu⟩ (Z R d)
    (hZ.trans (Q_le_adjacent_h R hu heu)) (frattini_Z_sup_X_eq_bot R geometry hb a d ha hda)
  have hXa' : X R a' ≤ stabilizer R a := by
    obtain ⟨t, hat, hta'⟩ := exists_adjacent_dist_sub_one R a a' (by
      rw [hc.1, geometry.distance_constant a ha]
      change 0 < geometry.b R
      omega)
    exact (X_le_Q_of_dist_lt R geometry hC a' ha' t (by
      rw [geometry.distance_constant a' ha', SimpleGraph.dist_comm]
      have hh := hc.1.trans (geometry.distance_constant a ha)
      omega)).trans (edge_le_stabilizer R ha hat)
  have h₁ : ⁅X R a, X R a'⁆ ≤ X R a :=
    le_normalizer_iff_commutator_le_left.mp (hXa'.trans (X_normalized R a))
  have h₂ : ⁅Z R d, X R a' ⊓ Q R a⁆ ≤ Z R d :=
    le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans ((Q_le_stabilizer_of_dist_two R a d ha (by
        rwa [SimpleGraph.dist_comm])).trans (Z_normalized R d)))
  have hY : ⁅Z R d, W⁆ ≤ Z R d ⊔ X R a :=
    hcomm.trans (sup_le (h₁.trans le_sup_right) (h₂.trans le_sup_left))
  have hWX : W ≤ normalizer (X R a : Set (FreeAmalgam R)) :=
    hW.le_X.trans (hXa'.trans (X_normalized R a))
  apply le_normalizer_iff.mpr
  intro w hw x hx
  have hmapZ : (Z R d).map (MulAut.conj w).toMonoidHom ≤ Z R d ⊔ X R a := by
    rintro _ ⟨z, hz, rfl⟩
    have hh := (Z R d ⊔ X R a).mul_mem
      (hY (by rw [commutator_comm]; exact commutator_mem_commutator hw hz))
      (mem_sup_left hz)
    simpa [commutatorElement_def, mul_assoc] using hh
  have hmapX : (X R a).map (MulAut.conj w).toMonoidHom ≤ Z R d ⊔ X R a := by
    exact (mem_normalizer_iff_map_conj_eq.mp (hWX hw)).le.trans le_sup_right
  have hmap : (Z R d ⊔ X R a).map (MulAut.conj w).toMonoidHom ≤ Z R d ⊔ X R a := by
    rw [Subgroup.map_sup]
    exact sup_le hmapZ hmapX
  exact hmap (mem_map_of_mem (MulAut.conj w).toMonoidHom hx)

/-- Source (2.3), proof step (2): simultaneous escape produces a new critical
pair two steps back and preserves failure to normalize the chosen N. -/
theorem escape_pair (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (hgen : Generation R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a')
    (e : Vertex R) (he : (cosetGraph R).dist e a' = 2)
    (hpath : (cosetGraph R).dist a e + 2 = (cosetGraph R).dist a a')
    (d : Vertex R) (hdt : Adjacent R d t) (hda : (cosetGraph R).dist d a = 2)
    (hnot : ¬ ((Z R d ⊔ X R a).subgroupOf (stabilizer R a)).Normal)
    (N : Subgroup (FreeAmalgam R)) (hNT : N ≤ Q R t)
    (hN : (N.subgroupOf (Q R t)).Normal)
    (hNG : ¬ (N.subgroupOf (stabilizer R a)).Normal)
    (W : Subgroup (FreeAmalgam R)) (hW : CommutatorWitness R a a' W) :
    ∃ (f : FreeAmalgam R) (_hf : f ∈ stabilizer R a)
      (hd : color R (act R f d) = false),
      CriticalPair R (act R f d) e (geometry.exists_critical _ hd) ∧
        ¬ W ≤ normalizer (rightConjugate N f) := by
  have hd : color R d = false := (color_eq_of_dist_even R d a (by rw [hda]; decide)).trans ha
  have ha' := critical_endpoint_color R a ha _ hc
  have hbd : 0 < criticalDistance R d (geometry.exists_critical d hd) := by
    rw [geometry.distance_constant d hd]
    change 0 < geometry.b R
    omega
  have hWT : W ≤ Q R t := hW.le_X.trans
    (X_le_Q_of_dist_lt R geometry hC a' ha' t (by
      rw [geometry.distance_constant a' ha', SimpleGraph.dist_comm]
      have hh := hc.1.trans (geometry.distance_constant a ha)
      omega))
  have hZT : Z R d ⊔ X R a ≤ Q R t :=
    sup_le ((geometry.omega_bound d hd hbd).trans (X_le_edge R hd hdt))
      (X_le_edge R ha hat)
  have hnorm : ((Z R d ⊔ X R a).subgroupOf (Q R t)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    exact (le_inf ((edge_le_stabilizer R hd hdt).trans (Z_normalized R d))
      ((edge_le_stabilizer R ha hat).trans (X_normalized R a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨f, hf, hfZ, hfN⟩ := simultaneous_escape W (stabilizer R a) (Q R t)
    (Z R d ⊔ X R a) N (edge_le_stabilizer R ha hat) hZT hNT hnorm hN hnot hNG
    (hgen.of_subgroup R ha hat hWT hW.not_le_Q)
  have hfix : act R f a = a := hf
  have hfd : color R (act R f d) = false := by rwa [action_preserves_color]
  have hdist : (cosetGraph R).dist (act R f d) a = 2 := by
    rw [← hfix, dist_act]; exact hda
  have hZ : ¬ Z R (act R f d) ≤ Q R e := by
    intro h
    apply hfZ
    have heq : rightConjugate (Z R d ⊔ X R a) f = Z R (act R f d) ⊔ X R a := by
      rw [rightConjugate, Subgroup.map_sup, ← Z_act, ← X_act, hfix]
    rw [heq]
    exact normalizes_of_not_critical R hC geometry hb ha hc hdist he hpath hW h
  refine ⟨f, hf, hfd, ⟨?_, hZ⟩, hfN⟩
  apply le_antisymm
  · have ht := (cosetGraph_connected R).dist_triangle (u := act R f d) (v := a) (w := e)
    rw [geometry.distance_constant _ hfd]
    have hh := hc.1.trans (geometry.distance_constant a ha)
    omega
  · exact criticalDistance_le R _ _ hZ

/-- A conjugate of the forward nonnormal product supplies the neighbor needed
in step (2), without using the later universal escape theorem. -/
theorem exists_nonnormal_neighbor (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a') :
    ∃ d, Adjacent R d t ∧ (cosetGraph R).dist d a = 2 ∧
      ¬ ((Z R d ⊔ X R a).subgroupOf (stabilizer R a)).Normal := by
  have hb' : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  obtain ⟨c, htc, hca'⟩ := exists_adjacent_dist_sub_one R t a' (by omega)
  have hac : (cosetGraph R).dist a c = 2 := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr htc)
    have hh := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := c)
    have hh' := (cosetGraph_connected R).dist_triangle (u := a) (v := c) (w := a')
    omega
  have hfwd := critical_nonnormal_forward R geometry hC
    a ha (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide : 0 < 2) hb)
    a' hc c hac (by omega)
  obtain ⟨f, hft, hfc⟩ := stabilizer_transitive_neighbors R t htc (adjacent_symm R hat)
  refine ⟨act R f a, ?_, ?_, ?_⟩
  · have htfix : act R f t = t := hft
    rw [← htfix]
    exact (adjacent_act_iff R f a t).mpr hat
  · calc
      (cosetGraph R).dist (act R f a) a =
          (cosetGraph R).dist (act R f a) (act R f c) := congrArg _ hfc.symm
      _ = (cosetGraph R).dist a c := dist_act R f a c
      _ = 2 := hac
  · intro hn
    apply hfwd.2
    apply (normal_map_iff (Z R a ⊔ X R c) (stabilizer R c) hfwd.1 (MulAut.conj f⁻¹)).mp
    have hmap : (Z R a ⊔ X R c).map (MulAut.conj f⁻¹).toMonoidHom =
        Z R (act R f a) ⊔ X R a := by
      rw [Subgroup.map_sup, ← Z_act, ← X_act, hfc]
    rw [hmap, ← stabilizer_act, hfc]
    exact hn

/-- Source (2.3), step (3), for every critical pair. The escape used in
source 2.2(v) is derived here from (b)--(c), not taken from source 4.3. -/
theorem criticalEscape (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : Generation R) (hcomm : CommutatorControl R geometry) :
    Factorization.CriticalEscape R geometry := by
  intro a ha a' hc e he hpath
  have hb' : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  obtain ⟨t, hat, hta'⟩ := exists_adjacent_dist_sub_one R a a' (by omega)
  obtain ⟨d, hdt, hda, hnot⟩ := exists_nonnormal_neighbor R hC geometry hb a ha a' hc t hat hta'
  obtain ⟨W, hW⟩ := hcomm a ha a' hc
  have ha' := critical_endpoint_color R a ha _ hc
  have hWT : W ≤ Q R t := hW.le_X.trans
    (X_le_Q_of_dist_lt R geometry hC a' ha' t (by
      rw [geometry.distance_constant a' ha', SimpleGraph.dist_comm]
      change (cosetGraph R).dist t a' < geometry.b R
      omega))
  have hNG : ¬ ((Q R t).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    apply hW.not_le_Q
    exact hWT.trans (le_Q_of_normal_edge R a t hat (Q R t)
      (le_inf (edge_le_stabilizer R ha hat) (fun _ hx => hx.1)) hn)
  obtain ⟨f, hf, hd, hpair, _⟩ := escape_pair R hC geometry hb hgen a ha a' hc t hat hta'
    e he hpath d hdt hda hnot (Q R t) le_rfl
    (normal_subgroupOf_of_le_normalizer (Q R t).le_normalizer) hNG W hW
  intro hV
  apply hpair.2
  apply le_trans ?_ hV
  apply le_iSup_of_le (act R f d)
  apply le_iSup_of_le
    (show (cosetGraph R).dist (act R f d) a ≤ 2 from by
      have hfix : act R f a = a := hf
      rw [← hfix, dist_act, hda])
  exact le_rfl


/-- Source (2.3), proof step (4): the given single-edge witness is normal at
the second vertex of each critical path through that edge. -/
theorem normal_at_second (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : Generation R) (hcomm : CommutatorControl R geometry)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t c : Vertex R) (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hac : (cosetGraph R).dist a c = 2)
    (hpath : (cosetGraph R).dist c a' + 2 = (cosetGraph R).dist a a')
    (A : Subgroup (FreeAmalgam R)) (hA : EdgeWitness R geometry a t A) :
    A ≤ stabilizer R c ∧ (A.subgroupOf (stabilizer R c)).Normal := by
  have hpos : 0 < geometry.b R := by omega
  have hAc : A ≤ stabilizer R c :=
    (hA.le_X.trans (X_le_Q_of_dist_lt R geometry hC a ha c (by
      rw [geometry.distance_constant a ha]
      change (cosetGraph R).dist a c < geometry.b R
      omega))).trans (fun _ hx => hx.1)
  refine ⟨hAc, ?_⟩
  by_contra hnotAc
  have hb' : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  have hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct))
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected R).dist_triangle (u := t) (v := c) (w := a')
    omega
  obtain ⟨e, he, hae⟩ := exists_two_before R a a' (by omega)
  obtain ⟨f, hft, hfc⟩ := stabilizer_transitive_neighbors R t (adjacent_symm R hct)
    (adjacent_symm R hat)
  have hfix : act R f t = t := hft
  have hdat : Adjacent R (act R f a) t := by
    rw [← hfix]
    exact (adjacent_act_iff R f a t).mpr hat
  have hda : (cosetGraph R).dist (act R f a) a = 2 := by
    calc
      _ = (cosetGraph R).dist (act R f a) (act R f c) := congrArg _ hfc.symm
      _ = (cosetGraph R).dist a c := dist_act R f a c
      _ = 2 := hac
  have hfwd := critical_nonnormal_forward R geometry hC a ha (by
    rw [geometry.distance_constant a ha]; exact hpos) a' hc c hac hpath
  have hnotZ : ¬ ((Z R (act R f a) ⊔ X R a).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    apply hfwd.2
    apply (normal_map_iff (Z R a ⊔ X R c) (stabilizer R c) hfwd.1 (MulAut.conj f⁻¹)).mp
    have hmap : (Z R a ⊔ X R c).map (MulAut.conj f⁻¹).toMonoidHom =
        Z R (act R f a) ⊔ X R a := by
      rw [Subgroup.map_sup, ← Z_act, ← X_act, hfc]
    rw [hmap, ← stabilizer_act, hfc]
    exact hn
  have hAf := hA.conjugate R ha hat f
  rw [hfix] at hAf
  have hdf : color R (act R f a) = false := by rwa [action_preserves_color]
  have hAfnot : ¬ ((rightConjugate A f).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    apply hnotAc
    apply (normal_map_iff A (stabilizer R c) hAc (MulAut.conj f⁻¹)).mp
    rw [← stabilizer_act, hfc]
    exact hn
  obtain ⟨W, hW⟩ := hcomm a ha a' hc
  obtain ⟨g, hg, hdg, hpair, hn⟩ := escape_pair R hC geometry hb hgen a ha a' hc t hat hta'
    e he hae (act R f a) hdat hda hnotZ (rightConjugate A f)
    (hAf.le_edge R hdf hdat) hAf.normal_edge hAfnot W hW
  have hAfg := hAf.conjugate R hdf hdat g
  have hsmall := hAfg.le_far_X R hC hpos hdg e hpair
    (moved_edge_on_path R geometry hat hdat (by omega) g hg hdg hpair)
  have hecol := critical_endpoint_color R _ hdg _ hpair
  have hXe : X R e ≤ Q R a' := X_le_Q_of_dist_lt R geometry hC e hecol a' (by
    rw [geometry.distance_constant e hecol]
    change (cosetGraph R).dist e a' < geometry.b R
    omega)
  exact hn (le_normalizer_of_le_Q R (hsmall.trans hXe) hW.le_X)


private theorem edge_not_normal (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) {a a' t : Vertex R} (ha : color R a = false)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (hat : Adjacent R a t) (ht : (cosetGraph R).dist t a' + 1 = geometry.b R)
    {W : Subgroup (FreeAmalgam R)} (hW : CommutatorWitness R a a' W) :
    ¬ ((Q R t).subgroupOf (stabilizer R a)).Normal := by
  intro hn
  have ha' := critical_endpoint_color R a ha _ hc
  apply hW.not_le_Q
  have hWT : W ≤ Q R t := hW.le_X.trans
    (X_le_Q_of_dist_lt R geometry hC a' ha' t (by
      rw [geometry.distance_constant a' ha', SimpleGraph.dist_comm]
      change (cosetGraph R).dist t a' < geometry.b R
      omega))
  exact hWT.trans (le_Q_of_normal_edge R a t hat (Q R t)
    (le_inf (edge_le_stabilizer R ha hat) (fun _ hx => hx.1)) hn)

private theorem rightConjugate_cancel {G : Type*} [Group G] (A : Subgroup G) (f : G) :
    rightConjugate (rightConjugate A f) f⁻¹ = A := by
  rw [rightConjugate, rightConjugate, map_map]
  have heq : (MulAut.conj (f⁻¹)⁻¹).toMonoidHom.comp (MulAut.conj f⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  rw [heq, map_id]

/-- A conjugate normal in an overgroup containing the conjugating element
is equal to the original subgroup. No ambient normality is asserted. -/
private theorem rightConjugate_eq_of_normal {G : Type*} [Group G]
    (A K : Subgroup G) (f : G) (hf : f ∈ K)
    (hAK : rightConjugate A f ≤ K)
    (hn : ((rightConjugate A f).subgroupOf K).Normal) : rightConjugate A f = A := by
  have hnorm := (normal_subgroupOf_iff_le_normalizer hAK).mp hn
  have heq : rightConjugate (rightConjugate A f) f⁻¹ = rightConjugate A f :=
    mem_normalizer_iff_map_conj_eq.mp (hnorm (K.inv_mem (K.inv_mem hf)))
  rw [rightConjugate_cancel] at heq
  exact heq.symm

/-- The last paragraph of source (2.3): two applications of step (2), and
normality at the second vertex, exclude critical distance greater than four. -/
theorem distance_eq_four (hC : EdgeCentralizerCondition R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : Generation R) (hcomm : CommutatorControl R geometry)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a')
    (A : Subgroup (FreeAmalgam R)) (hA : EdgeWitness R geometry a t A) :
    geometry.b R = 4 := by
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hfour : 4 ≤ geometry.b R := by obtain ⟨k, hk⟩ := heven; omega
  apply Nat.le_antisymm _ hfour
  by_contra hgt
  have hlarge : 4 < geometry.b R := by omega
  have hpos : 0 < geometry.b R := by omega
  have hdist : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  obtain ⟨e, hea', hae⟩ := exists_two_before R a a' (by omega)
  obtain ⟨d₀, hd₀t, hd₀a, hnot⟩ := exists_nonnormal_neighbor R hC geometry hb a ha a' hc
    t hat hta'
  obtain ⟨W, hW⟩ := hcomm a ha a' hc
  obtain ⟨g, hg, hd, hpair, hescape⟩ := escape_pair R hC geometry hb hgen a ha a' hc
    t hat hta' e hea' hae d₀ hd₀t hd₀a hnot A (hA.le_edge R ha hat)
    hA.normal_edge hA.not_normal_vertex W hW
  let d := act R g d₀
  let s := act R g t
  have hfix : act R g a = a := hg
  have hB : EdgeWitness R geometry a s (rightConjugate A g) := by
    have hh := hA.conjugate R ha hat g
    rwa [hfix] at hh
  have hds : Adjacent R d s := (adjacent_act_iff R g d₀ t).mpr hd₀t
  have has : Adjacent R a s := by
    rw [← hfix]
    exact (adjacent_act_iff R g a t).mpr hat
  have hda : (cosetGraph R).dist d a = 2 := by
    change (cosetGraph R).dist (act R g d₀) a = 2
    rw [← hfix, dist_act]
    exact hd₀a
  have hde : (cosetGraph R).dist d e = geometry.b R :=
    hpair.1.trans (geometry.distance_constant d hd)
  have hse : (cosetGraph R).dist s e + 1 = geometry.b R :=
    moved_edge_on_path R geometry hat hd₀t (by omega) g hg hd hpair
  have hrev := critical_nonnormal_reverse R geometry hC (criticalEscape R hC geometry hb hgen hcomm)
    d hd (by rw [geometry.distance_constant d hd]; exact hpos) hpair a hda (by omega)
  obtain ⟨j, hje, haj⟩ := exists_two_before R a e (by omega)
  have hdj : (cosetGraph R).dist d j + 2 = (cosetGraph R).dist d e := by
    have hu := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := j)
    have hl := (cosetGraph_connected R).dist_triangle (u := d) (v := j) (w := e)
    omega
  have hja' : (cosetGraph R).dist j a' = 4 := by
    have hu := (cosetGraph_connected R).dist_triangle (u := j) (v := e) (w := a')
    have hl := (cosetGraph_connected R).dist_triangle (u := a) (v := j) (w := a')
    omega
  obtain ⟨W₂, hW₂⟩ := hcomm d hd e hpair
  obtain ⟨f, hf, haf, hpair₂, _⟩ := escape_pair R hC geometry hb hgen d hd e hpair
    s hds (by omega) j hje hdj a has (by rwa [SimpleGraph.dist_comm]) hrev.2
    (Q R s) le_rfl (normal_subgroupOf_of_le_normalizer (Q R s).le_normalizer)
    (edge_not_normal R hC geometry hd hpair hds hse hW₂) W₂ hW₂
  have hBf := hB.conjugate R ha has f
  have hsj : (cosetGraph R).dist (act R f s) j + 1 = geometry.b R :=
    moved_edge_on_path R geometry hds has (by omega) f hf haf hpair₂
  have hsmall := hBf.le_far_X R hC hpos haf j hpair₂ hsj
  have hjcol := critical_endpoint_color R _ haf _ hpair₂
  have hXj : X R j ≤ Q R a' := X_le_Q_of_dist_lt R geometry hC j hjcol a' (by
    rw [geometry.distance_constant j hjcol]
    change (cosetGraph R).dist j a' < geometry.b R
    omega)
  have hfd : act R f d = d := hf
  have hdsf : Adjacent R d (act R f s) := by
    rw [← hfd]
    exact (adjacent_act_iff R f d s).mpr hds
  have hafs : Adjacent R (act R f a) (act R f s) := (adjacent_act_iff R f a s).mpr has
  have hafd : (cosetGraph R).dist (act R f a) d = 2 := by
    calc
      _ = (cosetGraph R).dist (act R f a) (act R f d) := congrArg _ hfd.symm
      _ = (cosetGraph R).dist a d := dist_act R f a d
      _ = 2 := by rwa [SimpleGraph.dist_comm]
  have hpair₂dist : (cosetGraph R).dist (act R f a) j = geometry.b R :=
    hpair₂.1.trans (geometry.distance_constant _ haf)
  have hnormal := normal_at_second R hC geometry hb hgen hcomm
    (act R f a) haf j hpair₂ (act R f s) d hafs hdsf hafd (by omega)
    (rightConjugate (rightConjugate A g) f) hBf
  have hBeq := rightConjugate_eq_of_normal (rightConjugate A g) (stabilizer R d) f hf
    hnormal.1 hnormal.2
  apply hescape
  rw [← hBeq]
  exact le_normalizer_of_le_Q R (hsmall.trans hXj) hW.le_X


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion.FromCentralizer
