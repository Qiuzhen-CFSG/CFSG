module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.SourceOffenders

/-!
# Escape two steps before a critical endpoint

Source (2.3)(b) generates the vertex group from the relative conjugates of
any edge subgroup escaping Q. Simultaneous escape is applied to the chosen
edge-normal subgroup and a conjugate of the forward nonnormal product.
If its moved Z-layer stays in the earlier kernel, (c) and the elementary
join force normalization, a contradiction. Critical minimality then gives
an actual new critical pair. Taking the whole edge kernel as N proves the
universal escape needed by source 2.2(v).

All groups lie in the original infinite amalgam; only local stabilizers
are finite. No later 4.3 escape or module classification is assumed.
Source: Meierfrankenfeld--Stellmacher (1993), (2.3), proof (2)--(3), p.858.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- Source (b) also generates from any subgroup of the edge kernel escaping Q. -/
theorem Generation.of_subgroup (hgen : Generation R) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    {W : Subgroup (FreeAmalgam R)} (hWT : W ≤ Q R t) (hWQ : ¬ W ≤ Q R a) :
    conjugatesIn W (stabilizer R a) ⊔ Q R t = stabilizer R a := by
  classical
  obtain ⟨x, hxW, hxQ⟩ : ∃ x ∈ W, x ∉ Q R a := by
    by_contra h
    apply hWQ
    intro x hx
    exact not_not.mp (fun hn => h ⟨x, hx, hn⟩)
  apply le_antisymm
  · exact sup_le (conjugatesIn_le _ _ (hWT.trans (edge_le_stabilizer R ha hat)))
      (edge_le_stabilizer R ha hat)
  · apply (hgen a t ha hat x (hWT hxW) hxQ).ge.trans
    apply sup_le_sup_right
    apply iSup_le
    intro f
    exact (map_mono (zpowers_le.mpr hxW)).trans
      (le_iSup (fun f : stabilizer R a => rightConjugate W f) f)

/-- Mapping a normal subgroup by an automorphism preserves relative normality. -/
theorem normal_map_iff {G : Type*} [Group G] (A K : Subgroup G)
    (hAK : A ≤ K) (f : MulAut G) :
    ((A.map f.toMonoidHom).subgroupOf (K.map f.toMonoidHom)).Normal ↔
      (A.subgroupOf K).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (map_mono hAK),
    normal_subgroupOf_iff_le_normalizer hAK]
  constructor
  · intro h
    apply le_normalizer_iff.mpr
    intro k hk a ha
    have hh := le_normalizer_iff.mp h (f k)
      (mem_map_of_mem f.toMonoidHom hk) (f a) (mem_map_of_mem f.toMonoidHom ha)
    obtain ⟨b, hb, heq⟩ := hh
    change f b = f k * f a * (f k)⁻¹ at heq
    have heq' : b = k * a * k⁻¹ := f.injective (by
      rw [map_mul, map_mul, map_inv]; exact heq)
    exact heq' ▸ hb
  · intro h
    exact (map_mono h).trans (A.le_normalizer_map f.toMonoidHom)

/-- The elementary join used when the conjugate fails to be critical. -/
theorem frattini_Z_sup_X_eq_bot (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a d : Vertex R) (ha : color R a = false)
    (hda : (cosetGraph R).dist d a = 2) :
    frattini ↥(Z R d ⊔ X R a) = ⊥ := by
  have hd : color R d = false := (color_eq_of_dist_even R d a (by rw [hda]; decide)).trans ha
  have hbd : 0 < criticalDistance R d (geometry.exists_critical d hd) := by
    rw [geometry.distance_constant d hd]
    exact lt_trans (by decide : 0 < 2) hb
  have hZ : Z R d ≤ Q R a := Z_le_Q_of_dist_lt R d _ (by
    rw [hda, geometry.distance_constant d hd]; exact hb)
  let : IsElementaryAbelian 2 (Z R d) := Z_elementary_of_positive R geometry d hd hbd
  let : IsElementaryAbelian 2 (X R a) := X_elementary R a
  let : IsElementaryAbelian 2 ↥(Z R d ⊔ X R a) :=
    IsElementaryAbelian.sup_of_le_centralizer (by
      intro x hx z hz
      exact (mem_omegaCenter_iff.mp hx).2.2 z (hZ hz))
  let : Fact (IsPGroup 2 ↥(Z R d ⊔ X R a)) := ⟨IsElementaryAbelian.isPGroup _ _⟩
  let : Finite ↥(Z R d ⊔ X R a) := finite_of_le_stabilizer R
    ((sup_le hZ (omegaCenter_le _)).trans (fun _ hx => hx.1))
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- If the nearby Z-layer stays in the kernel two before the endpoint, source
(c) forces the forbidden normalization. This is the algebraic step in (2). -/
theorem normalizes_of_not_critical {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a a' d e : Vertex R} (ha : color R a = false)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (hda : (cosetGraph R).dist d a = 2)
    (he : (cosetGraph R).dist e a' = 2)
    (hpath : (cosetGraph R).dist a e + 2 = (cosetGraph R).dist a a')
    {W : Subgroup (FreeAmalgam R)} (hW : CommutatorWitness R a a' W)
    (hZ : Z R d ≤ Q R e) : W ≤ normalizer (Z R d ⊔ X R a : Subgroup (FreeAmalgam R)) := by
  have hC := source.edgeCentralizerCondition geometry
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
theorem escape_pair {L : Subgroup M} (source : LocalSource L R)
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
  have hC := source.edgeCentralizerCondition geometry
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
    exact normalizes_of_not_critical R source geometry hb ha hc hdist he hpath hW h
  refine ⟨f, hf, hfd, ⟨?_, hZ⟩, hfN⟩
  apply le_antisymm
  · have ht := (cosetGraph_connected R).dist_triangle (u := act R f d) (v := a) (w := e)
    rw [geometry.distance_constant _ hfd]
    have hh := hc.1.trans (geometry.distance_constant a ha)
    omega
  · exact criticalDistance_le R _ _ hZ

/-- A conjugate of the forward nonnormal product supplies the neighbor needed
in step (2), without using the later universal escape theorem. -/
theorem exists_nonnormal_neighbor {L : Subgroup M} (source : LocalSource L R)
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
  have hfwd := critical_nonnormal_forward R geometry (source.edgeCentralizerCondition geometry)
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
theorem criticalEscape {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : Generation R) (hcomm : CommutatorControl R geometry) :
    Factorization.CriticalEscape R geometry := by
  intro a ha a' hc e he hpath
  have hb' : (cosetGraph R).dist a a' = geometry.b R :=
    hc.1.trans (geometry.distance_constant a ha)
  obtain ⟨t, hat, hta'⟩ := exists_adjacent_dist_sub_one R a a' (by omega)
  obtain ⟨d, hdt, hda, hnot⟩ := exists_nonnormal_neighbor R source geometry hb a ha a' hc t hat hta'
  obtain ⟨W, hW⟩ := hcomm a ha a' hc
  have ha' := critical_endpoint_color R a ha _ hc
  have hWT : W ≤ Q R t := hW.le_X.trans
    (X_le_Q_of_dist_lt R geometry (source.edgeCentralizerCondition geometry) a' ha' t (by
      rw [geometry.distance_constant a' ha', SimpleGraph.dist_comm]
      change (cosetGraph R).dist t a' < geometry.b R
      omega))
  have hNG : ¬ ((Q R t).subgroupOf (stabilizer R a)).Normal := by
    intro hn
    apply hW.not_le_Q
    exact hWT.trans (le_Q_of_normal_edge R a t hat (Q R t)
      (le_inf (edge_le_stabilizer R ha hat) (fun _ hx => hx.1)) hn)
  obtain ⟨f, hf, hd, hpair, _⟩ := escape_pair R source geometry hb hgen a ha a' hc t hat hta'
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

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
