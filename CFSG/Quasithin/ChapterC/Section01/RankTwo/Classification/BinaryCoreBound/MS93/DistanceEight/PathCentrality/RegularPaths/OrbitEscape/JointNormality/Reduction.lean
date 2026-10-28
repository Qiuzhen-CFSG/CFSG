module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.Spans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Inputs
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Reduction of the joint-normality argument in MS93 (4.4.2)

The relative normalizer P acts on the actual reverse span V₁; its orbit span
W is the source V₁*. Failure of reverse escape puts every local conjugate
of W in Q_(a′−4). If a chosen conjugate has displacement under Z_a′ inside V,
its join with V is normal in G_a. Conjugate generation in the genuine marked
quotient then descends that normality to V V₁.

Consequently each chosen H_i = [W^ti,Z_(a′−2)] is nontrivial unless joint
normality already holds. The H_i lie in U_(a′−2) and centralize Z_a′. If they
also lie in two separating edge conjugates, their disjointness and the
order-four bound for C_(U_a)(Z_a′) show that they generate that centralizer.
This places the critical commutator R inside U_(a′−2).

The selection of the two edge conjugates, their displacement bounds, and the
exclusion of this final critical containment remain source obligations. The
three contract definitions at the end have no asserted constructors here.
In particular, mutual normalization of V and V₁ does not prove the conclusion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), first paragraph of (4.4.2), printed p.893. All conjugations follow the
source right-conjugation convention; D in (4.4.1) means fixedCore.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
open NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The normalizer of the actual edge commutator, relative to G_a. -/
noncomputable def relativeP {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Subgroup (FreeAmalgam R) :=
  stabilizer R a ⊓ normalizer (edgeCommutator R a (p.walk.getVert 1))

/-- The source V₁* = ⟨V₁^P⟩, with the reverse local span as its seed. -/
noncomputable def reversePSpan {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Subgroup (FreeAmalgam R) :=
  conjugatesIn (localZSpan R a (p.walk.getVert 2)) (relativeP p)

/-- The subgroup H_i on printed p.893 for a specified local conjugator. -/
noncomputable def displacement {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (g : FreeAmalgam R) : Subgroup (FreeAmalgam R) :=
  ⁅rightConjugate (reversePSpan p) g, Z R (p.walk.getVert (p.walk.length - 2))⁆

private theorem conjugate_mul {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    rightConjugate (rightConjugate A g) h = rightConjugate A (g * h) := by
  rw [rightConjugate, rightConjugate, Subgroup.map_map, rightConjugate]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one {G : Type*} [Group G] (A : Subgroup G) :
    rightConjugate A 1 = A := by
  unfold rightConjugate
  have he : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [he, Subgroup.map_id]

theorem reverseSpan_le_reversePSpan {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    localZSpan R a (p.walk.getVert 2) ≤ reversePSpan p := by
  have h := le_iSup (fun g : relativeP p =>
    rightConjugate (localZSpan R a (p.walk.getVert 2)) g) 1
  simpa only [Subgroup.coe_one, conjugate_one, reversePSpan, conjugatesIn] using h

theorem reversePSpan_normalized {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    relativeP p ≤ normalizer (reversePSpan p) :=
  conjugatesIn_normalized _ _

theorem reversePSpan_le_stabilizer [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 2 < geometry.b R) :
    reversePSpan p ≤ stabilizer R a := by
  apply iSup_le
  intro g
  have hd : localZSpan R a (p.walk.getVert 2) ≤ stabilizer R a :=
    le_sup_right.trans (jointSpan_le_stabilizer p hb)
  exact (map_mono hd).trans
    (mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer R a).le_normalizer ((stabilizer R a).inv_mem g.property.1))).le

/-- Only the covariance direction needed for the failed reverse escape. -/
theorem conjugate_reverseSpan_le {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    rightConjugate (localZSpan R a (p.walk.getVert 2)) g ≤
      localZSpan R a (act R g (p.walk.getVert 2)) := by
  rw [rightConjugate, localZSpan, Subgroup.map_iSup]
  apply iSup_le
  intro h
  let k : FreeAmalgam R := g⁻¹ * h * g
  have hk : k ∈ stabilizer R (act R g (p.walk.getVert 2)) := by
    rw [stabilizer_act]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv, k] using
      mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom h.property
  have he : act R g (act R h a) = act R k (act R g a) := by
    simp only [← act_mul, k, mul_assoc, mul_inv_cancel_left]
  rw [← Z_act, he, show act R g a = a from hg]
  exact le_iSup (fun j : stabilizer R (act R g (p.walk.getVert 2)) =>
    Z R (act R j a)) ⟨k, hk⟩

theorem conjugate_reversePSpan_le_of_failed_reverse {a a' : Vertex R}
    (p : CriticalPath R geometry a a')
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    rightConjugate (reversePSpan p) g ≤ Q R (p.walk.getVert (p.walk.length - 4)) := by
  rw [reversePSpan, rightConjugate, conjugatesIn, Subgroup.map_iSup]
  apply iSup_le
  intro h
  change rightConjugate (rightConjugate (localZSpan R a (p.walk.getVert 2)) h) g ≤ _
  rw [conjugate_mul]
  have hhg : (h : FreeAmalgam R) * g ∈ stabilizer R a :=
    (stabilizer R a).mul_mem h.property.1 hg
  exact (conjugate_reverseSpan_le p hhg).trans (hreverse _ hhg)

private theorem orbit_normalization {G : Type*} [Group G]
    (F P Q V D A W : Subgroup G) (g : G)
    (hg : g ∈ F) (hPF : P ≤ F) (hAF : A ≤ F) (hVF : V ≤ F) (hWF : W ≤ F)
    (hDW : D ≤ W) (hFV : F ≤ normalizer V) (hPW : P ≤ normalizer W)
    (hQD : Q ≤ normalizer D) (hQV : Q ≤ normalizer V)
    (hgen : rightConjugate P g ⊔ A = F)
    (hgen' : conjugatesIn A F ⊔ Q = F)
    (hcomm : ⁅rightConjugate W g, A⁆ ≤ V) : F ≤ normalizer (V ⊔ D : Subgroup G) := by
  let Wg := rightConjugate W g
  let J := Wg ⊔ V
  have hgF := mem_normalizer_iff_map_conj_eq.mp (F.le_normalizer (F.inv_mem hg))
  have hWgF : Wg ≤ F := (map_mono hWF).trans hgF.le
  have hPgF : rightConjugate P g ≤ F := (map_mono hPF).trans hgF.le
  have hPgWg : rightConjugate P g ≤ normalizer Wg :=
    (map_mono hPW).trans (le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  have hJcomm : ⁅J, A⁆ ≤ V := by
    have hpre : J ≤ commutatorPreimage F A V :=
      sup_le (le_commutatorPreimage hWgF hcomm)
        (le_commutatorPreimage hVF
          (le_normalizer_iff_commutator_le_left.mp (hAF.trans hFV)))
    exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le F A V hFV)
  have hFJ : F ≤ normalizer J := by
    rw [← hgen]
    exact sup_le
      ((le_inf hPgWg (hPgF.trans hFV)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
      (le_normalizer_iff_commutator_le_left.mpr (hJcomm.trans le_sup_right))
  have hDJ : D ≤ J := by
    have hDg : rightConjugate D g ≤ J := (map_mono hDW).trans le_sup_left
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hDg
    have hJ := mem_normalizer_iff_map_conj_eq.mp (hFJ hg)
    change J.map (MulAut.conj g).toMonoidHom = J at hJ
    have hh' : rightConjugate (rightConjugate D g) g⁻¹ ≤ J := by
      simpa only [rightConjugate, inv_inv, hJ] using hh
    simpa only [conjugate_mul, mul_inv_cancel, conjugate_one] using hh'
  have hNK : conjugatesIn A F ≤ normalizer (V ⊔ D : Subgroup G) := by
    apply iSup_le
    intro t
    have hJ := mem_normalizer_iff_map_conj_eq.mp (hFJ (F.inv_mem t.property))
    have hV := mem_normalizer_iff_map_conj_eq.mp (hFV (F.inv_mem t.property))
    change J.map (MulAut.conj (t : G)⁻¹).toMonoidHom = J at hJ
    change V.map (MulAut.conj (t : G)⁻¹).toMonoidHom = V at hV
    have hc : ⁅J, rightConjugate A t⁆ ≤ V := by
      rw [← hJ, rightConjugate, ← map_commutator, ← hV]
      exact map_mono hJcomm
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono (sup_le le_sup_right hDJ) le_rfl).trans (hc.trans le_sup_left)
  rw [← hgen']
  exact sup_le hNK ((le_inf hQV hQD).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))

/-- The contained-orbit branch of the printed argument, with its displacement
bound explicit. The actual quotient supplies normal generation. -/
theorem jointSpan_normalized_of_conjugate_bound [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hgen : rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a)
    (hcomm : ⁅rightConjugate (reversePSpan p) g, Z R a'⁆ ≤
      localZSpan R (p.walk.getVert 2) a) :
    stabilizer R a ≤ normalizer (jointSpan p) := by
  have hd : (cosetGraph R).dist a (p.walk.getVert 2) = 2 :=
    p.dist_start (by have hh := p.length_eq_b; have hb := common.large_distance; omega)
  have hAF := (source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical).2
  have hnot : ¬ Z R a' ≤ Q R a :=
    (common.critical_reverse a p.start_color a' p.end_color p.critical).2
  apply orbit_normalization (stabilizer R a) (relativeP p) (Q R a)
    (localZSpan R (p.walk.getVert 2) a) (localZSpan R a (p.walk.getVert 2))
    (Z R a') (reversePSpan p) g hg inf_le_left hAF
    (le_sup_left.trans (jointSpan_le_stabilizer p common.large_distance))
    (reversePSpan_le_stabilizer p common.large_distance) (reverseSpan_le_reversePSpan p)
    (localZSpan_normalized R _ _) (reversePSpan_normalized p)
    ((Q_le_stabilizer_of_dist_two R a _ p.start_color hd).trans (localZSpan_normalized R _ _))
    ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (localZSpan_normalized R _ _))
    hgen (Escape.Initial.local_conjugate_generation source a p.start_color _ hAF hnot) hcomm

/-- At the second predecessor the common local centralizer identifies the
kernel, because the orbit span is already in the fourth predecessor kernel. -/
theorem conjugate_reversePSpan_le_of_displacement_eq_bot [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) (hH : displacement p g = ⊥) :
    rightConjugate (reversePSpan p) g ≤ Q R (p.walk.getVert (p.walk.length - 2)) := by
  have hl := p.length_eq_b
  have heven : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  have he : color R (p.walk.getVert (p.walk.length - 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hde : Adjacent R (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 3)) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := p.walk.length - 4) (by omega))
    simpa only [show p.walk.length - 4 + 1 = p.walk.length - 3 by omega] using h
  have hef : Adjacent R (p.walk.getVert (p.walk.length - 2))
      (p.walk.getVert (p.walk.length - 3)) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := p.walk.length - 3) (by omega))
    simpa only [show p.walk.length - 3 + 1 = p.walk.length - 2 by omega] using
      adjacent_symm R h
  have hf : color R (p.walk.getVert (p.walk.length - 3)) = true := by
    have hn := adjacent_color_ne R hef
    cases hc : color R (p.walk.getVert (p.walk.length - 3)) <;> simp_all
  have hQ := (conjugate_reversePSpan_le_of_failed_reverse p hreverse hg).trans
    (Q_le_adjacent_h R hf hde)
  exact (le_inf hQ (commutator_eq_bot_iff_le_centralizer.mp hH)).trans_eq
    (common.centralizer _ _ he hef)

/-- The two H_i are nontrivial if joint normality fails, once the contained
branch's commutator bound is available. -/
theorem displacement_ne_bot_of_not_normalized [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hgen : rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a)
    (hbound : rightConjugate (reversePSpan p) g ≤
        Q R (p.walk.getVert (p.walk.length - 2)) →
      ⁅rightConjugate (reversePSpan p) g, Z R a'⁆ ≤ localZSpan R (p.walk.getVert 2) a)
    (hn : ¬ stabilizer R a ≤ normalizer (jointSpan p)) : displacement p g ≠ ⊥ := by
  intro hH
  exact hn (jointSpan_normalized_of_conjugate_bound common p hg hgen
    (hbound (conjugate_reversePSpan_le_of_displacement_eq_bot common p hb hreverse hg hH)))

/-- The reverse-escape assumption places every H_i in the actual natural
subgroup at the second predecessor, before any edge-plane localization. -/
theorem displacement_le_terminal_natural [Finite M]
    (source : LocalSource L R) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    displacement p g ≤ U R (p.walk.getVert (p.walk.length - 2)) := by
  have hl := p.length_eq_b
  have heven : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  have he : color R (p.walk.getVert (p.walk.length - 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hde : Adjacent R (p.walk.getVert (p.walk.length - 4))
      (p.walk.getVert (p.walk.length - 3)) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := p.walk.length - 4) (by omega))
    simpa only [show p.walk.length - 4 + 1 = p.walk.length - 3 by omega] using h
  have hef : Adjacent R (p.walk.getVert (p.walk.length - 2))
      (p.walk.getVert (p.walk.length - 3)) := by
    have h := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (i := p.walk.length - 3) (by omega))
    simpa only [show p.walk.length - 3 + 1 = p.walk.length - 2 by omega] using
      adjacent_symm R h
  have hf : color R (p.walk.getVert (p.walk.length - 3)) = true := by
    have hn := adjacent_color_ne R hef
    cases hc : color R (p.walk.getVert (p.walk.length - 3)) <;> simp_all
  have hQ := (conjugate_reversePSpan_le_of_failed_reverse p hreverse hg).trans
    (Q_le_adjacent_h R hf hde)
  have hG : rightConjugate (reversePSpan p) g ≤
      stabilizer R (p.walk.getVert (p.walk.length - 2)) :=
    hQ.trans (fun _ hx => hx.2 _ (adjacent_symm R hef))
  rw [displacement, commutator_comm]
  exact (commutator_mono le_rfl hG).trans (Escape.Initial.Z_commutator_stabilizer source _ he).le

theorem displacement_centralizes_endpoint [Finite M]
    (source : LocalSource L R) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    displacement p g ≤ centralizer (Z R a' : Set (FreeAmalgam R)) := by
  have hl := p.length_eq_b
  have heven : Even p.walk.length := by
    rw [p.shortest, p.critical.1]
    exact geometry.even a p.start_color
  have he : color R (p.walk.getVert (p.walk.length - 2)) = false :=
    (p.vertex_color (by omega)).mpr (by rw [Nat.even_iff] at heven ⊢; omega)
  have hZ : Z R a' ≤ Q R (p.walk.getVert (p.walk.length - 2)) := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [geometry.distance_constant a' p.end_color, SimpleGraph.dist_comm, p.dist_end]
    change p.walk.length - (p.walk.length - 2) < geometry.b R
    omega
  exact (displacement_le_terminal_natural source p hb hreverse hg).trans
    ((U_le_Z R _).trans ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes _ he)).trans (centralizer_le hZ)))

/-- The source critical commutator R lies in C_(U_a)(Z_a'). -/
theorem critical_le_natural_centralizer [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    ⁅Z R a, Z R a'⁆ ≤ U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R)) := by
  obtain ⟨hstart, hend⟩ := source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical
  refine le_inf ((commutator_mono le_rfl hend).trans
    (Escape.Initial.Z_commutator_stabilizer source a p.start_color).le) ?_
  have hR : ⁅Z R a, Z R a'⁆ ≤ Z R a' :=
    le_normalizer_iff_commutator_le_right.mp (hstart.trans (Z_normalized R a'))
  have hZ : Z R a' ≤ Q R a' := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [geometry.distance_constant a' p.end_color, SimpleGraph.dist_self]
    change 0 < geometry.b R
    have hb := common.large_distance
    omega
  exact hR.trans ((commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes a' p.end_color)).trans (centralizer_le hZ))

/-- The fixed subgroup of the nontrivial critical actor is proper in the
marked eight-group. Thus its order is at most four, without selecting a
particular order for the actor or for an incident edge. -/
theorem natural_centralizer_card_le_four [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Nat.card (U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) ≤ 4 := by
  let C := U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R))
  have hcard := common.natural.card_at a p.start_color
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hne : C ≠ U R a := by
    intro h
    have hcentral : U R a ≤ centralizer (Z R a' : Set (FreeAmalgam R)) :=
      h.symm.le.trans inf_le_right
    apply common.critical_noncommutation a p.start_color a' p.critical
    rw [(naturalStructure common).critical_commutator_eq geometry a p.start_color a' p.critical]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hcentral.trans (centralizer_le (U_le_Z R a'))
  have hdiv := card_dvd_of_le (show C ≤ U R a from inf_le_left)
  rw [hcard] at hdiv
  have hsmall : Nat.card C < 8 := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge inf_le_left (by rwa [hcard]))
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  change Nat.card C ≤ 4
  omega

private theorem small_join {G : Type*} [Group G] (C H K : Subgroup G)
    [Finite C] (hC : Nat.card C ≤ 4) (hHC : H ≤ C) (hKC : K ≤ C)
    (hH : H ≠ ⊥) (hK : K ≠ ⊥) (hd : Disjoint H K) : H ⊔ K = C := by
  have hjoin : H ⊔ K ≤ C := sup_le hHC hKC
  let : Finite H := Finite.of_injective (inclusion hHC) (inclusion_injective hHC)
  let : Finite K := Finite.of_injective (inclusion hKC) (inclusion_injective hKC)
  let : Finite (H ⊔ K : Subgroup G) :=
    Finite.of_injective (inclusion hjoin) (inclusion_injective hjoin)
  let f : H × K → ↥(H ⊔ K) := fun z => ⟨z.1 * z.2, mul_mem_sup z.1.property z.2.property⟩
  have hf : Function.Injective f := fun _ _ he =>
    mul_injective_of_disjoint hd (congrArg Subtype.val he)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  have hHcard := (one_lt_card_iff_ne_bot H).mpr hH
  have hKcard := (one_lt_card_iff_ne_bot K).mpr hK
  apply eq_of_le_of_card_ge hjoin
  nlinarith

/-- Nonzero H_i in the two separating conjugates fill the actual fixed
subgroup in U_a. This is the printed equality H₁H₂ = C_(U_a)(Z_a'). -/
theorem displacements_sup_eq_natural_centralizer [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hreverse : ∀ g ∈ stabilizer R a, localZSpan R a (act R g (p.walk.getVert 2)) ≤
      Q R (p.walk.getVert (p.walk.length - 4)))
    {g h : FreeAmalgam R} (hg : g ∈ stabilizer R a) (hh : h ∈ stabilizer R a)
    (hHg : displacement p g ≠ ⊥) (hHh : displacement p h ≠ ⊥)
    (hEg : displacement p g ≤ rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g)
    (hEh : displacement p h ≤ rightConjugate (edgeCommutator R a (p.walk.getVert 1)) h)
    (hsep : (rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g ⊓
        rightConjugate (edgeCommutator R a (p.walk.getVert 1)) h) ⊓
        (U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R))) = ⊥) :
    displacement p g ⊔ displacement p h =
      U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R)) := by
  have hl := p.length_eq_b
  have hadj : Adjacent R a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  have hE : edgeCommutator R a (p.walk.getVert 1) ≤ U R a :=
    Escape.Initial.edge_le_natural source a _ p.start_color hadj
  have hEgU : rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g ≤ U R a :=
    (map_mono hE).trans (mem_normalizer_iff_map_conj_eq.mp
      (U_normalized a ((stabilizer R a).inv_mem hg))).le
  have hEhU : rightConjugate (edgeCommutator R a (p.walk.getVert 1)) h ≤ U R a :=
    (map_mono hE).trans (mem_normalizer_iff_map_conj_eq.mp
      (U_normalized a ((stabilizer R a).inv_mem hh))).le
  let C := U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R))
  have hHCg : displacement p g ≤ C :=
    le_inf (hEg.trans hEgU) (displacement_centralizes_endpoint source p hb hreverse hg)
  have hHCh : displacement p h ≤ C :=
    le_inf (hEh.trans hEhU) (displacement_centralizes_endpoint source p hb hreverse hh)
  have hdisj : Disjoint (displacement p g) (displacement p h) := by
    apply disjoint_iff_inf_le.mpr
    exact (le_inf (inf_le_inf hEg hEh) (inf_le_left.trans hHCg)).trans_eq hsep
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at a p.start_color]; decide)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ U R a from inf_le_left))
    (inclusion_injective _)
  exact small_join C _ _ (natural_centralizer_card_le_four common p) hHCg hHCh hHg hHh hdisj

/-- The two edge conjugates selected on p.893, retaining both local
generation equations and the literal threefold intersection. -/
def SeparatingConjugates {a a' : Vertex R} (p : CriticalPath R geometry a a') : Prop :=
  ∃ g ∈ stabilizer R a, ∃ h ∈ stabilizer R a,
    rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a ∧
    rightConjugate (relativeP p) h ⊔ Z R a' = stabilizer R a ∧
    (rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g ⊓
      rightConjugate (edgeCommutator R a (p.walk.getVert 1)) h) ⊓
      (U R a ⊓ centralizer (Z R a' : Set (FreeAmalgam R))) = ⊥

/-- The first application of (4.4.1) in the contained branch. This definition
records a remaining obligation, not an established consequence of the source. -/
def ContainedDisplacementBound {a a' : Vertex R} (p : CriticalPath R geometry a a') : Prop :=
  ∀ g ∈ stabilizer R a,
    rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a →
    rightConjugate (reversePSpan p) g ≤ Q R (p.walk.getVert (p.walk.length - 2)) →
    ⁅rightConjugate (reversePSpan p) g, Z R a'⁆ ≤ localZSpan R (p.walk.getVert 2) a

/-- Localization of the nontrivial H_i in the chosen edge conjugate, the
second application of (4.4.1). No proof of this contract is asserted here. -/
def EdgeDisplacementBound {a a' : Vertex R} (p : CriticalPath R geometry a a') : Prop :=
  ∀ g ∈ stabilizer R a,
    rightConjugate (relativeP p) g ⊔ Z R a' = stabilizer R a →
    displacement p g ≠ ⊥ →
    displacement p g ≤ rightConjugate (edgeCommutator R a (p.walk.getVert 1)) g

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
