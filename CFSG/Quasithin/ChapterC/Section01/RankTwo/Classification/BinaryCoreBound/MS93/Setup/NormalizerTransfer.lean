module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer.Algebra

/-!
# MS93 local normalization and simultaneous conjugate escape

We prove both clauses (2.1)(vi--vii) on the actual free amalgam. A shared
holomorph neighbor puts Q_alpha in G_delta when their distance is two. A
shortest critical path puts Z_alpha' in its first edge kernel, using the
constant critical distance and minimality at alpha'; no reversed critical
pair or centralizer hypothesis is needed.

These containments supply the normalizers required by nilpotent saturation
inside Q_alpha, which is finite and a two-group. The nested commutator stays
in the source order [[Z_delta,Q_alpha],Z_alpha']. For (vii), the relative
conjugate-generation lemma is applied inside G_alpha to the normalizer of
X₁. Generation then forces an escaping conjugate that also fails to normalize
X₂. Normality is always expressed in the indicated local subgroup.

`Geometry` supplies only the actual critical geometry. No `CommonFacts`
instance, finite amalgam, center bound, or later reduction is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.10), p.854, and (2.1)(vi--vii), pp.855--856.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] (R : Subgroup M)

/-- A vertex at distance two shares a holomorph neighbor with a. -/
private lemma distance_two_neighbor (a δ : Vertex R)
    (hd : (cosetGraph R).dist a δ = 2) :
    ∃ t, Adjacent R a t ∧ Adjacent R δ t := by
  obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a δ
  rw [hd] at hp
  cases p with
  | nil => simp at hp
  | @cons a t δ hat p =>
    cases p with
    | nil => simp at hp
    | @cons t u δ htu p =>
      have hlen : p.length = 0 := by simp only [SimpleGraph.Walk.length_cons] at hp; omega
      have heq : u = δ := SimpleGraph.Walk.eq_of_length_eq_zero hlen
      subst u
      exact ⟨t, (cosetGraph_adj R _ _).mp hat,
        adjacent_symm R ((cosetGraph_adj R _ _).mp htu)⟩

variable [Finite M]

theorem Q_le_stabilizer_of_dist_two (a δ : Vertex R) (ha : color R a = false)
    (hd : (cosetGraph R).dist a δ = 2) : Q R a ≤ stabilizer R δ := by
  obtain ⟨t,hat,hδt⟩ := distance_two_neighbor R a δ hd
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases hc : color R t <;> simp_all
  exact (Q_le_adjacent_h R ht hat).trans
    (by rw [Q_h_eq_edge R ht hδt]; exact inf_le_left)

/-- The first vertex on a shortest critical path contains Z at the far endpoint. -/
theorem critical_first_neighbor (geometry : Geometry R) (a : Vertex R)
    (ha : color R a = false)
    (hb : 0 < criticalDistance R a (geometry.exists_critical a ha))
    {a' : Vertex R} (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ∃ t, Adjacent R a t ∧ color R t = true ∧
      (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' ∧ Z R a' ≤ Q R t := by
  obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have ha' := critical_endpoint_color R a ha _ hc
  have hdconst : criticalDistance R a' (geometry.exists_critical a' ha') =
      criticalDistance R a (geometry.exists_critical a ha) :=
    (geometry.distance_constant a' ha').trans (geometry.distance_constant a ha).symm
  cases p with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hp; have := hc.1; omega
  | @cons a t a' hat p =>
    have hat' := (cosetGraph_adj R _ _).mp hat
    have ht : color R t = true := by
      have hne := adjacent_color_ne R hat'
      cases hcol : color R t <;> simp_all
    have hdist : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
      have hle := SimpleGraph.dist_le p
      have htri := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hat] at htri
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega
    refine ⟨t, hat', ht, hdist, Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' ha') ?_⟩
    rw [hdconst, SimpleGraph.dist_comm]
    have := hc.1
    omega

theorem critical_Z_le_stabilizer (geometry : Geometry R) (a : Vertex R)
    (ha : color R a = false)
    (hb : 0 < criticalDistance R a (geometry.exists_critical a ha))
    {a' : Vertex R} (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Z R a' ≤ stabilizer R a := by
  obtain ⟨t,hat,ht,_,hZ⟩ := critical_first_neighbor R geometry a ha hb hc
  exact hZ.trans (by rw [Q_h_eq_edge R ht hat]; exact inf_le_left)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
open NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- Source 2.1(vi), on the genuine critical geometry. -/
theorem source_2_1_vi {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (a : Vertex R) (ha : color R a = false)
    (hb : 0 < criticalDistance R a (geometry.exists_critical a ha))
    {a' : Vertex R} (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (δ : Vertex R) (hd : (cosetGraph R).dist a δ = 2)
    (hδ : Z R δ ≤ Q R a)
    (hcomm : ⁅Z R δ, Z R a'⁆ ≤ ⁅⁅Z R δ, Q R a⁆, Z R a'⁆ ⊔ Z R a) :
    Z R a' ≤ normalizer (Z R δ ⊔ Z R a : Subgroup (FreeAmalgam R)) ∧
    Z R a' ≤ normalizer (⁅Z R δ, Q R a⁆ ⊔ Z R a : Subgroup (FreeAmalgam R)) := by
  have hGa := critical_Z_le_stabilizer R geometry a ha hb hc
  have hQGa : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  let : Finite (stabilizer R a) := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective (inclusion hQGa) (inclusion_injective hQGa)
  exact nilpotent_normalization (Z R δ) (Z R a') (Z R a) (Q R a)
    (Q_isPGroup R source.two_group source.core_le a ha).isNilpotent
    hδ (Z_le_Q_of_dist_lt R a _ (by simpa using hb))
    ((Q_le_stabilizer_of_dist_two R a δ ha hd).trans (Z_normalized R δ))
    (hGa.trans (Q_normalized R a)) (hGa.trans (Z_normalized R a))
    (Z_centralizes_Q R a ha) hcomm

/-- Source 2.1(vii). It holds at every adjacent edge, in particular at the
first edge of the critical path; no reversal of the critical pair is assumed. -/
theorem source_2_1_vii (a a' t : Vertex R) (ha : color R a = false)
    (hat : Adjacent R a t) (X₁ X₂ : Subgroup (FreeAmalgam R))
    (hX₁ : X₁ ≤ Q R t) (hX₂ : X₂ ≤ Q R t)
    (hN₁ : (X₁.subgroupOf (Q R t)).Normal)
    (hN₂ : (X₂.subgroupOf (Q R t)).Normal)
    (hnot₁ : ¬ (X₁.subgroupOf (stabilizer R a)).Normal)
    (hnot₂ : ¬ (X₂.subgroupOf (stabilizer R a)).Normal)
    (hgen : conjugatesIn (Z R a') (stabilizer R a) ⊔ Q R t = stabilizer R a) :
    ∃ g ∈ stabilizer R a,
      ¬ Z R a' ≤ normalizer (X₁.map (MulAut.conj g⁻¹).toMonoidHom) ∧
      ¬ Z R a' ≤ normalizer (X₂.map (MulAut.conj g⁻¹).toMonoidHom) := by
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases hcol : color R t <;> simp_all
  have hTF : Q R t ≤ stabilizer R a := by
    rw [Q_h_eq_edge R ht hat]
    exact inf_le_left
  exact simultaneous_escape (Z R a') (stabilizer R a) (Q R t) X₁ X₂
    hTF hX₁ hX₂ hN₁ hN₂ hnot₁ hnot₂ hgen
end CFSG.Quasithin.ChapterC.BinaryMS.MS93
