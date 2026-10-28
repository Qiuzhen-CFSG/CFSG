module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Decomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The core containment in MS93 (4.5.4)(vi)

Use the proved Q_a decomposition with its triple-intersection factor.
The critical endpoint Z_(a+8) is contained in hat W_(a+4), whose commutator
with Q_(a+4) lies in Z_(a+4) by (4.5.3). Thus Z_(a+8) centralizes Q_a
modulo hat V_a^(6). Critical reversal makes its image outside Q_a nontrivial.
Normal generation in the actual SL3(2) quotient then puts the local
two-residual in that centralizer, proving [Q_a,Ltilde_a] ≤ hat V_a^(6).

All normality is relative to G_a. The five explicit inputs are preceding
(4.5.1)(iv) and (4.5.3) conclusions, with producer
qt-c01-ms93-core-factors-early-layers. Neither orbit abelianness nor any
marked quotient or later commutator equality is used. Their discharge in
the source theorem remains with the higher-layer assembly owner.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.896--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

private theorem seed_le_span {G : Type*} [Group G] (A P : Subgroup G) :
    A ≤ conjugatesIn A P := by
  intro x hx
  apply (le_iSup (fun g : P => rightConjugate A g) 1)
  exact ⟨x, hx, by simp⟩

private theorem span_le {G : Type*} [Group G] {A P N : Subgroup G}
    (hA : A ≤ N) (hN : P ≤ normalizer N) : conjugatesIn A P ≤ N := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hN (P.inv_mem g.property))).le

private theorem residual_le_of_normalized (source : LocalSource L R)
    {a : Vertex R} (ha : color R a = false) {A N : Subgroup (FreeAmalgam R)}
    (hN : N ≤ stabilizer R a) (hn : stabilizer R a ≤ normalizer N)
    (hA : A ≤ N) (hout : ¬ A ≤ Q R a) : Ltilde R a ≤ N := by
  let P := stabilizer R a
  let N₀ := N.subgroupOf P
  let Q₀ := (Q R a).subgroupOf P
  have hQP : Q R a ≤ P := fun _ hx => hx.1
  let : N₀.Normal := normal_subgroupOf_of_le_normalizer hn
  have hgen : N ⊔ Q R a = P := by
    apply le_antisymm (sup_le hN hQP)
    rw [← Escape.Initial.local_conjugate_generation source a ha A (hA.trans hN) hout]
    exact sup_le_sup (span_le hA hn) le_rfl
  have hgen₀ : N₀ ⊔ Q₀ = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hN, map_subgroupOf_eq_of_le hQP,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hgen
  let : Finite P := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective (inclusion hQP) (inclusion_injective _)
  have hQ : IsPGroup 2 (Q R a) := by
    rw [IsPGroup.iff_card, source.Q_card a ha]
    exact pCore_isPGroup.exists_card_eq
  have hr : pResidual 2 P ≤ N₀ :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N₀ Q₀ hQ.comap_subtype hgen₀⟩
  have h := map_mono (f := P.subtype) hr
  rwa [map_subgroupOf_eq_of_le hN] at h

private theorem core_le_of_Q_product (source : LocalSource L R)
    {a : Vertex R} (ha : color R a = false) {S K A : Subgroup (FreeAmalgam R)}
    (hS : S ≤ Q R a) (hn : stabilizer R a ≤ normalizer S)
    (hK : K ≤ Q R a)
    (hprod : (Q R a : Set (FreeAmalgam R)) = (S : Set (FreeAmalgam R)) * (K : Set (FreeAmalgam R)))
    (hA : A ≤ stabilizer R a) (hout : ¬ A ≤ Q R a)
    (hcomm : ⁅K, A⁆ ≤ S) : core R a ≤ S := by
  let P := stabilizer R a
  have hQP : Q R a ≤ P := fun _ hx => hx.1
  let C := commutatorPreimage P A S
  have hSC : S ≤ C := le_commutatorPreimage (hS.trans hQP)
    (le_normalizer_iff_commutator_le_left.mp (hA.trans hn))
  have hKC : K ≤ C := le_commutatorPreimage (hK.trans hQP) hcomm
  have hQC : Q R a ≤ C := by
    intro x hx
    have hx' : x ∈ (Q R a : Set (FreeAmalgam R)) := hx
    rw [hprod] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    exact C.mul_mem (hSC hs) (hKC hk)
  have hQA : ⁅Q R a, A⁆ ≤ S :=
    (commutator_mono hQC le_rfl).trans (commutator_commutatorPreimage_le P A S hn)
  let N := commutatorPreimage P (Q R a) S
  have hAN : A ≤ N := le_commutatorPreimage hA (by rwa [commutator_comm])
  have hPN : P ≤ normalizer N :=
    commutatorPreimage_normalized P (Q R a) S P hn P.le_normalizer (Q_normalized R a) hn
  have hLN : Ltilde R a ≤ N := residual_le_of_normalized source ha
    (commutatorPreimage_le _ _ _) hPN hAN hout
  change ⁅Q R a, Ltilde R a⁆ ≤ S
  rw [commutator_comm]
  exact (commutator_mono hLN le_rfl).trans (commutator_commutatorPreimage_le P (Q R a) S hn)

/-- MS93 (4.5.4)(vi), including its local Q decomposition. Its five extra
premises are literal preceding (4.5.1)(iv) and (4.5.3) conclusions.
There is no premise from (4.5.4)(ii)--(v) or from (4.5.5). -/
theorem SourcePath.core_le_hatSix (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a)
    (hVa : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a)
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R a (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hcomm : ⁅hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8)) :
    core R a ≤ hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) := by
  have hcol {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) : color R (p.walk.getVert i) = false :=
    (RegularPaths.walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi14)).mpr hi
  have ha : color R a = false := by simpa only [p.center_eq] using hcol (i := 4) (by decide) (by decide)
  have hf : color R (p.walk.getVert 12) = false := hcol (by decide) (by decide)
  have hcrit : CriticalPair R a (p.walk.getVert 12) (geometry.exists_critical a ha) := by
    have hp := p.critical 4 (by decide) (by decide)
    simp only [p.center_eq] at hp
    exact ⟨hp.1.trans (earlier.distance.symm.trans (geometry.distance_constant a ha).symm), hp.2⟩
  have hZfW : Z R (p.walk.getVert 12) ≤
      hatW R (p.walk.getVert 8) (p.walk.getVert 10) (p.walk.getVert 12) :=
    (Z_le_localZSpan R _ _).trans (seed_le_span _ _)
  have hZdS : Z R (p.walk.getVert 8) ≤
      hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) :=
    (Early.Z_le_hatV (hcol (i := 8) (by decide) (by decide))
      (p.dist (i := 8) (j := 10) (by decide) (by decide))).trans
        ((seed_le_span _ _).trans (hatW_seed_le_hatSix _ _ _ _))
  apply core_le_of_Q_product source ha (p.hatSix_le_Q earlier) (hatSix_normalized R _ _ _ _)
    (inf_le_left.trans inf_le_left) (SourcePath.Q_product p earlier hVa hVd hleft hright)
    (source.critical_Z_le_stabilizer geometry a ha _ hcrit).2
    (common.critical_reverse a ha _ hf hcrit).2
  rw [commutator_comm]
  exact (commutator_mono hZfW inf_le_right).trans (hcomm.trans hZdS)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
