module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CenterDisjointness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReverseDisplacement
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The natural-start branch of DGS 8.6 and its Chapter 9 application

Actual natural-center coordinates give a surjection onto SL₂ with the
literal vertex-core kernel. Its quotient isomorphism supplies the linear
starting case of the radius-three theorem. Natural edge commutators then
identify H with the terminal center span, and central disjointness gives
8.6(b). Transporting the quotient to the middle vertex constructs an
exchange of the actual neighbors; the two disjoint conjugates of H contain
the intersection commutator, proving 8.6(c) in this natural-start branch.

The final theorem supplies the actual distance and quotient conclusions
at the reversed critical pair used by the Chapter 9 exchange proof. Thus
that natural-start specialization of 9.2 has no Chapter 8 callback. The
naturality hypothesis remains explicit: these results do not prove the
converse implications of 8.6, the general nonlinear distance-five case,
or the equal-field conclusion of 8.7.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 8.6, printed p.139, and 9.2, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

open scoped MatrixGroups

/-- Actual natural-center coordinates at the starting vertex identify the
nonzero critical commutator with the terminal center span. -/
theorem source_natural_center_commutator_eq_terminal
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup a) (Z (family P) a) (Q (family P) a)) :
    ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ = Z (family P) a' := by
  let := finite_endpoints h
  obtain ⟨hodd,_,hcentral,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  have ht : beta.type = a'.type := by
    apply (even_dist_iff (family P) h.generate beta a').mp
    obtain ⟨n,hn⟩ := hodd
    exact ⟨n,by omega⟩
  rw [commutator_comm]
  exact source_natural_span_commutator h hB d hab ht hcentral hnat _ inf_le_right
    (by rwa [commutator_comm])

/-- The natural-center representation induces an isomorphism on the literal
local quotient by its two-core, over its original finite field. -/
theorem source_natural_center_linear_quotient
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    (v : Vertex (family P))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v)) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nonempty ((d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* SL(2,k)) := by
  let := finite_endpoints h
  obtain ⟨k,hk,hfin,halg,π,hπ,hker,_⟩ := hnat
  let L := d.localGroup v
  have hcore : (Q (family P) v).subgroupOf L = pCore 2 L := by
    rw [←localGroup_core_eq (family P) d v]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  exact ⟨k,inferInstance,inferInstance,inferInstance,
    ⟨(QuotientGroup.quotientMulEquivOfEq (hker.trans hcore).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩⟩

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem isPSL_of_binary_linear_equiv {X : Type u} [Group X]
    {K : Type u} [Field K] [Finite K] [CharP K 2] (eK : X ≃* SL(2,K)) :
    ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL X 2 (2^n) := by
  let k := Shrink.{0} K
  let ek : K ≃+* k := (Shrink.ringEquiv.{0,_} K).symm
  let : CharP k 2 := (ek.toRingHom.charP_iff_charP 2).mp inferInstance
  let e := eK.trans (Atlas.fieldEquivSL 2 ek)
  let := Fintype.ofFinite k
  obtain ⟨n,_,hcard⟩ := FiniteField.card k 2
  exact ⟨n,n.property,k,inferInstance,inferInstance,
    by simpa only [Nat.card_eq_fintype_card] using hcard,
    ⟨e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩)⟩⟩

/-- The natural-start reduced F1.11 branch has b = 3, H equal to the terminal
center, and the disjoint-conjugate conclusion of 8.6(b). -/
theorem reduced_natural_start_distance_and_center
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter
      (graphLocalGroup (Reduction.reducedFamily J S₀) a)
      (Z (Reduction.reducedFamily J S₀) a) (Q (Reduction.reducedFamily J S₀) a)) :
    let F := Reduction.reducedFamily J S₀
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    b F = 3 ∧ H = Z F a' ∧
      ∃ mid : Vertex F, (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
        ∀ g : Reduction.G₀ J S₀, g ∈ stabilizer F mid → g ∉ stabilizer F a' →
          Disjoint H (H.map (MulAut.conj g).toMonoidHom) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨K,_,_,_,⟨eK⟩⟩ := source_natural_center_linear_quotient ht d a hnat
  have hstart := isPSL_of_binary_linear_equiv eK
  have hb3 := reduced_linear_start_distance_three h hob models hc hab hd hb hcomm hne (Or.inl hstart)
  have hH := source_natural_center_commutator_eq_terminal ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm hne hnat
  exact ⟨hb3,hH,source_distance_three_central_implies_disjoint ht
    (Reduction.reduced_borel_core_sylow h) d models hc hab hd hb3 hcomm hH.le⟩

/-- Source 8.6(c) in the natural-start branch: transport the actual linear
quotient, exchange the neighboring vertices, and use disjoint conjugates of H. -/
theorem reduced_natural_start_intersection_commutes
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter
      (graphLocalGroup (Reduction.reducedFamily J S₀) a)
      (Z (Reduction.reducedFamily J S₀) a) (Q (Reduction.reducedFamily J S₀) a)) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ = ⊥ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨hb3,_,mid,hbm,ham,hdis⟩ :=
    reduced_natural_start_distance_and_center h hob models hc hab hd hb hcomm hne hnat
  obtain ⟨k,_,_,_,⟨e⟩⟩ := source_natural_center_linear_quotient ht d a hnat
  have hat : a.type = mid.type := by
    have ha := hab.1
    have hm := hbm.1
    generalize a.type = x at ha ⊢
    generalize beta.type = y at ha hm
    generalize mid.type = z at hm ⊢
    cases x <;> cases y <;> cases z <;> tauto
  obtain ⟨g,hg⟩ := (same_orbit_iff F a mid).mpr hat
  have heq : d.localGroup mid = (d.localGroup a).map (MulAut.conj g).toMonoidHom := by
    rw [←hg,d.conjugate]
  let f := (MulEquiv.subgroupCongr heq).trans
    ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  let em := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  have hex := CommutingTrivial.linear_local_neighbor_exchange ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hbm.symm ham.symm em
  change ∃ t : d.localGroup mid, (t : Reduction.G₀ J S₀) • beta = a' ∧
    (t : Reduction.G₀ J S₀) • a' = beta ∧ (t : Reduction.G₀ J S₀) * t ∈ Q F mid at hex
  obtain ⟨t,htb,hta,_⟩ := hex
  have hba : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self,hb3] at hd
    omega
  have htfix : (t : Reduction.G₀ J S₀) ∈ stabilizer F mid := d.local_le mid t.property
  have htescape : (t : Reduction.G₀ J S₀) ∉ stabilizer F a' := by
    intro hfix
    exact hba (hta.symm.trans hfix)
  have hdis' := hdis t htfix htescape
  have he : H.map (MulAut.conj (t : Reduction.G₀ J S₀)).toMonoidHom =
      ⁅V F a' 1 ⊓ Q F beta,V F beta 1⁆ := by
    rw [←displacement_translate,htb,hta]
  have h₁ : ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ ≤ H :=
    commutator_mono le_rfl inf_le_left
  have h₂ : ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ ≤
      H.map (MulAut.conj (t : Reduction.G₀ J S₀)).toMonoidHom := by
    rw [he,commutator_comm (V F a' 1 ⊓ Q F beta)]
    exact commutator_mono inf_le_left le_rfl
  exact bot_unique (hdis' h₁ h₂)

/-- Apply the natural-start linear quotient to the actual reversed Chapter 9
critical pair. This discharges the Chapter 8 callback in this specialization
of 9.2 while retaining the explicit naturality, earlier-source and catalogue inputs. -/
theorem reduced_reverse_displacement_of_natural_start
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily J S₀) a' 1 ≤ Q (Reduction.reducedFamily J S₀) beta)
    (hnat : Noncommuting.HasNaturalCenter
      (graphLocalGroup (Reduction.reducedFamily J S₀) a)
      (Z (Reduction.reducedFamily J S₀) a) (Q (Reduction.reducedFamily J S₀) a)) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F a' 1 ⊓ Q F beta,V F beta 1⁆ = ⊥ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨K,_,_,_,⟨e⟩⟩ := source_natural_center_linear_quotient ht d a hnat
  apply CommutingTrivial.reduced_reverse_displacement_of_chapterEight
    h hc hab hd hb hcomm htriv he
  intro z hz hzc hzcomm hrev
  have htba : beta.type = a'.type := by
    apply (even_dist_iff F ht.generate beta a').mp
    have hodd : Odd (b F) := (source_critical_geometry ht d hc hab hd hb hcomm).1
    have hdF : (graph F).dist beta a' + 1 = b F := hd
    obtain ⟨n,hn⟩ := hodd
    exact ⟨n,by omega⟩
  have hat : a.type = z.type := by
    have ha := hab.1
    have hz' := hz.1
    rw [←htba] at hz'
    cases ha' : a.type <;> cases hz'' : z.type <;> cases hb' : beta.type <;> simp_all
  obtain ⟨g,hg⟩ := (same_orbit_iff F a z).mpr hat
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport ht g hg
  let ez : (graphLocalGroup F z ⧸ pCore 2 (graphLocalGroup F z)) ≃* SL(2,K) := f.symm.trans e
  have hd' : (graph F).dist a' beta + 1 = b F := by rwa [SimpleGraph.dist_comm]
  have hb3 := reduced_linear_start_distance_three h hob models hzc hz hd' hb hzcomm hrev
    (Or.inl (isPSL_of_binary_linear_equiv ez))
  exact ⟨K,inferInstance,inferInstance,inferInstance,hb3,⟨ez⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
