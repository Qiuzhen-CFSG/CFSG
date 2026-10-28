module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules

/-!
# The binary radius-derived subgroup

The supplied common facts give the literal natural-module structure used by
the proved critical-module bounds. At distance four, two M-colored generators
of the radius have commutator of order at most two. The central vertex kernel
normalizes both generators, hence fixes their commutator pointwise. Generation
then puts the whole radius-derived subgroup in the center of that kernel.
Involution generation puts it in its omega-center, which is Z.

This binary argument supplies the second conclusion of (4.6.3) before its
first conclusion. It does not prove centrality of [V,Q], the center containment
in (4.6.1), or the factorization obstruction (4.6.2).

Source: Meierfrankenfeld--Stellmacher (1993), binary pairing in (3.5), (3.9),
and (4.6.3), printed pp.869--870, 879, and 901--902.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The four existing common outputs are precisely the natural-structure input. -/
def naturalStructure (common : CommonFacts R source geometry) :
    BinaryNaturalStructure source where
  X_eq_Z := common.X_eq_Z
  natural := common.natural
  decomposition := common.decomposition
  disjoint := common.disjoint

/-- All Section 3 module fields follow from the common inputs and the proved
binary critical-module calculations; no SectionThree constructor is assumed. -/
def moduleFacts [Finite M] (common : CommonFacts R source geometry) :
    ModuleFacts source geometry where
  X_eq_Z := common.X_eq_Z
  natural := common.natural
  full_commutation := common.full_commutation
  decomposition := common.decomposition
  disjoint := common.disjoint
  critical_U_index := (naturalStructure common).critical_U_index geometry common.large_distance
  critical_Z_commutator_card :=
    (naturalStructure common).critical_Z_commutator_card geometry common.large_distance
  b_four_class_two := (naturalStructure common).b_four_class_two geometry

/-- The H-colored generators in the radius already lie in Z at its center.
It therefore suffices to check only its M-colored generators. -/
theorem radius_le_of_generators (a : Vertex R) (ha : color R a = false)
    (D : Subgroup (FreeAmalgam R))
    (hD : ∀ c, color R c = false → (cosetGraph R).dist c a ≤ 2 → Z R c ≤ D) :
    V R a ≤ D := by
  apply iSup_le
  intro c
  apply iSup_le
  intro hc
  by_cases hcol : color R c = false
  · exact hD c hcol hc
  · have hcol' : color R c = true := by cases hh : color R c <;> simp_all
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c a
    have hnEven : ¬ Even p.length := by
      rw [walk_even_iff_color_eq, hcol', ha]
      decide
    have hlen : p.length = 1 := by
      have hle : p.length ≤ 2 := hp.trans_le hc
      rw [Nat.even_iff] at hnEven
      omega
    have hadj : Adjacent R a c :=
      adjacent_symm R ((cosetGraph_adj R _ _).mp (p.adj_of_length_eq_one hlen))
    have hcZ : Z R c ≤ Z R a := by
      rw [Z, if_neg hcol, Z, if_pos ha]
      exact le_iSup_of_le c (le_iSup_of_le hadj le_rfl)
    exact hcZ.trans (hD a ha (by simp))

private theorem normalizer_le_centralizer_small {G : Type*} [Group G]
    (D : Subgroup G) [Finite D] (hD : Nat.card D ≤ 2) :
    normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  by_cases hsmall : Nat.card D ≤ 1
  · rw [eq_bot_of_card_le D hsmall]
    intro g _ x hx
    have hxone : x = 1 := hx
    simp [hxone]
  · have htwo : Nat.card D = 2 := by omega
    obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    intro g hg x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xD : D := ⟨x, hx⟩
    let yD : D := ⟨g * x * g⁻¹, (hg x).mp hx⟩
    have hyne : yD ≠ 1 := by
      intro hy
      apply hxone
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using hh
    have heq : yD = xD := (hzuniq yD hyne).trans (hzuniq xD (by
      intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have hh := congrArg (fun a : G => a * g) heq'
    simpa [mul_assoc] using hh.symm

private theorem commutator_iSup_le_of_normalizes {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer (D : Set G)) (hc : ∀ i, ⁅A i, Y⁆ ≤ D) :
    ⁅⨆ i, A i, Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)

/-- The central vertex kernel fixes every binary pair commutator in the radius. -/
theorem radius_pair_centralizes_Q [Finite M] (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (a : Vertex R) (ha : color R a = false)
    (c d : Vertex R) (hc : color R c = false) (hd : color R d = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hda : (cosetGraph R).dist d a ≤ 2) :
    ⁅Z R c, Z R d⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
  have hcd := geometry.ball_Z_le_stabilizer (by omega) a c d hc hca hda
  have hdc := geometry.ball_Z_le_stabilizer (by omega) a d c hd hda hca
  rw [(naturalStructure common).commutator_eq_of_mutual_stabilizer c hc d hd hcd hdc]
  have hcn := (U_le_Z c).trans (hcd.trans (U_normalized d))
  have hdn := (U_le_Z d).trans (hdc.trans (U_normalized c))
  let : Finite (U R c) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at c hc]; decide)
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at d hd]; decide)
  let := geometry.U_elementary (by omega) c hc
  let := geometry.U_elementary (by omega) d hd
  have hbound := card_commutator_le_two_of_elementary_eight _ _
    (common.natural.card_at c hc) (common.natural.card_at d hd) hcn hdn
  have hle : ⁅U R c, U R d⁆ ≤ U R c :=
    le_normalizer_iff_commutator_le_left.mp hdn
  let : Finite (⁅U R c, U R d⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective hle)
  apply le_centralizer_iff.mp
  apply le_trans _ (normalizer_le_centralizer_small _ hbound)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator]
  have hgc := (Q_le_stabilizer_of_dist_le_two a c ha hc
    (by rwa [SimpleGraph.dist_comm])).trans (U_normalized c)
  have hgd := (Q_le_stabilizer_of_dist_le_two a d ha hd
    (by rwa [SimpleGraph.dist_comm])).trans (U_normalized d)
  rw [mem_normalizer_iff_map_conj_eq.mp (hgc hg),
    mem_normalizer_iff_map_conj_eq.mp (hgd hg)]

/-- The binary radius-derived subgroup centralizes the entire local kernel. -/
theorem radius_derived_centralizes_Q [Finite M] (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, V R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
  let I := {c : Vertex R // color R c = false ∧ (cosetGraph R).dist c a ≤ 2}
  let A : I → Subgroup (FreeAmalgam R) := fun c => Z R c.val
  have hV : V R a = ⨆ c, A c := by
    apply le_antisymm
    · apply radius_le_of_generators a ha
      intro c hc hca
      exact le_iSup A ⟨c, hc, hca⟩
    · apply iSup_le
      intro c
      exact le_iSup_of_le c.val (le_iSup_of_le c.property.2 le_rfl)
  have hn : (⨆ c, A c) ≤ normalizer (centralizer (Q R a : Set (FreeAmalgam R))) := by
    rw [← hV]
    exact (radius_le_Q common a ha).trans
      ((le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _))
  rw [hV]
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro c
  rw [commutator_comm]
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro d
  exact radius_pair_centralizes_Q common hb a ha
    d.val c.val d.property.1 c.property.1 d.property.2 c.property.2

/-- The second assertion of (4.6.3), using the binary pairing directly.
This does not assume its first assertion about [V,Q]. -/
theorem radius_derived_le_Z [Finite M] (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, V R a⁆ ≤ Z R a := by
  have hc : ⁅V R a, V R a⁆ ≤ (center (Q R a)).map (Q R a).subtype := by
    intro x hx
    refine ⟨⟨x, radius_le_Q common a ha (commutator_le_self _ hx)⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (radius_derived_centralizes_Q common hb a ha hx y y.property)
  rw [← common.X_eq_Z a ha]
  exact DistanceEight.commutator_le_omegaCenter_of_omegaOne_eq_self
    (V R a) (V R a) (Q R a) (radius_le_Q common a ha)
    (DistanceEight.VBall_omegaOne R a 2) hc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
