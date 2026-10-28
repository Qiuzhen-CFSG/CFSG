module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure
public import Theory.GroupTheory.ElementaryEightPairing

/-!
# Binary critical-pair formulas and the radius-two class bound

The actual marked natural action and its transported kernels reduce the
critical-pair indices to the centralizer indices of mutually normalizing
elementary abelian subgroups of order eight. Their commutator pairing gives
index reciprocity and the order-two commutator conclusion.

At critical distance four, the M-vertex generators of the radius-two group
mutually lie in the local stabilizers. Their pair commutators have order at
most two and are normalized by every generator, hence centralized. The
H-vertex generators already lie in Z at the center vertex. Passing to the
generated subgroup proves that the derived subgroup of V is central.

These prove the three critical-module fields of ModuleFacts conditionally
on BinaryNaturalStructure. Constructing that natural structure, and the
unconditional ModuleFacts assembly, remain with the parent reduction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), binary natural-module cases of (3.5) and (3.9), printed pp.869--870
and 879. The last group is the radius-two V, not the global commutator core.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The binary natural-module case of MS93 (3.5)(i): the two critical
images have equal order. The action kernels identify these relative indices
with the centralizer indices in the elementary-eight pairing. -/
theorem BinaryNaturalStructure.critical_U_index [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    (Q R a').relIndex (U R a) = (Q R a).relIndex (U R a') := by
  have ha' := critical_endpoint_color R a ha _ hc
  have hr := source.critical_reverse geometry a ha a' ha' hc
  rw [structureData.critical_U_index_centralizer geometry a ha a' hc,
    structureData.critical_U_index_centralizer geometry a' ha' a hr]
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [structureData.natural.card_at a ha]; decide)
  let : Finite (U R a') := Nat.finite_of_card_ne_zero (by rw [structureData.natural.card_at a' ha']; decide)
  let := geometry.U_elementary (by omega) a ha
  let := geometry.U_elementary (by omega) a' ha'
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry a ha a' hc
  exact centralizer_relIndex_eq_of_elementary_eight _ _
    (structureData.natural.card_at a ha) (structureData.natural.card_at a' ha') hn hn'

/-- The binary natural-module case of MS93 (3.5)(ii). In this specialization,
the elementary-eight bound and critical noncommutation already force order two,
even without the image-order premise retained in the ModuleFacts interface. -/
theorem BinaryNaturalStructure.critical_Z_commutator_card [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (_hi : (Q R a').relIndex (Z R a) = 4) :
    Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  have ha' := critical_endpoint_color R a ha _ hc
  rw [structureData.critical_commutator_eq geometry a ha a' hc]
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [structureData.natural.card_at a ha]; decide)
  let : Finite (U R a') := Nat.finite_of_card_ne_zero (by rw [structureData.natural.card_at a' ha']; decide)
  let := geometry.U_elementary (by omega) a ha
  let := geometry.U_elementary (by omega) a' ha'
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry a ha a' hc
  exact card_commutator_eq_two_of_elementary_eight _ _
    (structureData.natural.card_at a ha) (structureData.natural.card_at a' ha') hn hn'
    (structureData.critical_U_noncommutation geometry a ha a' hc)

private theorem V_le_of_m_ball (a : Vertex R) (ha : color R a = false)
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

private theorem ball_pair_centralized [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (hb : 4 ≤ geometry.b R)
    (a : Vertex R) (ha : color R a = false)
    (c d : Vertex R) (hc : color R c = false) (hd : color R d = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hda : (cosetGraph R).dist d a ≤ 2) :
    ⁅Z R c, Z R d⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  have hcd := geometry.ball_Z_le_stabilizer hb a c d hc hca hda
  have hdc := geometry.ball_Z_le_stabilizer hb a d c hd hda hca
  rw [structureData.commutator_eq_of_mutual_stabilizer c hc d hd hcd hdc]
  have hcn := (U_le_Z c).trans (hcd.trans (U_normalized d))
  have hdn := (U_le_Z d).trans (hdc.trans (U_normalized c))
  let : Finite (U R c) := Nat.finite_of_card_ne_zero (by rw [structureData.natural.card_at c hc]; decide)
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [structureData.natural.card_at d hd]; decide)
  let := geometry.U_elementary (by omega) c hc
  let := geometry.U_elementary (by omega) d hd
  have hbound := card_commutator_le_two_of_elementary_eight _ _
    (structureData.natural.card_at c hc) (structureData.natural.card_at d hd) hcn hdn
  have hle : ⁅U R c, U R d⁆ ≤ U R c :=
    le_normalizer_iff_commutator_le_left.mp hdn
  let : Finite (⁅U R c, U R d⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective hle)
  apply le_centralizer_iff.mp
  apply V_le_of_m_ball a ha
  intro t ht hta
  apply le_trans _ (normalizer_le_centralizer_small _ hbound)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator]
  have hgc := (geometry.ball_Z_le_stabilizer hb a t c ht hta hca).trans (U_normalized c)
  have hgd := (geometry.ball_Z_le_stabilizer hb a t d ht hta hda).trans (U_normalized d)
  rw [mem_normalizer_iff_map_conj_eq.mp (hgc hg),
    mem_normalizer_iff_map_conj_eq.mp (hgd hg)]

/-- The binary natural-module case of MS93 (3.9): the derived subgroup of
the radius-two group V is central when the critical distance is four. -/
theorem BinaryNaturalStructure.b_four_class_two [Finite M]
    {source : LocalSource L R} (structureData : BinaryNaturalStructure source)
    (geometry : Geometry R) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) :
    ⁅⁅V R a, V R a⁆, V R a⁆ = ⊥ := by
  let I := {c : Vertex R // color R c = false ∧ (cosetGraph R).dist c a ≤ 2}
  let A : I → Subgroup (FreeAmalgam R) := fun c => Z R c.val
  have hV : V R a = ⨆ c, A c := by
    apply le_antisymm
    · apply V_le_of_m_ball a ha
      intro c hc hca
      exact le_iSup A ⟨c, hc, hca⟩
    · apply iSup_le
      intro c
      exact le_iSup_of_le c.val (le_iSup_of_le c.property.2 le_rfl)
  have hn : (⨆ c, A c) ≤ normalizer (centralizer (V R a : Set (FreeAmalgam R))) := by
    rw [← hV]
    exact (le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [hV]
  apply commutator_iSup_le_of_normalizes
  · simpa only [hV] using hn
  intro c
  rw [commutator_comm]
  apply commutator_iSup_le_of_normalizes
  · simpa only [hV] using hn
  intro d
  rw [← hV]
  exact ball_pair_centralized structureData geometry (by omega) a ha
    d.val c.val d.property.1 c.property.1 d.property.2 c.property.2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
