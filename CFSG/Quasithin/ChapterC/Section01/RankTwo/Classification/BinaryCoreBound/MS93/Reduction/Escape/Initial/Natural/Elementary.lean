module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Source
public import Theory.ElementaryAbelian.Quotient

/-!
# Elementary abelianness of the radius quotient

For b > 2, evenness gives b ≥ 4. Each pair of M-type Z-generators in the
radius-two ball mutually normalizes. Their commutator agrees with that of
the actual natural eight-groups, so it has order at most two. The kernel Q_a
fixes every M-vertex in this ball and hence normalizes each pair commutator.
It therefore centralizes the pair commutator, which lies in X_a = Z_a.
Passing to the generated group gives [V_a,V_a] ≤ Z_a.

The Z-generators are elementary abelian. Their images generate the abelian
quotient V_a/Z_a, so this quotient also has exponent two. All quotient
normality is relative to the finite local stabilizer. Neither the contrary
escape configuration nor the order-four radius commutator is needed here.

Source: Meierfrankenfeld--Stellmacher (1993), binary natural case of (3.5)
and the radius argument (3.9), pp.869--870,879; this supplies the actual
module used in (4.3.1)(iii), pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
variable {M : Type*} [Group M] {L R : Subgroup M}

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


private theorem pair_le_Z [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 ≤ geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (c d : Vertex R) (hc : color R c = false) (hd : color R d = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hda : (cosetGraph R).dist d a ≤ 2) :
    ⁅Z R c, Z R d⁆ ≤ Z R a := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hcd := geometry.ball_Z_le_stabilizer hb a c d hc hca hda
  have hdc := geometry.ball_Z_le_stabilizer hb a d c hd hda hca
  rw [s.commutator_eq_of_mutual_stabilizer c hc d hd hcd hdc]
  have hcn := (U_le_Z c).trans (hcd.trans (U_normalized d))
  have hdn := (U_le_Z d).trans (hdc.trans (U_normalized c))
  let : Finite (U R c) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at c hc]; decide)
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at d hd]; decide)
  let := geometry.U_elementary (by omega) c hc
  let := geometry.U_elementary (by omega) d hd
  have hbound := card_commutator_le_two_of_elementary_eight _ _
    (modules.natural.card_at c hc) (modules.natural.card_at d hd) hcn hdn
  have hle : ⁅U R c, U R d⁆ ≤ U R c :=
    le_normalizer_iff_commutator_le_left.mp hdn
  let : Finite (⁅U R c, U R d⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective hle)
  have hnormal : Q R a ≤ normalizer
      ((⁅U R c, U R d⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator]
    have hgc := (Q_le_stabilizer_of_dist_le_two a c ha hc
      (by rwa [SimpleGraph.dist_comm])).trans (U_normalized c)
    have hgd := (Q_le_stabilizer_of_dist_le_two a d ha hd
      (by rwa [SimpleGraph.dist_comm])).trans (U_normalized d)
    rw [mem_normalizer_iff_map_conj_eq.mp (hgc hg),
      mem_normalizer_iff_map_conj_eq.mp (hgd hg)]
  have hcentral := le_centralizer_iff.mp
    (hnormal.trans (normalizer_le_centralizer_small _ hbound))
  rw [← modules.X_eq_Z a ha]
  intro x hx
  apply mem_omegaCenter_iff.mpr
  have hcV : U R c ≤ V R a := (U_le_Z c).trans
    (le_iSup_of_le c (le_iSup_of_le hca le_rfl))
  exact ⟨geometry.V_le_Q (by omega) a ha (hcV (hle hx)),
    elemPow_eq_one_of_isElementaryAbelian x (hle hx), hcentral hx⟩

/-- Binary pair commutators are central in Q_a, hence lie in X_a = Z_a. -/
theorem radius_derived_le_Z [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) : ⁅V R a, V R a⁆ ≤ Z R a := by
  have hfour : 4 ≤ geometry.b R := by
    have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
    obtain ⟨k, hk⟩ := heven
    omega
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
  have hn : (⨆ c, A c) ≤ normalizer (Z R a : Set (FreeAmalgam R)) := by
    rw [← hV]
    exact (geometry.V_le_Q hb a ha).trans
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))
  rw [hV]
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro c
  rw [commutator_comm]
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro d
  exact pair_le_Z source geometry hfour modules a ha d.val c.val
    d.property.1 c.property.1 d.property.2 c.property.2

private theorem elementary_quotient_of_iSup {G : Type*} [Group G]
    {ι : Sort*} (A : ι → Subgroup G) (H N : Subgroup G)
    [(N.subgroupOf H).Normal] (hH : H = ⨆ i, A i)
    (hA : ∀ i, IsElementaryAbelian 2 (A i)) (hc : ⁅H, H⁆ ≤ N) :
    IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) := by
  have hc' : _root_.commutator H ≤ N.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    rwa [map_subtype_commutator]
  let := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc'
  let q := QuotientGroup.mk' (N.subgroupOf H)
  have hAH (i) : A i ≤ H := hH.symm ▸ le_iSup A i
  have hgen : (⨆ i, (A i).subgroupOf H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    exact (iSup_congr fun i => map_subgroupOf_eq_of_le (hAH i)).trans hH.symm
  have hgenq : (⨆ i, ((A i).subgroupOf H).map q) = ⊤ := by
    rw [← Subgroup.map_iSup, hgen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  have hx : x ∈ ⨆ i, ((A i).subgroupOf H).map q := hgenq.symm ▸ mem_top x
  induction hx using iSup_induction' with
  | hp i x hx =>
    let := hA i
    let := IsElementaryAbelian.subgroupOf (p := 2) (hAH i)
    let := IsElementaryAbelian.map q (A := (A i).subgroupOf H) (p := 2)
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  | h1 => simp
  | hmul x y _ _ hx hy => rw [mul_pow, hx, hy, one_mul]

/-- The actual local quotient V_a/Z_a is elementary abelian before representation recognition. -/
theorem elementary_radius_quotient [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) : ElementaryRadiusQuotient geometry a := by
  let S := stabilizer R a
  let H := (V R a).subgroupOf S
  let N := (Z R a).subgroupOf S
  let := geometry.Z_normal a
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
  have hVS : V R a ≤ S := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hAS (c : I) : A c ≤ S := (hV.symm ▸ le_iSup A c).trans hVS
  have hH : H = ⨆ c, (A c).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_iSup, map_subgroupOf_eq_of_le hVS, hV]
    exact iSup_congr fun c => (map_subgroupOf_eq_of_le (hAS c)).symm
  apply elementary_quotient_of_iSup _ H N hH
  · intro c
    let := geometry.Z_elementary (by omega) c.val c.property.1
    exact IsElementaryAbelian.subgroupOf (hAS c)
  · apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hVS]
    exact radius_derived_le_Z source geometry hb modules a ha

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural
