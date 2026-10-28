module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.NormalizerContainment
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.J4Fusion.PairFixedPoint
/-!
# The second AS91 fixed-coset argument

After pair-plane containment, an escaping conjugate of E meets E in <t>.
The rank-five quotient C_M(t)/E bounds its elementary subgroups by 64.
A returning actor fixing a native coordinate would instead centralize 128
radical elements. Thus the Todd image of any conjugate radical in C_M(t)
has trivial point stabilizer on the marked pair and has order at most two.
Its kernel has order at most two, improving the bound to four. Applying
this to a conjugated radical centralizer contradicts either possible
fixed-space order, 64 or 128. Every element of E outside <t> therefore
fixes exactly the base coset of I∩M in I=C_G(t).

All maps use the original Todd projection; the argument distinguishes
quotient actors from the two classes of radical vectors.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.3), p.602.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

theorem secondCentralizer_conjugate_subgroup_card_le (a : LocalData h)
    (hi : MarkerIntersection a) (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (D : Subgroup G) (hDN : D ≤ secondCentralizer a)
    (hDE : D ≤ a.P.E.map (MulAut.conj g).toMonoidHom) : Nat.card D ≤ 64 := by
  let := a.P.E_elementary
  let : IsElementaryAbelian 2 (a.P.E.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (inclusion hDE) (inclusion_injective hDE)
  let f := (secondCentralizerProjection a).comp (inclusion hDN)
  have hker : Nat.card f.ker ≤ 2 := by
    let j : f.ker → (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) := fun x =>
      ⟨x.val.val,by
        have hx : (⟨x.val.val,hDN x.val.property⟩ : secondCentralizer a) ∈
            (secondCentralizerProjection a).ker := x.property
        rw [secondCentralizerProjection_ker] at hx
        exact ⟨hx,hDE x.val.property⟩⟩
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) => (x : G)) he
    exact (Nat.card_le_card_of_injective j hj).trans
      (centralizer_intersection_card_le_two a hi g hgc hgm)
  let H := cocodeVectorStabilizer cocodeRepresentation (pairVector ⟨{0,1},by decide⟩)
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : primeRank 2 H ≤ 5 := by
    rw [←primeRank_equiv 2 (secondCentralizerQuotientEquiv a)]
    exact secondCentralizer_quotient_rank_le a
  have him := (primeRank_le_iff_elementary_card_le H).mp hr f.range inferInstance
  have hc : Nat.card D = Nat.card f.ker * Nat.card f.range := by
    rw [←f.ker.card_mul_index,index_ker]
  rw [hc]
  exact (Nat.mul_le_mul hker him).trans (by decide)



/-- The conjugate fixed subgroup lies in the original second centralizer.
The normalizer barrier is applied to the actual span of t and v. -/
theorem second_returning_centralizer_le (a : LocalData h) (hi : MarkerIntersection a)
    (g v : G) (hgc : g ∈ centralizer (second a)) (hvE : v ∈ a.P.E)
    (hvU : v ∉ zpowers (second a)) :
    (a.P.E ⊓ centralizer (g*v*g⁻¹)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      secondCentralizer a := by
  let := a.P.E_elementary
  let V := zpowers (second a) ⊔ zpowers v
  have hVE : V ≤ a.P.E := sup_le (zpowers_le.mpr (second_mem a)) (zpowers_le.mpr hvE)
  have hUV : zpowers (second a) < V := lt_of_le_of_ne le_sup_left (by
    intro he
    have hvV : v ∈ V := (le_sup_right : zpowers v ≤ V) (mem_zpowers v)
    exact hvU (he.symm ▸ hvV))
  have hVc : 2 < Nat.card V := by
    by_contra hn
    have hc : Nat.card (zpowers (second a)) = 2 := by rw [Nat.card_zpowers,second_order]
    exact hUV.ne (eq_of_le_of_card_ge hUV.le (by omega))
  have hbar := second_strict_overgroup_normalizer_le a hi V hVE hVc
  rintro x ⟨c,hc,rfl⟩
  have hcI : c ∈ centralizer (second a) :=
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm (⟨c,hc.1⟩ : a.P.E) ⟨second a,second_mem a⟩))
  have hxI : MulAut.conj g⁻¹ c ∈ centralizer (second a) := by
    change g⁻¹*c*g⁻¹⁻¹ ∈ centralizer (second a)
    rw [inv_inv]
    exact (centralizer (second a)).mul_mem
      ((centralizer (second a)).mul_mem ((centralizer (second a)).inv_mem hgc) hcI) hgc
  have hxv : MulAut.conj g⁻¹ c ∈ centralizer v := by
    have hcomm : Commute c (g*v*g⁻¹) := mem_centralizer_singleton_iff.mp hc.2
    have hh := hcomm.map (MulAut.conj g⁻¹)
    have he : MulAut.conj g⁻¹ (g*v*g⁻¹) = v := by simp [mul_assoc]
    rw [he] at hh
    exact mem_centralizer_singleton_iff.mpr hh.eq
  have hxV : MulAut.conj g⁻¹ c ∈ Subgroup.centralizer (V : Set G) := by
    have hle : V ≤ Subgroup.centralizer ({MulAut.conj g⁻¹ c} : Set G) := by
      apply sup_le <;> apply zpowers_le.mpr
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxI).symm
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxv).symm
    intro u hu
    exact mem_centralizer_singleton_iff.mp (hle hu)
  exact ⟨hxI,hbar ⟨Subgroup.centralizer_le_normalizer _ hxV,hxI⟩⟩

/-- The second rank comparison: an escaping transporter bounds each returned
radical fixed subgroup by 2*32. -/
theorem second_returning_centralizer_card_le (a : LocalData h) (hi : MarkerIntersection a)
    (g v : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (hvE : v ∈ a.P.E) (hvU : v ∉ zpowers (second a)) :
    Nat.card (a.P.E ⊓ centralizer (g*v*g⁻¹) : Subgroup G) ≤ 64 := by
  have hd := secondCentralizer_conjugate_subgroup_card_le a hi g⁻¹
    ((centralizer (second a)).inv_mem hgc) (fun he => hgm (a.P.M.inv_mem_iff.mp he))
    _ (second_returning_centralizer_le a hi g v hgc hvE hvU)
    (map_mono inf_le_left)
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hd

/-- A returned actor with a fixed native coordinate has 128 radical fixed
points, contradicting the second rank bound. -/
theorem second_returning_actor_fixedPoint_false (a : LocalData h) (hi : MarkerIntersection a)
    (g v : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (hvE : v ∈ a.P.E) (hvU : v ∉ zpowers (second a))
    (hwM : g*v*g⁻¹ ∈ a.P.M)
    (ho : orderOf (a.P.projection ⟨g*v*g⁻¹,hwM⟩) = 2)
    (hf : ∃ i : Fin 24, a.P.projection ⟨g*v*g⁻¹,hwM⟩ • i = i) : False := by
  have hb := second_returning_centralizer_card_le a hi g v hgc hgm hvE hvU
  rw [todd_centralizer_card a.P ⟨g*v*g⁻¹,hwM⟩] at hb
  have hz := CocodeOctad.Involutions.isConj_z_of_fixedPoint _ ho hf
  have hd := fixedCodim_add_finrank cocodeRepresentation
    (zpowers (a.P.projection ⟨g*v*g⁻¹,hwM⟩))
  rw [finrank_cocode,CocodeOctad.Involutions.fixedCodim_of_isConj_z _ hz] at hd
  have he : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation
      (zpowers (a.P.projection ⟨g*v*g⁻¹,hwM⟩))) = 7 := by omega
  rw [he] at hb
  norm_num at hb


/-- A conjugate radical's image in the original pair stabilizer has no
nonidentity point-fixing element; hence its order is at most two. -/
theorem secondCentralizer_conjugate_subgroup_card_le_four (a : LocalData h)
    (hi : MarkerIntersection a) (g : G) (hgc : g ∈ centralizer (second a)) (hgm : g ∉ a.P.M)
    (D : Subgroup G) (hDN : D ≤ secondCentralizer a)
    (hDE : D ≤ a.P.E.map (MulAut.conj g).toMonoidHom) : Nat.card D ≤ 4 := by
  let := a.P.E_elementary
  let : IsElementaryAbelian 2 (a.P.E.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (inclusion hDE) (inclusion_injective hDE)
  let f := a.P.projection.comp (inclusion (hDN.trans inf_le_right))
  have hker : Nat.card f.ker ≤ 2 := by
    let j : f.ker → (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) := fun x =>
      ⟨x.val.val,by
        have hx : (⟨x.val.val,(hDN x.val.property).2⟩ : a.P.M) ∈ a.P.projection.ker := x.property
        rw [a.P.projection_ker] at hx
        exact ⟨hx,hDE x.val.property⟩⟩
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) => (x : G)) he
    exact (Nat.card_le_card_of_injective j hj).trans
      (centralizer_intersection_card_le_two a hi g hgc hgm)
  have him : Nat.card f.range ≤ 2 := by
    apply MathieuCode.J4Fusion.pair_stabilizer_card_le_two ⟨{0,1},by decide⟩ 0 (by simp)
    · rintro s ⟨d,rfl⟩
      exact (second_centralizer_iff a ⟨d.val,(hDN d.property).2⟩).mp (hDN d.property).1
    · rintro s ⟨d,rfl⟩ hfix
      by_contra hne
      have ho : orderOf (f d) = 2 := by
        apply orderOf_eq_prime
        · rw [←map_pow]
          have hd2 : d^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 D) d
          rw [hd2,map_one]
        · exact hne
      obtain ⟨v,hv,he⟩ := hDE d.property
      change MulAut.conj g v = d.val at he
      have hwM : g*v*g⁻¹ ∈ a.P.M := by
        change MulAut.conj g v ∈ a.P.M
        rw [he]
        exact (hDN d.property).2
      have hvU : v ∉ zpowers (second a) := by
        intro hvU
        obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp hvU
        have htfix : MulAut.conj g (second a) = second a :=
          mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgc)
        have hdE : d.val ∈ a.P.E := by
          rw [←he,map_zpow,htfix]
          exact a.P.E.zpow_mem (second_mem a) k
        apply hne
        change (⟨d.val,(hDN d.property).2⟩ : a.P.M) ∈ a.P.projection.ker
        rw [a.P.projection_ker]
        exact hdE
      have hq : a.P.projection ⟨g*v*g⁻¹,hwM⟩ = f d := by
        apply congrArg a.P.projection
        exact Subtype.ext he
      exact second_returning_actor_fixedPoint_false a hi g v hgc hgm hv hvU hwM
        (by rwa [hq]) ⟨0,by rwa [hq]⟩
  have hc : Nat.card D = Nat.card f.ker * Nat.card f.range := by
    rw [←f.ker.card_mul_index,index_ker]
  rw [hc]
  exact (Nat.mul_le_mul hker him).trans (by decide)


/-- The returning-element form of the second standard fixed-coset argument. -/
theorem second_transporter_mem (a : LocalData h) (hi : MarkerIntersection a)
    (g v : G) (hgc : g ∈ centralizer (second a)) (hvE : v ∈ a.P.E)
    (hvU : v ∉ zpowers (second a)) (hwM : g*v*g⁻¹ ∈ a.P.M) : g ∈ a.P.M := by
  let := a.P.E_elementary
  by_contra hgm
  have hwE : g*v*g⁻¹ ∉ a.P.E := by
    intro hwE
    have hwLine : g*v*g⁻¹ ∈ zpowers (second a) := by
      rw [←centralizer_intersection_eq_second_line a hi g hgc hgm]
      exact ⟨hwE,v,hvE,rfl⟩
    have hvl : MulAut.conj g⁻¹ (g*v*g⁻¹) ∈ zpowers (second a) := by
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp hwLine
      rw [←hk,map_zpow,show MulAut.conj g⁻¹ (second a) = second a from
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp
          ((centralizer (second a)).inv_mem hgc))]
      exact zpow_mem_zpowers _ _
    exact hvU (by simpa [mul_assoc] using hvl)
  have ho : orderOf (a.P.projection ⟨g*v*g⁻¹,hwM⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [←map_pow]
      have hm2 : (⟨g*v*g⁻¹,hwM⟩ : a.P.M)^2=1 := by
        apply Subtype.ext
        change (MulAut.conj g v)^2=1
        rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian v hvE,map_one]
      rw [hm2,map_one]
    · intro he
      have hk : (⟨g*v*g⁻¹,hwM⟩ : a.P.M) ∈ a.P.projection.ker := he
      rw [a.P.projection_ker] at hk
      exact hwE hk
  have hb := secondCentralizer_conjugate_subgroup_card_le_four a hi g⁻¹
    ((centralizer (second a)).inv_mem hgc) (fun he => hgm (a.P.M.inv_mem_iff.mp he))
    _ (second_returning_centralizer_le a hi g v hgc hvE hvU) (map_mono inf_le_left)
  rw [card_map_of_injective (MulAut.conj g⁻¹).injective] at hb
  have hc := todd_involution_centralizer_card a ⟨g*v*g⁻¹,hwM⟩ ho
  change Nat.card (a.P.E ⊓ centralizer (g*v*g⁻¹) : Subgroup G) = 128 ∨
    Nat.card (a.P.E ⊓ centralizer (g*v*g⁻¹) : Subgroup G) = 64 at hc
  rcases hc with hc | hc <;> omega

/-- Every surviving element of E/<t> fixes exactly the base coset of I∩M
in the full original centralizer I=C_G(t). -/
theorem second_unique_fixed_coset (a : LocalData h) (hi : MarkerIntersection a)
    (v : centralizer (second a)) (hvE : (v : G) ∈ a.P.E)
    (hvU : (v : G) ∉ zpowers (second a)) :
    ∃! q : centralizer (second a) ⧸ a.P.M.subgroupOf (centralizer (second a)), v • q = q := by
  apply UniqueFixedCoset.unique_of_transporter (G := centralizer (second a))
    (M := a.P.M.subgroupOf (centralizer (second a))) (a.P.E_le hvE)
  intro g hg
  exact second_transporter_mem a hi g.val v.val g.property hvE hvU hg

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
